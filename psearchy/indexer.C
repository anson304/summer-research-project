/*
 * parallel version of Pedsort
 */

#define LINUX
#define DEBUG
//#define DRAM_CACHE
//#define N2F_CMAP_PM // docID to file
//#define W2B_CMAP_PM
#define TIMER
//#define SST
//#define FLUSH

#include <libpmemkv.h>
#include <libpmem.h>
#include <cassert>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>
#include <signal.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <errno.h>
#include <db.h>
#include <pthread.h>
#include <sched.h>
#ifdef LINUX
#include <wait.h>
#include <linux/unistd.h>
#include <linux/mman.h>
#endif
#include "args.h"
#include "mkdb.h"

#include <set>
#include <vector>

#define ASSERT(expr)                                                                     \
        do {                                                                             \
                if (!(expr))                                                             \
                        puts(pmemkv_errormsg());                                         \
                assert(expr);                                                            \
        } while (0)

#define LOG(msg) puts(msg)

const char *tmpdir;
const char *pmemdir;
const char *config = "mkdb.config";
unsigned maxwordlen;
const long long GB = 1024UL*1024UL*1024UL;
int ncore = 1;
long long D2F_DB_SIZE = 0;
long long W2B_DB_SIZE = 0;
long long BLOCKS_SIZE = 0;
long long BUCKETS_SIZE = 0;

DID did = 1;
DID max_did = 1;
int first = 1;
int order = 0;
int threaded = 1;
int dblim = 0;

pmemkv_db *w2b_db = NULL;
pmemkv_db *n2f_db = NULL;
pmemkv_db *sst_db = NULL;

#define NFILES 10000000
#define MAXFILENAME 200
#define MaxFDS 800

char files[NFILES][MAXFILENAME];

#define BLOCKSIZE 128
#define MAXWORDLEN 64
#define MAX_VAL_LEN 16

struct Block {
  int next; // next block
  int n; //number of postings
  PostIt p[BLOCKSIZE];
};

struct Bucket {
    char word[MAXWORDLEN];
  int b0; // first block
  int bN; // last block
  unsigned n; //number of postings
  int used;
};

struct timer {
	const char *name;
	double start;
	double agg;
};

inline static uint64_t rdtsc()
{
    unsigned long a, d;
    asm volatile ("rdtsc" : "=a" (a), "=d" (d));
    return a | ((uint64_t)d << 32);
}

inline static double getTimeInSecs()
{
	struct timeval tv;
	gettimeofday(&tv, (struct timezone *) 0);
	return tv.tv_sec + (tv.tv_usec / 1000000.0);
}

static void initialize_timer(struct timer *t, int cid, const char *s) {
	t[cid].name = s;
	t[cid].start = 0.0;
	t[cid].agg = 0.0;
}

static void start_timer(struct timer *t, int cid) {
	//printf("starting timer %s for core %d \n",t->name,cid);
	t[cid].start = getTimeInSecs();
}

static void end_timer(struct timer *t, int cid) {
	//printf("ending timer %s for core %d \n",t->name,cid);
	t[cid].agg += (getTimeInSecs() - t[cid].start);
	//printf("agg for %s and cid %d is %.2f \n",t->name,cid,t[cid].agg);
	t[cid].start = 0.0;
}

static void print_uni_timer(struct timer *t) {
	printf("%s took %.2f secs\n", t->name, t->agg);
}

static void print_timer(struct timer *t, int cid) {
	printf("%.2f ", t[cid].agg);
}

struct timer timer_main;
struct timer timer_n2f;
struct timer *timer_pass0;
struct timer *timer_alloc_table;
struct timer *timer_sst;
struct timer *timer_flush;

struct pass0_state {
    char *wordbytes;
    PostIt *infobuf;
    struct Bucket *buckets;
    struct Block *blocks;
    struct pass0_state_info *psinfo;
    long long wordi;
    long long infoi;
};

struct pass0_state_info {
    long long blocki;
    long long bucketi;
    long long maxinfo;
    long long maxword;
    long long maxbuckets;
    long long maxblocks;
    long long doci;

};

bool update_only;
void *dofiles();
int pass0(int cid, FILE *input, DID did, int *pass0files,  struct pass0_state *ps);
float printrusage(int init);
void query_term(char *term, struct pass0_state *ps);

static struct sharedmem {
  volatile int run;
  volatile int first;
  volatile int did;
  volatile uint64_t tot;
} *shared;

struct cpuinfo
{
  int proc, phys;
};

static void
initshared(void)
{
  if (threaded) {
    shared = (struct sharedmem *) malloc(sizeof(struct sharedmem));
    assert(shared);
  } else {
    shared = (struct sharedmem *) mmap(0, sizeof(struct sharedmem), PROT_READ|PROT_WRITE,
                                       MAP_SHARED|MAP_ANONYMOUS, 0, 0);
    if (shared == MAP_FAILED) {

      perror("mmap failed");
      exit(-1);
    }
  }
  shared->did = 1;
  shared->first = 1;
}

static int init_kv(char *engine, char *path, size_t db_size, pmemkv_db **kv) {
    pmemkv_config *cfg = pmemkv_config_new();
    ASSERT(cfg != NULL);

    int s = pmemkv_config_put_path(cfg, path);
    ASSERT(s == PMEMKV_STATUS_OK);
    s = pmemkv_config_put_size(cfg, db_size);
    ASSERT(s == PMEMKV_STATUS_OK);
    s = pmemkv_config_put_force_create(cfg, true);
    ASSERT(s == PMEMKV_STATUS_OK);
    printf("Opening pmemkv database\n");
    s = pmemkv_open(engine, cfg, kv);
    ASSERT(s == PMEMKV_STATUS_OK);
    ASSERT(kv != NULL);
    return 0;
}

static void sst(struct pass0_state *ps) {
    printf("Creating sst\n");

    char *fp;
    unsigned long long offset = 0;
    char sst_path[100];
    sprintf(sst_path, "%s/sst", pmemdir);
    int is_pmem;
    size_t sst_mapped_len;
    long long sst_size = BLOCKSIZE * sizeof(PostIt) * ps->psinfo->blocki + ps->psinfo->bucketi*sizeof(unsigned);

    #ifdef TIMER
    start_timer(timer_sst,0);
    #endif

    if ((fp = (char *)pmem_map_file(sst_path, sst_size, PMEM_FILE_CREATE, 0666, &sst_mapped_len, &is_pmem)) == NULL) {
        perror("pmem_map_file");
        exit(1);
    }

    memset(fp, 0, sst_size);

    // cmap
//    pmemkv_db *sst_db = NULL;
//    printf("Creating a new config\n");
//    pmemkv_config *cfg = pmemkv_config_new();
//    ASSERT(cfg != NULL);
//
//    int s = pmemkv_config_put_path(cfg, "/mnt/pmem1.0/ansont/sst.db");
//    ASSERT(s == PMEMKV_STATUS_OK);
//    s = pmemkv_config_put_size(cfg, 5*GB);
//    ASSERT(s == PMEMKV_STATUS_OK);
//    s = pmemkv_config_put_force_create(cfg, true);
//    ASSERT(s == PMEMKV_STATUS_OK);
//    printf("Opening sst database\n");
//    s = pmemkv_open("cmap", cfg, &sst_db);
//    ASSERT(s == PMEMKV_STATUS_OK);
//    ASSERT(sst_db != NULL);

    DB *w2p_db;
    char w2p_path[MAXFILENAME];
    int err = db_create(&w2p_db, NULL, 0);
    sprintf(w2p_path, "%s/w2p.db", pmemdir);

    if (err) {
        fprintf(stderr,"failed to create db %s\n", strerror(errno));
        exit(2);
    }
    err = w2p_db->open(w2p_db, NULL, w2p_path, NULL, DB_BTREE, DB_TRUNCATE|DB_CREATE, 0666);
    if (err) {
        fprintf(stderr,"failed to open db %s\n", strerror(errno));
        exit(2);
    }


    for (int i = 0; i < ps->psinfo->maxbuckets; i++) {
        struct Bucket *bu = &ps->buckets[i];

        if (bu->used != 0) {
            struct Block *bl = &ps->blocks[bu->b0];

            //        char val[MAX_VAL_LEN];
            //        sprintf(val, "%d", offset);
            //        s = pmemkv_put(sst_db, bu->word, strlen(bu->word), val, MAX_VAL_LEN);
            //        ASSERT(s == PMEMKV_STATUS_OK);

            DBT key, data;
            bzero(&key,sizeof(key));
            bzero(&data,sizeof(data));

            //printf("mkdb try put: %s\n", bu->word);

            key.data = (void *) bu->word;
            key.size = strlen(bu->word) + 1;
            data.data = &offset;
            data.size = sizeof(offset);
            if((err = w2p_db->put(w2p_db, NULL, &key, &data, DB_NOOVERWRITE)) != 0){
                printf("mkdb: db->put failed %s\n", db_strerror(err));
            }


            memcpy(fp+offset, &bu->n, sizeof(bu->n));
            unsigned docCount = *(fp + offset);
            printf("docCount:%u\n", docCount);
            //*(fp+offset) = bu->n;
            offset += sizeof(bu->n);
            //xwrite2(&(bu->n), sizeof(bu->n), fp, &offset);


            while (1) {
                for (int pi=0; pi<bl->n; pi++) {
                    memcpy(fp+offset, &bl->p[pi], sizeof(PostIt));
                    //*(fp+offset) = bl->p[pi];
                    offset += sizeof(PostIt);
                    //xwrite2(&bl->p[pi], sizeof(PostIt), fp, &offset);
                }
                if (bl->next != 0) {
                    bl = &ps->blocks[bl->next];
                } else {
                    break;
                }
            }
        }



    }

    #ifdef TIMER
    end_timer(timer_sst,0);
    #endif

    assert(w2p_db);
    if(w2p_db->close(w2p_db, 0) != 0){
        fprintf(stderr, "pedsort: db close failed %s\n", strerror(errno));
        exit(1);
    }
    w2p_db = NULL;

    pmem_persist(fp, sst_mapped_len);
    pmem_unmap(sst_path, sst_mapped_len);
    pmemkv_close(sst_db);
}

int main(int argc, char *argv[]) {
  char ch;
  printrusage(1);

  update_only = false;

  while ((ch = getopt(argc, argv, "p:")) != -1) {
    switch (ch) {
      case 'p':
        pmemdir = optarg;
        break;
      default:
        break;
    }
  }
  argc -= optind;
  argv += optind;

  if (argc != 0) {
    fprintf(stderr,"./indexer [-p pmemdir]\n");
    exit(1);
  }

#ifdef TIMER
  initialize_timer(&timer_main, 0, "main");
  initialize_timer(&timer_n2f, 0, "n2f");

  timer_pass0 = (struct timer*) malloc(ncore * sizeof(struct timer));
  timer_alloc_table = (struct timer*) malloc(ncore * sizeof(struct timer));
  timer_flush = (struct timer*) malloc(ncore * sizeof(struct timer));
  timer_sst = (struct timer*) malloc(ncore * sizeof(struct timer));

  initialize_timer(timer_pass0, 0, "pass0");
  initialize_timer(timer_alloc_table, 0, "alloc-table");
  initialize_timer(timer_flush, 0, "flush");
  initialize_timer(timer_sst, 0, "sst");
#endif

#ifdef TIMER
  start_timer(&timer_main,0);
#endif

  Args *a = new Args(config);
  maxwordlen = a->nget<unsigned>("maxwordlen", 100);

  // Increase my FD limit as much as possible
  struct rlimit fdlim;
  if (getrlimit(RLIMIT_NOFILE, &fdlim) < 0) {
      perror("getrlimit failed");
      exit(-1);
  }
  fdlim.rlim_cur = fdlim.rlim_max;
  if (setrlimit(RLIMIT_NOFILE, &fdlim) < 0) {
      perror("setrlimit failed");
      exit(-1);
  }

#ifdef N2F_CMAP_PM
  char n2f_db_path[100];
  uint64_t N2F_DB_SIZE = 5 * GB;
  sprintf(n2f_db_path, "%s/n2f.db", pmemdir);
  int s = init_kv("cmap",n2f_db_path, N2F_DB_SIZE, &n2f_db);
  ASSERT(n2f_db != NULL);
  #ifdef DEBUG
    printf("Opened N2F DB\n");
  #endif
#endif

#ifdef TIMER
  start_timer(&timer_n2f,0);
#endif
  while (fgets(files[max_did], MAXFILENAME, stdin) != NULL) {
    files[max_did][strlen(files[max_did])-1] = '\0';
    char *key = (char*)malloc(sizeof(char)*50);
    sprintf(key,"%lld",max_did);
    char *value = files[max_did];
    s = pmemkv_put(n2f_db, key, strlen(key), value, strlen(value));
    ASSERT(s == PMEMKV_STATUS_OK);
    max_did++;

    assert(max_did < NFILES);
  }
#ifdef TIMER
  end_timer(&timer_n2f,0);
#endif

#ifdef DEBUG
  printf("max_did:%d nfiles:%d\n",max_did,NFILES);
#endif

#ifdef W2B_CMAP_PM
  char w2b_dbname[100]; // word to bucket db name
  sprintf(w2b_dbname, "%s/w2b.db", pmemdir);
  uint64_t W2B_DB_SIZE = 5*GB; //create a 1 Gb file
  s = init_kv("cmap", w2b_dbname, W2B_DB_SIZE, &w2b_db);
  #ifdef DEBUG
  printf("Opened W2B DB\n");
  #endif
#endif

  initshared();
  dofiles();

#ifdef N2F_CMAP_PM
  LOG("Closing w2b database\n"); pmemkv_close(w2b_db);
#endif

#ifdef W2B_CMAP_PM
  LOG("Closing n2f database\n"); pmemkv_close(n2f_db);
#endif

#ifdef TIMER
  end_timer(&timer_main,0);
  print_uni_timer(&timer_main);
#endif

  exit(0);
}


void *dofiles()
{
#ifdef DEBUG
  printf("dofiles\n");
#endif

  struct pass0_state ps;
  int cid = 0;
  int pass0files = 0;
  int nfile = 0;
  int nword = 0;
  int nwordlast = 0;
  int is_pmem;

  char psinfo_path[100];
  sprintf(psinfo_path, "%s/ps/psinfo", pmemdir);
  size_t psinfo_mapped_len;

  char buckets_path[100];
  sprintf(buckets_path, "%s/ps/buckets", pmemdir);
  size_t buckets_mapped_len;

  char blocks_path[100];
  sprintf(blocks_path, "%s/ps/blocks", pmemdir);
  size_t blocks_mapped_len;

  #ifdef TIMER
  start_timer(timer_alloc_table, cid);
  #endif

  if ((ps.psinfo = (struct pass0_state_info *) pmem_map_file(psinfo_path, sizeof(struct pass0_state_info), PMEM_FILE_CREATE, 0666, &psinfo_mapped_len, &is_pmem)) == NULL) {
      perror("pmem_map_file");
      exit(1);
  }

#ifdef DEBUG
  printf("psinfo:ispmem:%d,mappedlen:%d\n", is_pmem, psinfo_mapped_len);
#endif

  ps.psinfo->bucketi = 0;
  ps.psinfo->blocki = 0;
  ps.psinfo->maxinfo = 15*GB;
  ps.psinfo->maxword = GB;
  ps.psinfo->maxblocks = 25*GB/sizeof(struct Block);
  ps.psinfo->maxbuckets = GB/sizeof(struct Bucket);

  ps.wordi = 0;
  ps.infoi = 0;
  ps.psinfo->doci = 0;

  ps.wordbytes=(char*)malloc(ps.psinfo->maxword);
  ps.infobuf= (PostIt *)malloc(sizeof(PostIt)*ps.psinfo->maxinfo);

  if ((ps.buckets=(struct Bucket *)pmem_map_file(buckets_path, sizeof(struct Bucket) * ps.psinfo->maxbuckets, PMEM_FILE_CREATE, 0666, &buckets_mapped_len, &is_pmem)) == NULL) {
      perror("pmem_map_file");
      exit(1);
  }
  memset(ps.buckets, 0, sizeof(struct Bucket) * ps.psinfo->maxbuckets);

#ifdef DEBUG
  printf("buckets:ispmem:%d,mappedlen:%d\n", is_pmem, buckets_mapped_len);
#endif

  if ((ps.blocks=(struct Block *)pmem_map_file(blocks_path, sizeof(struct Block)*ps.psinfo->maxblocks, PMEM_FILE_CREATE, 0666, &blocks_mapped_len, &is_pmem)) == NULL) {
      perror("pmem_map_file");
      exit(1);
  }
  memset(ps.blocks, 0, ps.psinfo->maxblocks * sizeof(struct Block));

#ifdef DEBUG
  printf("blocks:ispmem:%d,mappedlen:%d\n", is_pmem, blocks_mapped_len);
#endif

#ifdef TIMER
  end_timer(timer_alloc_table, cid);
#endif

#ifdef DEBUG
  printf("size of PostIt = %d \n",sizeof(PostIt));
  printf("size of Bucket = %d \n",sizeof(struct Bucket));
  printf("size of Block = %d \n",sizeof(struct Block));
  printf("maxinfo %lld \n", ps.psinfo->maxinfo);
  printf("maxword %lld \n", ps.psinfo->maxword);
  printf("maxblocks %lld \n",ps.psinfo->maxblocks);
#endif

  assert(ps.wordbytes && ps.infobuf && ps.blocks && ps.buckets);

  while (1) {

    if (shared->did >= max_did) // Anson move
        break;

    DID d = shared->did;
    shared->did += 1;

    FILE *input = fopen((const char *) files[d], "r");

    if (input == 0) {
        printf("input==0\n");
      fprintf(stderr, "dofiles: couldn't open %lld: %s %s\n", d, files[d], strerror(errno));
    }

    nwordlast = pass0(cid, input, d, &pass0files, &ps);
    nword += nwordlast;
    fclose(input);
    nfile++;
  }

#ifdef DEBUG
  printf("Finished pass0\n");
  printf("bucketi %lld\n", ps.psinfo->bucketi);
  printf("blocki %lld\n", ps.psinfo->blocki);
  printf("infoi %lld\n", ps.infoi);
  printf("wordi %lld\n", ps.wordi);
  printf("doci %lld\n",ps.psinfo->doci);
#endif

#ifdef FLUSH
  #ifdef TIMER
  start_timer(timer_flush, cid);
  #endif
  pmem_persist(ps.psinfo, sizeof(pass0_state_info));
  pmem_persist(ps.buckets, sizeof(Bucket) * ps.psinfo->bucketi);
  pmem_persist(ps.blocks, sizeof(Block) * ps.psinfo->blocki);
  printf("flushed\n");
  #ifdef TIMER
  end_timer(timer_flush, cid);
  #endif
#endif

#ifdef SST
  sst(&ps);
#endif

  pmem_unmap(psinfo_path, psinfo_mapped_len);
  pmem_unmap(buckets_path, buckets_mapped_len);
  pmem_unmap(blocks_path, blocks_mapped_len);
  free (ps.infobuf);
  free (ps.wordbytes);

#ifdef DEBUG
  printf("unmapped pmem\n");
#endif

  if (shared->first) {
    shared->first = 0;
    fprintf(stdout, "pedsort %d: nfile %d, nword %d,  hashsize %d, pass0files %d,nwordlast %d, total: ", cid, nfile, nword, ps.psinfo->maxbuckets, pass0files, nwordlast);
    float r = printrusage(0);
    fprintf(stdout, " throughput: %f", ((60*60)  / r) / ncore);
    fprintf(stdout, "\n");
  }
#ifdef TIMER
  printf("%s %s %s %s: ", "alloc_table","pass0", "flush", "sst");
  print_timer(timer_alloc_table, cid);
  print_timer(timer_pass0, cid);
  print_timer(timer_flush, cid);
  print_timer(timer_sst, cid);
  printf("\n");
#endif
  return 0;
}

int lookup(struct pass0_state *ps, char *word) {
    int i;
    unsigned int h;
    unsigned int k = 0;
    unsigned int o;

    for(i = 0; word[i]; i++)
        k = (k * 33) + word[i];
    h = k % ps->psinfo->maxbuckets;
    o = 1 + (k % (ps->psinfo->maxbuckets - 1));
    for(i = 0; i < ps->psinfo->maxbuckets; i++){
        if(ps->buckets[h].used == 0)
            return(h);
        if(strcmp(ps->buckets[h].word, word) == 0)
            return(h);
        h += o;
        if(h >= (unsigned int)ps->psinfo->maxbuckets)
            h = h - ps->psinfo->maxbuckets;
    }
    fprintf(stderr, "pedsort: hash table full\n");
    exit(1);
}

int pass0(int cid, FILE *input, DID did, int *pass0files, struct pass0_state *ps) {
  char *p;
  struct Bucket *bu;
  struct Block *bl;
  PostIt *infop;
  int len, c, skip;
  unsigned wc = 0;
#ifdef TIMER
  start_timer(timer_pass0, cid);
#endif
  while(1){
      len = 0;
      skip = 0;
      p = ps->wordbytes + ps->wordi; // todo wordbytes never changed
      while((c = getc(input)) != EOF) {
          if (WORDCHAR(c)) {
              p[len] = tolower(c);
              len++;
          } else {
              p[len] = '\0';
              if (len == 0) {
                  p++;
                  skip++;
                  continue;
              } else
                  len++;
              break;
          }
      }
      wc++; // inc word count
      if(len == 0) {
          assert(c == EOF);
          break; // exit if file is empty
      }
      assert(len>0);

      infop = ps->infobuf + ps->infoi;
      infop->dn = did;
      infop->wc = wc;
      ps->infoi++;

      if (strlen(p) < MAXWORDLEN) {
        #ifdef W2B_CMAP_PM
        int s = pmemkv_exists(w2b_db, p, strlen(p)); // check if key exists
        if (s == PMEMKV_STATUS_OK) {
          // printf("word found in cmap\n");
          char val[MAX_VAL_LEN];
          s = pmemkv_get_copy(w2b_db, p, strlen(p), val, MAX_VAL_LEN, NULL);
          // printf("index:%s\n", val);
          ASSERT(s == PMEMKV_STATUS_OK);
          bu = &ps->buckets[atoi(val)];
        } else if (s == PMEMKV_STATUS_NOT_FOUND) {
          //printf("word not found in cmap\n");
          char val[MAX_VAL_LEN];
          sprintf(val, "%d", ps->psinfo->bucketi);
          s = pmemkv_put(w2b_db, p, strlen(p), val, MAX_VAL_LEN);
          ASSERT(s == PMEMKV_STATUS_OK);
          bu = &ps->buckets[ps->psinfo->bucketi];
        } else {
          printf("error with cmap\n");
          exit(1);
        }
        #else
          bu = &ps->buckets[lookup(ps, p)];
        #endif
          if(bu->used == 0){
              ps->psinfo->bucketi++;
              bu->used = 1;
              strncpy(bu->word, p, sizeof(bu->word)-1);
              //printf("Word: %s\n", bu->word);

              ps->wordi += len + skip;
              bu->n = 0;
              bu->b0 = bu->bN = ps->psinfo->blocki++;
              bl = &ps->blocks[bu->b0];
              bl->n = 0;
              bl->next = 0;
          } else if(ps->blocks[bu->bN].n >= BLOCKSIZE){
              ps->blocks[bu->bN].next = ps->psinfo->blocki++; //new block
              bl = &ps->blocks[ps->blocks[bu->bN].next];
              bu->bN = ps->blocks[bu->bN].next;
              bl->next = 0;
              bl->n = 0;
          } else {
              //printf("same block");
              bl = &ps->blocks[bu->bN];
          }
          bl->p[bl->n] = *infop;
          bl->n += 1;
          bu->n += 1;
      }
  }
    #ifdef TIMER
          end_timer(timer_pass0, cid);
    #endif
  ps->psinfo->doci += 1;
  return wc;
}





float
printrusage(int init)
{
  static struct rusage oru;
  static double _or;
  struct rusage ru;
  struct timeval tv;
  double u, s, r;
  long i, o;

  gettimeofday(&tv, (struct timezone *) 0);
  if(getrusage(RUSAGE_SELF, &ru) < 0){
    perror("pedsort: getrusage");
    return 0.0;
  }

  if (init) {
    oru = ru;
    _or = tv.tv_sec + (tv.tv_usec / 1000000.0);
    return 0.0;
  }

  u = ru.ru_utime.tv_sec + (ru.ru_utime.tv_usec / 1000000.0);
  u -= oru.ru_utime.tv_sec + (oru.ru_utime.tv_usec / 1000000.0);
  s = ru.ru_stime.tv_sec + (ru.ru_stime.tv_usec / 1000000.0);
  s -= oru.ru_stime.tv_sec + (oru.ru_stime.tv_usec / 1000000.0);
  r = tv.tv_sec + (tv.tv_usec / 1000000.0);
  r -= _or;
  i = ru.ru_inblock;
  i -= oru.ru_inblock;
  o = ru.ru_oublock;
  o -= oru.ru_oublock;

  fprintf(stdout, "%.2fu %.2fs %.2fr %ldi %ldo", u, s, r, i, o);
  return r;
}

