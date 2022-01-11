
#define LINUX
#define TIMER
//#define DEBUG

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
#include <time.h>



#define ASSERT(expr)                                                                     \
do {                                                                             \
if (!(expr))                                                             \
puts(pmemkv_errormsg());                                         \
assert(expr);                                                            \
} while (0)

#define LOG(msg) puts(msg)

const char *tmpdir;
const char *pmemdir;
pthread_mutex_t input_lock;
const char *config = "mkdb.config";
const long long GB = 1024UL*1024UL*1024UL;
extern int errno;
int *cpuseq;
string prefix;
int ncore = 1;
long long maxmem = 256*1024*1024;
long long NBYTES = 0;
long long N2F_DB_SIZE = 0;
long long OBIN_SIZE = 0;
long long term_i = 1;
long long max_term = 1;
int first = 1;
int order = 0;
int threaded = 1;
int dblim = 0;
int currRepeat = 0;

pmemkv_db *w2b_db = NULL;
pmemkv_db *n2f_db = NULL;

#define NTERMS 100000
#define MAXWORDLENGTH 64 // Anson
#define BLOCKSIZE 128
#define MAXFILENAME 200

#define REPEATS 10

char terms[NTERMS][MAXWORDLENGTH];
double queryTimeArr[REPEATS][NTERMS];


struct Block {
    int next; // next block
    int n; //number of groups of Tags
    PostIt p[BLOCKSIZE];
};

struct Bucket {
    char word[MAXWORDLENGTH];
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

static void reset_Timer(struct timer *t, int cid) {
    t[cid].agg = 0.0;
    t[cid].start = 0.0;
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
    printf("%s took %.6f secs\n", t->name, t->agg);
}

double get_uni_timer(struct timer *t) {
    return t->agg;
}

static void print_timer(struct timer *t, int cid) {
    printf("%.6f\n", t[cid].agg);
}

static double get_timer(struct timer *t, int cid) {
    return t[cid].agg;
}

struct timer timer_main;
struct timer timer_alloc_table;
struct timer *timer_query;
struct timer timer_doterms;
struct timer timer_doterms_last;
struct timer *timer_sync;


struct pass0_state {
    char *wordbytes;
    PostIt *infobuf;
    struct Bucket *buckets;
    struct Block *blocks;
    struct pass0_state_info *psinfo;

};

struct pass0_state_info {
    long long blocki;
    long long bucketi;
    long long maxinfo;
    long long maxword;
    long long maxbuckets;
    long long maxblocks;
    long long wordi;
    long long infoi;
    long long doci;

};


struct pass0_state ps;
char *fp_sst[32];
DB *w2p_db[32];
int fp_stock[32];
char **word_ptr; //qe_term_stock2


bool update_only;

float printrusage(int init);

static struct sharedmem {
    volatile int run;
    volatile int first;
    volatile int did;
    volatile uint64_t tot;
} *shared;




#define NPMC 1

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


static void get_cpu_sequence(int order, int *seq)
{
    if (getenv("CPUSEQ")) {
        char *cpuseq = strdup(getenv("CPUSEQ"));
        char *tok, *pos = cpuseq;
        int n = 0;
        while ((tok = strsep(&pos, ",")) && n < ncore) {
            seq[n++] = atoi(tok);
        }
        free(cpuseq);

        if (n < ncore) {
            fprintf(stderr, "Number of cores requested %d > CPUSEQ %d",
                    ncore, n);
            exit(-1);
        }
        return;
    }

    // Parse cpuinfo file
    std::vector<cpuinfo> cpus;

    FILE *cpuinfo = fopen("/proc/cpuinfo", "r");
    if (cpuinfo == NULL) {
        perror("failed to open /proc/cpuinfo");
        exit(-1);
    }

    char line[1024];
    struct cpuinfo cur;
    while (fgets(line, sizeof line, cpuinfo)) {
        int *val = NULL;
        if (strncmp(line, "processor\t", 10) == 0)
            val = &cur.proc;
        else if (strncmp(line, "physical id\t", 12) == 0)
            val = &cur.phys;
        if (val)
            *val = atoi(strchr(line, ':')+1);

        if (line[0] == '\n')
            cpus.push_back(cur);
    }

    fclose(cpuinfo);

    if (ncore > (int)cpus.size()) {
        fprintf(stderr, "Number of cores requested %d > available cores %d\n",
                ncore, (int)cpus.size());
        exit(-1);
    }

    if (order == 0) {
        // Sequential
        for (int i = 0; i < ncore; ++i)
            seq[i] = cpus.at(i).proc;
    } else {
        // Round-robin
        int maxphys = 0;
        for (unsigned int i = 0; i < cpus.size(); ++i)
            if (cpus[i].phys > maxphys)
                maxphys = cpus[i].phys;

            int i = 0;
            while (true) {
                // Take one processor from each physical chip
                assert(!cpus.empty());
                std::set<int> phys;
                std::vector<struct cpuinfo>::iterator it;
                for (it = cpus.begin(); it != cpus.end();) {
                    if (!phys.count(it->phys)) {
                        phys.insert(it->phys);
                        seq[i++] = it->proc;
                        if (i == ncore)
                            return;
                        it = cpus.erase(it);
                    } else {
                        ++it;
                    }
                }
            }
    }
}


/*
 * mmap() doesn't like offsets not divisable by the page size.
 */
char *
xmmap(size_t len, int fd, off_t offset, void *& realp, size_t& reallen)
{
    void *p;
    size_t nlen;
    off_t noffset;
    int pagesize = getpagesize();

    noffset = offset & ~(pagesize-1);
    nlen = len + (offset - noffset);

    p = mmap(0, nlen, PROT_READ, MAP_SHARED, fd, noffset);
    if(p == (void *)-1){
        fprintf(stderr, "queryop: xmmap %ld bytes at %ld failed: %s\n",
                (long)nlen,
                (long)noffset,
                strerror(errno));
        exit(1);
    }
    realp = p;
    reallen = nlen;
    return((char*)p + (offset - noffset));
}
static pid_t gettid(void)
{
    return syscall(__NR_gettid);
}


void set_affinity(int cpu_id) {
    int tid = gettid();
    cpu_set_t mask;
    CPU_ZERO(&mask);
    //CPU_SET(((cpu_id<<2)|(cpu_id>>2)) & 15, &mask);
    CPU_SET(cpu_id, &mask);

    // printf("set_affinity: %d %d\n", tid, cpu_id);

    int r = sched_setaffinity(tid, sizeof(mask), &mask);
    if (r < 0) {
        fprintf(stderr, "couldn't set affinity for %d\n", cpu_id);
        exit(1);
    }
}


static inline int atomic_add_return(int i, volatile int *n)
{
    int __i = i;
    asm volatile("lock; xaddl %0, %1"
    : "+r" (i), "+m" (*n)
    : : "memory");
    return i + __i;
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
            //printf("samebucket\n");
            return(h);
        h += o;
        if(h >= (unsigned int)ps->psinfo->maxbuckets)
            h = h - ps->psinfo->maxbuckets;
    }
    fprintf(stderr, "pedsort: hash table full\n");
    exit(1);
}

char* query_term_stock(char *term, int *bufferi, int cid) {

    char *bufferP;
    PostIt *infop;


    string w = string(term);

#ifdef DEBUG
    printf("New query: %s, len: %d\n", term, strlen(term));
#endif

    ind_offset offset;
    DBT key, data;
    bzero(&key,sizeof(key));
    bzero(&data,sizeof(data));
    key.data = (void *)w.c_str();
    key.size = w.size() + 1;
    data.data = &offset;
    data.size = sizeof(offset);

    unsigned docCount = 0;

    char *_incore_vec = NULL;
    #ifdef TIMER
    start_timer(timer_query, cid);
    #endif

    if ((w2p_db[cid]->get(w2p_db[cid], NULL, &key, &data, 0) != 0) || (data.size != sizeof(offset))) {
    #ifdef DEBUG
        printf("no such word found in database\n");
    #endif
        return NULL;
    }
    memcpy(&offset,data.data,sizeof(offset));

    char wordbuf[100+2+sizeof(docCount)]; //max word le default val is 100
    for(unsigned i=0; i<(100+2+sizeof(docCount)); i++)
        wordbuf[i] = *(word_ptr[cid] + offset + i);
    offset += (w.size()+1 + sizeof(docCount));
    docCount = *((unsigned *)(wordbuf+w.size()+1));

    bufferP = (char *)malloc(sizeof(PostIt)*docCount);

    for (int i=0; i<(sizeof(PostIt)*docCount); i++) {
        bufferP[i] = *(word_ptr[cid] + offset + i);
    }
    #ifdef TIMER
    end_timer(timer_query, cid);
    #endif
    return bufferP;

}



PostIt* query_term_pm(char *term, int *bufferi, int cid) {
    //printf("New query: %s, len: %d\n", term, strlen(term));

    struct Bucket *bu;
    struct Block *bl;
    PostIt *bufferP;
    PostIt *infop;
    int MAX_VAL_LEN = 64;
    int counter = 0;

    #ifdef TIMER
    start_timer(timer_query, cid);
    #endif

#ifdef W2B_CMAP_PM
    int s = pmemkv_exists(w2b_db, term, strlen(term)); // check if key exists
    if (s == PMEMKV_STATUS_OK) {
        //printf("word found in cmap\n");
        char val[MAX_VAL_LEN];
        s = pmemkv_get_copy(w2b_db, term, strlen(term), val, MAX_VAL_LEN, NULL);
        ASSERT(s == PMEMKV_STATUS_OK);
        //printf("index:%s\n", val);
        bu = &ps.buckets[atoi(val)];
    } else if (s == PMEMKV_STATUS_NOT_FOUND) {
        //printf("word not found in cmap\n");
        return NULL;
    } else {
        printf("error with cmap\n");
        exit(1);
    }

#else
    bu = &ps.buckets[lookup(&ps, term)];
#endif
    bufferP = (PostIt *)malloc(sizeof(PostIt)*bu->n);
    if(bu->used == 0){
        return NULL;
        //printf("word not found\n");
    } else {
        bl = &ps.blocks[bu->b0];
        bufferP = (PostIt *)malloc(sizeof(PostIt)*bu->n);
        //printf("Allocated buffer for %d postings\n", bu->n);

        while (1) {
            for (int i=0; i<bl->n; i++) {
                infop = bufferP + *bufferi;
                infop->dn = bl->p[i].dn;
                infop->wc = bl->p[i].wc;
                ++*bufferi;
            }
            if (bl->next != 0) {
                bl = &ps.blocks[bl->next];
            } else {
                break;
            }
        }
    }
    #ifdef TIMER
    end_timer(timer_query, cid);
    #endif



    //printf("Counter: %d\n", counter);
    return bufferP;
}




PostIt* query_term_sst(char *term, int *bufferi, int cid) {

    string w = string(term);

    unsigned long long offset;
    DBT key, data;
    bzero(&key,sizeof(key));
    bzero(&data,sizeof(data));
    key.data = (void *)w.c_str();
    key.size = w.size() + 1;
    //data.flags = DB_DBT_MALLOC;
//    data.data = malloc(sizeof offset);
    data.data = &offset;
    data.size = sizeof(offset);
    int counter = 0;
#ifdef DEBUG
    printf("New query: %s, len: %d\n", term, strlen(term));
#endif
    struct Bucket *bu;
    struct Block *bl;
    PostIt *bufferP;
    PostIt *infop;
    int MAX_VAL_LEN = 64;

    #ifdef TIMER
    start_timer(timer_query, cid);
    #endif

    if ((w2p_db[cid]->get(w2p_db[cid], NULL, &key, &data, 0) != 0) || (data.size != sizeof(offset))) {
        //printf("no such word found in database: %s", term);
        return NULL;
    }
    memcpy(&offset,data.data,sizeof(offset));

    //free(data.data);

#ifdef DEBUG
    printf("offset:%u\n", offset);
#endif

    unsigned docCount;
    //printf("docCount:%u\n", docCount);
    memcpy(&docCount, fp_sst[cid]+offset, sizeof(docCount));
#ifdef DEBUG
    printf("docCount:%u\n", docCount);
#endif
    offset += sizeof (unsigned);

    bufferP = (PostIt *)malloc(sizeof(PostIt)*docCount);
#ifdef DEBUG
    printf("Allocated buffer for %d postings\n", sizeof(PostIt)*docCount);
#endif


    memcpy(bufferP, fp_sst[cid]+offset, sizeof(PostIt)*docCount);
    *bufferi = sizeof(PostIt)*docCount;

#ifdef DEBUG
    for (int i=0; i<docCount; i++) {
        infop = bufferP + i;
        printf("dn: %d, wc: %d\n", infop->dn, infop->wc);
        counter++;
    }
#endif



#ifdef TIMER
    end_timer(timer_query, cid);
#endif

#ifdef DEBUG
    printf("Counter: %d\n", counter);
#endif
    return bufferP;
}

static int open_kv(char *engine, char *path, pmemkv_db **kv) {
    pmemkv_config *cfg = pmemkv_config_new();
    ASSERT(cfg != NULL);

    int s = pmemkv_config_put_path(cfg, path);
    ASSERT(s == PMEMKV_STATUS_OK);
    s = pmemkv_open(engine, cfg, kv);
    ASSERT(s == PMEMKV_STATUS_OK);
    ASSERT(kv != NULL);
    return 0;
}


int get_kv_callback(const char *k, size_t kb, const char *value, size_t value_bytes, void *arg) {
    printf("   visited: %s\n", k);
    return 0;
}


void *doterms(void *arg) {
    int cid = (long long) arg;

    int c = cpuseq[cid];
    set_affinity(c);
    //printf("%d assigned to core %d\n", cid, c);

    //  pthread_mutex_lock(&input_lock);
    while (1) {
        #ifdef TIMER
            start_timer(timer_sync, cid);
        #endif
        long long d = atomic_add_return(1, &(shared->did));
        if (shared->did >= max_term)
            break;
        #ifdef TIMER
            end_timer(timer_sync, cid);
        #endif
        //printf("cid: %d, Query: %s\n", cid, terms[d]);
        int bufferi = 0;

        PostIt *bufferResult;
        char *bufferResult2;

        #ifdef SST
        bufferResult = query_term_sst(terms[d], &bufferi, cid);
        if (bufferi > 0) {
            free (bufferResult);
        }
        #elif PM_TABLE
        bufferResult = query_term_pm(terms[d], &bufferi, cid);
        if (bufferi > 0) {
            free (bufferResult);
        }
        #else
        bufferResult2 = query_term_stock(terms[d], &bufferi, cid);
        if (bufferi > 0) {
            free (bufferResult2);
        }
        #endif


        //printf("cid: %d, bufferi: %d\n", cid, bufferi);
        // pthread_mutex_lock(&input_lock);
//        printf("Query time: ");

//        print_timer(timer_query, cid);
        queryTimeArr[currRepeat][d] = get_timer(timer_query, cid);
        reset_Timer(timer_query, cid);
    }
    // pthread_mutex_unlock(&input_lock);

}

int cmpfunc (const void * a, const void * b)
{
    return (*(double*)a > *(double*)b) ? 1 : (*(double*)a < *(double*)b) ? -1:0 ;
}

int main(int argc, char *argv[]) {
    char ch;

    printrusage(1);

    update_only = false;

    while ((ch = getopt(argc, argv, "p:c:")) != -1) {
        switch (ch) {
            case 'p':
                pmemdir = optarg;
                break;
            case 'c':
                ncore = atoi (optarg);
                break;
            default:
                break;
        }
    }
    argc -= optind;
    argv += optind;

    if (argc != 0) {
        fprintf(stderr,"./pedsort [-t tmpdir] [-u (update)] [-f config_file] [-c ncore] [-s sched] [-p] [-l dblim]\n");
        exit(1);
    }



#ifdef TIMER
    initialize_timer(&timer_main, 0, "main");
    initialize_timer(&timer_alloc_table, 0, "alloc_table");
    initialize_timer(&timer_doterms, 0, "doterms");
    initialize_timer(&timer_doterms_last, 0, "doterms_last");

    timer_sync = (struct timer*) malloc(ncore * sizeof(struct timer));
    timer_query = (struct timer*) malloc(ncore * sizeof(struct timer));
    for(int core=0; core<ncore; core++) {
        initialize_timer(timer_query, core, "query");
        initialize_timer(timer_sync, core, "sync");
    }

#endif

#ifdef TIMER
    start_timer(&timer_main,0);
#endif

    Args *a = new Args(config);
    cpuseq = new int[ncore];
    get_cpu_sequence(order, cpuseq);

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

    pthread_mutex_init(&input_lock, NULL);

    while (fgets(terms[max_term], MAXWORDLENGTH, stdin) != NULL) {
        assert(strlen(terms[max_term]) < MAXWORDLENGTH);
        assert(terms[max_term][strlen(terms[max_term])-1] == '\n');
        terms[max_term][strlen(terms[max_term])-1] = '\0';
        for (int i=0; i < strlen(terms[max_term]); i++) {
            terms[max_term][i] = tolower(terms[max_term][i]);
        }
        max_term++;
        assert(max_term < NTERMS);
    }

#ifdef TIMER
    start_timer(&timer_alloc_table, 0);
#endif

    #ifdef PM_TABLE
        char psinfo_path[100];
        sprintf(psinfo_path, "%s/ps/psinfo", pmemdir);
        size_t psinfo_mapped_len;

        char buckets_path[100];
        sprintf(buckets_path, "%s/ps/buckets", pmemdir);
        size_t buckets_mapped_len;

        char blocks_path[100];
        sprintf(blocks_path, "%s/ps/blocks", pmemdir);
        size_t blocks_mapped_len;

        int is_pmem;

        int psinfo_file = open (psinfo_path, O_RDONLY, 0640);
        int buckets_file = open (buckets_path, O_RDONLY, 0640);
        int blocks_file = open (blocks_path, O_RDONLY, 0640);

        ps.psinfo = (struct pass0_state_info *)mmap (0, sizeof(struct pass0_state_info), PROT_READ, MAP_SHARED, psinfo_file, 0);
        ps.buckets = (struct Bucket *)mmap (0, sizeof(struct Bucket) * ps.psinfo->maxbuckets, PROT_READ, MAP_SHARED, buckets_file, 0);
        ps.blocks = (struct Block *)mmap (0, sizeof(struct Block) * ps.psinfo->maxblocks, PROT_READ, MAP_SHARED, blocks_file, 0);
    #elif SST
        char psinfo_path[100];
        sprintf(psinfo_path, "%s/ps/psinfo", pmemdir);
        size_t psinfo_mapped_len;
        char sst_path[100];
        sprintf(sst_path, "%s/sst", pmemdir);
        size_t sst_mapped_len;

        int is_pmem;

        int psinfo_file = open (psinfo_path, O_RDONLY, 0640);
        int sst_file = open (sst_path, O_RDONLY, 0640);

        pass0_state_info *psinfo = (struct pass0_state_info *)mmap (0, sizeof(struct pass0_state_info), PROT_READ, MAP_SHARED, psinfo_file, 0);
        long long sst_size = BLOCKSIZE * sizeof(PostIt) * psinfo->blocki + psinfo->bucketi*sizeof(unsigned);

        char w2p_path[MAXFILENAME];
        sprintf(w2p_path, "/dev/shm/w2p.db");

        for (int i = 0; i < ncore; i++) {
            fp_sst[i] = (char *)mmap (0, sst_size, PROT_READ, MAP_SHARED, sst_file, 0);
            int err = db_create(&w2p_db[i], NULL, 0);
            err = w2p_db[i]->open(w2p_db[i], NULL, w2p_path, NULL, DB_BTREE, DB_RDONLY,  0666);
            if (err) {
                fprintf(stderr, "failed to open %s\n", w2p_path);
                exit(1);
            }
        }

    #else
        char filename[100];
        sprintf(filename, "%s0/%s-f-0", "/mnt/nvme-1.0/anson/stock/large/db/db", "ind");


        if (!fp_stock) {
            fprintf(stderr, "error opening %s\n", filename);
            perror("qe.C: open ");
            exit(1);
        }

        char dbname[100];
        sprintf(dbname, "%s0/%s-w2p.db-0", "/mnt/nvme-1.0/anson/stock/large/db/db", "ind");

        word_ptr = (char**) malloc(ncore * sizeof(char*)); //qe_term_stock2
        for (int i = 0; i < ncore; i++) {
            fp_stock[i] = open(filename,O_RDONLY,0640);
            word_ptr[i] = (char *) mmap (0, 17179869184, PROT_READ, MAP_SHARED, fp_stock[i], 0); //qe_term_stock2
            int err = db_create(&w2p_db[i], NULL, 0);
            assert(!err);
            err = w2p_db[i]->open(w2p_db[i], NULL, dbname, NULL, DB_BTREE, DB_RDONLY,  0666);
            if (err) {
                fprintf(stderr, "failed to open %s\n", dbname);
                exit(1);
            }
        }

    #endif
#ifdef TIMER
    end_timer(&timer_alloc_table, 0);
#endif

    printf("Finished alloc table\n");

#ifdef W2B_CMAP_PM
    char w2b_dbname[100]; // word to bucket db name
    sprintf(w2b_dbname, "%s/w2b.db", pmemdir);
    open_kv("cmap", w2b_dbname, &w2b_db);
    printf("Open cmap db\n");
#endif


    fflush(stdout);
    initshared();

    #ifdef TIMER
        start_timer(&timer_doterms,0);
    #endif

        for (currRepeat = 0; currRepeat < REPEATS; currRepeat++) { // 5 repeats

        #ifdef TIMER
            if (currRepeat == REPEATS-1) {
                start_timer(&timer_doterms_last,0);
            }
        #endif
            pthread_t *tha = new pthread_t[ncore];
            void *value;
            shared->did = 1;

            for(int i = 0; i < ncore; i++)
                pthread_create(&(tha[i]), NULL, &doterms, (void *) i);

            for(int i = 0; i < ncore; i++)
                assert(pthread_join(tha[i], &value) == 0);
            delete[] tha;
        #ifdef TIMER
            if (currRepeat == REPEATS-1) {
                end_timer(&timer_doterms_last,0);
            }
        #endif
        }
    #ifdef TIMER
        end_timer(&timer_doterms,0);
    #endif
    printf("Finished doterms\n");


#ifdef W2B_CMAP_PM
    LOG("Closing n2f database\n"); pmemkv_close(w2b_db);
#endif

#ifdef PM_TABLE
    munmap(ps.buckets, sizeof(struct Bucket) * ps.psinfo->maxbuckets);
    munmap(ps.blocks, sizeof(struct Block) * ps.psinfo->maxblocks);
    munmap(ps.psinfo, sizeof(struct pass0_state_info));
#elif SST

//    if (w2p_db)
    for (int i = 0; i < ncore; i++) {
        w2p_db[i]->close(w2p_db[i],0);
        munmap(fp_sst[i], sst_size);
    }

    munmap(psinfo, sizeof(struct pass0_state_info));


#else
//    if (w2p_db)
//        w2p_db->close(w2p_db,0);
    for (int i = 0; i < ncore; i++) {
        w2p_db[i]->close(w2p_db[i],0);
        //fclose(fp_stock[i]);
    }


#endif



#ifdef TIMER
    end_timer(&timer_main,0);
    //print_uni_timer(&timer_main);
    //print_uni_timer(&timer_alloc_table);


//    printf("doterms avg: %.6f\n", get_uni_timer(&timer_doterms)/REPEATS);
//    print_uni_timer(&timer_doterms_last);
//
//    double syncTime = 0;
//
//    for (int i=0; i<ncore; i++) {
//        syncTime += get_timer(timer_sync,i);
//    }
//    syncTime = syncTime/REPEATS;
//    printf("sync: %.6f\n", syncTime);
//
//    //sort array
//    for (int r=0; r<REPEATS; r++) {
//        qsort(queryTimeArr[r], max_term, sizeof(double), cmpfunc);
//    }
//    double tailLatSum = 0.0;
//
//    for (int r=0; r<REPEATS; r++) {
//        tailLatSum += queryTimeArr[r][max_term-max_term/100-1];
//    }
//    printf("tail latency avg: %.6f\n", tailLatSum/REPEATS);
//    printf("tail latency last: %.6f\n", queryTimeArr[REPEATS-1][max_term-max_term/100-1]);


    printf("doterms avg, doterms last, sync, tail latency avg, tail latency last:\n");
    printf("%.6f\n", get_uni_timer(&timer_doterms)/REPEATS);
    printf("%.6f\n", get_uni_timer(&timer_doterms_last));

    double syncTime = 0;

    for (int i=0; i<ncore; i++) {
        syncTime += get_timer(timer_sync,i);
    }
    syncTime = syncTime/REPEATS;
    printf("%.6f\n", syncTime);

    //sort array
    for (int r=0; r<REPEATS; r++) {
        qsort(queryTimeArr[r], max_term, sizeof(double), cmpfunc);
    }
    double tailLatSum = 0.0;

    for (int r=0; r<REPEATS; r++) {
        tailLatSum += queryTimeArr[r][max_term-max_term/100-1];
    }
    printf("%.6f\n", tailLatSum/REPEATS);
    printf("%.6f\n", queryTimeArr[REPEATS-1][max_term-max_term/100-1]);









    //print tail latency

#endif

exit(0);
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

