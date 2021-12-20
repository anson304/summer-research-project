
#define LINUX
//#define PMEM_DEBUG
//#define DEBUG
//#define TABLE_NVM
//#define SPILL_NVM
//#define OBIN_NVM
//#define ODB_NVM
//#define CLFLUSH

//#define CACHE_DATA

#define TIMER
//#define SYNC

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

//static const long long N2F_DB_SIZE = 1024 * 1024 * 1024;
//static const long long OBIN_SIZE =   1024 * 1024 * 1024;


// #define COUNTER

const char *tmpdir;
const char *pmemdir;
const char *config = "mkdb.config";
const long long GB = 1024UL*1024UL*1024UL;
//pthread_mutex_t input_lock;
extern int errno;
unsigned maxwordlen;
string prefix;
int ncore = 1;
long long maxmem = 256*1024*1024;
long long NBYTES = 0;
long long N2F_DB_SIZE = 0;
long long OBIN_SIZE = 0;
DID did = 1;
DID max_did = 1;
int first = 1;
int order = 0;
int threaded = 1;
int dblim = 0;

// pmemkv db
//pmemkv_db *w2b_db = NULL;
//pmemkv_db *n2f_db = NULL;


extern int nprimes, primes[];

#define NWORDS 3000
#define MAXDIDBUFFER 512
#define MAXWORDLENGTH 64 // Anson



#define BLOCKSIZE 128
struct Block {
    int next; // next block
    int n; //number of groups of Tags
    PostIt p[BLOCKSIZE];
};

struct Bucket {
    //  char *word;
    int word;
    int b0; // first block
    int bN; // last block
    unsigned n; //number of blocks
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
    printf("%s took %.2f secs\n", t->name, t->agg);
}

static void print_timer(struct timer *t, int cid) {
    printf("%.6f\n", t[cid].agg);
}

#ifdef CLFLUSH
inline static void cl_flush(volatile void *p) {
    asm volatile ("clflushopt (%0)" :: "r"(p));
}

inline static void s_fence () {
    asm volatile("sfence" : : : "memory");
}

inline static void __flush__(volatile void *p) {
    cl_flush(p);
    s_fence();
}
#endif

struct timer timer_main;
struct timer timer_alloc_table;
struct timer *timer_query;

//#define NBYTES   (maxmem/4)  // number of bytes per data structure

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

int hash_primes[] = { 0, 0, 0, 0, 0, 53, 97, 193, 389, 769, 1543, 3079, 6151, 12289, 24593, 49157, 98317, 196613, 393241, 786433, 1572869, 3145739, 6291469, 12582917, 25165843, 50331653, 100663319, 201326611, 402653189, 805306457, 1610612741};

bool update_only;
//struct pass0_state * pstate();
//void *pstate_close();
float printrusage(int init);
void query_term(char *term, struct pass0_state *ps);

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

PostIt* query_term_buffer(char *term, int *bufferi) {

    PostIt *bufferP;

    char dbname[100];
    char filename[100];
    int cid = 0;
    DB *w2p_db = NULL;
    FILE *fp;
    int err;

    string w = string(term);

    #ifdef TIMER
    start_timer(timer_query, 0);
    #endif


    sprintf(filename, "%s%d/%s-f-%d", "/mnt/nvme-1.0/anson/stock/large/db/db", cid, "ind", cid);
    fp = fopen(filename,"r");

    if (!fp) {
        fprintf(stderr, "error opening %s\n", filename);
        perror("qe.C: open ");
        exit(1);
    }

    sprintf(dbname, "%s%d/%s-w2p.db-%d", "/mnt/nvme-1.0/anson/stock/large/db/db", cid, "ind", cid);
    err = db_create(&w2p_db, NULL, 0);
    assert(!err);
    err = w2p_db->open(w2p_db, NULL, dbname, NULL, DB_BTREE, DB_RDONLY,  0666);
    if (err) {
        fprintf(stderr, "failed to open %s\n", dbname);
        exit(1);
    }



    //printf("Timer Started\n");

    ind_offset offset;
    DBT key, data;
    bzero(&key,sizeof(key));
    bzero(&data,sizeof(data));
    key.data = (void *)w.c_str();
    key.size = w.size() + 1;
    data.data = &offset;
    data.size = sizeof(offset);
    size_t _in_core_p_sz;
    void *_in_core_p_real;
    unsigned _max = 0;

    char *_incore_vec = NULL;

    //printf("Get offset\n");
    if (w2p_db) {
        if ((w2p_db->get(w2p_db, NULL, &key, &data, 0) != 0)
        || (data.size != sizeof(offset))) {
//            _max = _in_core_p = 0;
            printf("no such word found in database\n");
            return bufferP;
        }
        memcpy(&offset,data.data,sizeof(offset));
    }


    //printf("Fseeko/\n");

    if (fseeko(fp,(off_t)offset,SEEK_SET) != 0) { // moves the file pointer to the offset
        fprintf(stderr,"seek error\n");
//        _max = _in_core_p = 0;
        return bufferP;
    }


    char wordbuf[100+2+sizeof(_max)]; //max word le default val is 100
    unsigned r = fread(wordbuf,1,w.size()+1+sizeof(_max),fp);
    if ((r!= (w.size()+1+sizeof(_max))) || (strcmp(w.c_str(),wordbuf)!=0)) {
        fprintf(stderr,"read error! read %d char (%s) opposed to %s\
        end of file? %u\n", r, wordbuf,w.c_str(),feof(fp)?1:0);
        //_max = _in_core_p = 0;
        return bufferP;
    }
    //printf("wordBuff: %s\n", wordbuf);
    //*bufferi += sprintf(bufferP + *bufferi, "W:%s,", wordbuf);
    //printf("r:%d\n", r);

    offset += (w.size()+1 + sizeof(_max));
    _max = *((unsigned *)(wordbuf+w.size()+1));

    bufferP = (PostIt *)malloc(sizeof(PostIt)*_max);
    printf("Allocated buffer for %d postings\n",_max);

    PostIt *_in_core = (PostIt *)xmmap(_max*sizeof(PostIt),fileno(fp),(off_t)offset, _in_core_p_real, _in_core_p_sz);
    PostIt *infop;

    if (_max > BLOCKSIZE) {
        _max = BLOCKSIZE;
    }
    for (int i=0; i < _max; i++) {
        infop = bufferP + *bufferi;
        infop->dn = _in_core->dn;
        infop->wc = _in_core->wc;
        ++*bufferi;
        //printf("PostIt,docid:%d,wc:%d\n", _in_core->dn, _in_core->wc);
        //*bufferi += sprintf(bufferP + *bufferi,"DID:%d,WC:%d,",_in_core->dn, _in_core->wc);
        //*bufferi += sprintf(bufferP + *bufferi,"%d,%d\n",_in_core->dn, _in_core->wc);
        _in_core++;
    }






    if (w2p_db)
        w2p_db->close(w2p_db,0);

    fclose(fp);

    #ifdef TIMER
    end_timer(timer_query, 0);
    #endif

    return bufferP;
}

int get_kv_callback(const char *k, size_t kb, const char *value, size_t value_bytes, void *arg) {
    printf("   visited: %s\n", k);
    return 0;
}

int main(int argc, char *argv[]) {
    char ch;


    printrusage(1);

    tmpdir = "/tmp";
    pmemdir = "/mnt/pmem1.0/ansont";

    if(getenv("TMPDIR"))
        tmpdir = getenv("TMPDIR");

    update_only = false;

    char term[MAXWORDLENGTH];


    while ((ch = getopt(argc, argv, "q:")) != -1) {
        switch (ch) {
            case 'q':
                strcpy(term, optarg);
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

    if(ncore == 1)
        OBIN_SIZE = 16 * maxmem;

#ifdef TIMER
    initialize_timer(&timer_main, 0, "main");
    initialize_timer(&timer_alloc_table, 0, "alloc_table");
    timer_query = (struct timer*) malloc(ncore * sizeof(struct timer));
    for(int core=0; core<ncore; core++) {
        initialize_timer(timer_query, core, "query");
    }
#endif

#ifdef TIMER
    start_timer(&timer_main,0);
#endif
    printf("Query: %s\n", term);
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



//  #ifdef TIMER
//    start_timer(&timer_alloc_table, cid);
//  #endif
//
//  #ifdef TIMER
//    end_timer(&timer_alloc_table, cid);
//  #endif


#ifdef COUNTER
    read_counters(cid);
    for (int i = 0; i < NPMC; i++) {
        atomic_add64_return(pmccount[i], &(shared->tot));
        printf("%d: pmc %llu:\n", cid, (unsigned long long)pmccount[i]);
    }
#endif

    // todo query
    int cid = 0;
    // print keys
    //pmemkv_get_all(w2b_db, &get_kv_callback, NULL);

    //printf("Query:\n");
    int bufferi = 0;

//    srand(time(NULL));
//    int rn = rand() % 3000;
//    int counter = 0;

    PostIt *bufferResult = query_term_buffer(term, &bufferi);
    if (bufferi > 0) {
        free (bufferResult);
    }

    printf("Query time: ");
    print_timer(timer_query, cid);


//    while (fgets(term, MAXWORDLENGTH, stdin) != NULL) {
//        term[strcspn(term, "\n")] = 0;
//        if (counter == rn) {
//            query_term_buffer(term, bufferP, &bufferi);
//            print_timer(timer_query, cid);
//            reset_Timer(timer_query, cid);
//        }
//        counter++;
//
//    }

//    printf("bufferi: %d\n",bufferi);



#ifdef COUNTER
printf("tot = %llu\n", (unsigned long long)shared->tot);
#endif

// fprintf(stdout, "%d: ", ncore);
// float r = printrusage(0);
// fprintf(stdout, " throughput: %f jobs/hour/core", ((60*60)  / r) / ncore);
// fprintf(stdout, "\n");

// printf("npfs: %d\n", get_npfs());

// LOG("Closing w2b database\n"); pmemkv_close(w2b_db);
// LOG("Closing n2f database\n"); pmemkv_close(n2f_db);



#ifdef TIMER
//printf("query: ");
//print_timer(timer_query, 0);
end_timer(&timer_main,0);
//print_uni_timer(&timer_main);
//print_uni_timer(&timer_alloc_table);

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

