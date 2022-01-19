LDB = /home/shoaiba/mosbench/libdb/db4.7-mod/include
CXXFLAGS := -O2 -MD -Wmisleading-indentation -Wunused-but-set-variable -Wint-to-pointer-cast  # -g -fno-omit-frame-pointer
CXXFLAGS += -I$(LDB) -I/home/shoaiba/pmem/pmemkv/src -I/home/shoaiba/pmem/pmdk/include
LDFLAGS += -L/home/shoaiba/mosbench/libdb/build/db4.7-mod 
LDFLAGS += -L/home/shoaiba/pmem/pmemkv/lib -L/home/shoaiba/pmem/pmdk/lib

TABLE_PM += -DN2F_CMAP_PM -DFLUSH
CMAP_PM += -DN2F_CMAP_PM -DW2B_CMAP_PM -DFLUSH
TABLE_SST += -DN2F_CMAP_PM -DSST -DFLUSH
QE_SST_DC += -DSST -DDRAM_CACHE
QE_PM += -DPM_TABLE
QE_PM_DC += -DPM_TABLE -DDRAM_CACHE
QE_CMAP_PM += -DPM_TABLE -DW2B_CMAP_PM
DRAM_CACHE_PM += -DDRAM_CACHE


OBJS1 := args.o cmap-pm.o
OBJS3 := args.o table-dram.o
OBJS4 := args.o table-pm.o
OBJS10 := args.o table-sst.o

OBJS2 := args.o qe-cmap-pm.o
OBJS5 := args.o qe-stock.o
OBJS7 := args.o qe-table-pm.o
OBJS11 := args.o qe-table-sst.o

OBJS12 := args.o qe2-cmap-pm.o
OBJS13 := args.o qe2-stock.o
OBJS14 := args.o qe2-table-pm.o
OBJS15 := args.o qe2-table-sst.o

cmap-pm.o: indexer.C
	g++ -c -o $@ $(CMAP_PM) $(CXXFLAGS) $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem

table-pm.o: indexer.C
	g++ -c -o $@ $(TABLE_PM) $(CXXFLAGS) $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem

table-sst.o: indexer.C
	g++ -c -o $@ $(TABLE_SST) $(CXXFLAGS) $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem


qe-cmap-pm.o: searcher.C
	g++ -c -o $@ $(QE_CMAP_PM) $(CXXFLAGS) $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem

qe-stock.o: searcher.C
	g++ -c -o $@ $(CXXFLAGS) $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem

qe-table-pm.o: searcher.C
	g++ -c -o $@ $(QE_PM) $(CXXFLAGS) $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem

qe-table-sst.o: searcher.C
	g++ -c -o $@ $(TABLE_SST) $(CXXFLAGS) $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem


qe2-cmap-pm.o: searcherAND.C
	g++ -c -o $@ $(QE_CMAP_PM) $(CXXFLAGS) $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem

qe2-stock.o: searcherAND.C
	g++ -c -o $@ $(CXXFLAGS) $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem

qe2-table-pm.o: searcherAND.C
	g++ -c -o $@ $(QE_PM) $(CXXFLAGS) $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem

qe2-table-sst.o: searcherAND.C
	g++ -c -o $@ $(TABLE_SST) $(CXXFLAGS) $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem



cmap-pm: $(OBJS1)
	g++ -o $@ $(CXXFLAGS)  $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem
	mv cmap-pm bin

table-dram: $(OBJS3)
	g++ -o $@ $(CXXFLAGS)  $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem
	mv table-dram bin

table-sst: $(OBJS10)
	g++ -o $@ $(CXXFLAGS)  $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem
	mv table-sst bin

table-pm: $(OBJS4)
	g++ -o $@ $(CXXFLAGS)  $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem
	mv table-pm bin


qe-cmap-pm: $(OBJS2)
	g++ -o $@ $(CXXFLAGS)  $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem
	mv qe-cmap-pm bin

qe-stock: $(OBJS5)
	g++ -o $@ $(CXXFLAGS)  $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem
	mv qe-stock bin

qe-table-pm: $(OBJS7)
	g++ -o $@ $(CXXFLAGS)  $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem
	mv qe-table-pm bin

qe-table-sst: $(OBJS11)
	g++ -o $@ $(CXXFLAGS)  $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem
	mv qe-table-sst bin


qe2-cmap-pm: $(OBJS12)
	g++ -o $@ $(CXXFLAGS)  $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem
	mv qe2-cmap-pm bin

qe2-stock: $(OBJS13)
	g++ -o $@ $(CXXFLAGS)  $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem
	mv qe2-stock bin

qe2-table-pm: $(OBJS14)
	g++ -o $@ $(CXXFLAGS)  $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem
	mv qe2-table-pm bin

qe2-table-sst: $(OBJS15)
	g++ -o $@ $(CXXFLAGS)  $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem
	mv qe2-table-sst bin


.PHONY: clean
clean:
	rm -f pedsort queryEval primes.C $(OBJS) $(OBJS1)

