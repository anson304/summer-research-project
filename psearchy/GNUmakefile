LDB = /home/shoaiba/mosbench/libdb/db4.7-mod/include
CXXFLAGS := -O2 -MD -Wmisleading-indentation -Wunused-but-set-variable -Wint-to-pointer-cast  # -g -fno-omit-frame-pointer
CXXFLAGS += -I$(LDB) -I/home/shoaiba/pmem/pmemkv/src -I/home/shoaiba/pmem/pmdk/include
LDFLAGS += -L/home/shoaiba/mosbench/libdb/build/db4.7-mod 
LDFLAGS += -L/home/shoaiba/pmem/pmemkv/lib -L/home/shoaiba/pmem/pmdk/lib

TABLE_PM += -DRAM_CACHE -N2F_CMAP_PM -FLUSH
CMAP_PM += -DRAM_CACHE -N2F_CMAP_PM -W2B_CMAP_PM -FLUSH
TABLE_SST += -DRAM_CACHE -N2F_CMAP_PM -SST -FLUSH


OBJS1 := args.o cmap-pm.o
OBJS2 := args.o qe-cmap-pm.o
OBJS3 := args.o table-dram.o
OBJS4 := args.o table-pm.o
OBJS5 := args.o qe-stock.o
OBJS7 := args.o qe-table-pm.o
OBJS8 := args.o qe-table-pm-seq.o
OBJS9 := args.o qe-cmap-pm-seq.o
OBJS10 := args.o table-sst.o
OBJS11 := args.o qe-table-sst.o

cmap-pm.o: indexer.C
	g++ -c -o $@ $(CMAP_PM) $(CXXFLAGS) $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem

qe-cmap-pm.o: qe-cmap-pm.C
	g++ -c -o $@ $(CMAP_PM) $(CXXFLAGS) $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem

qe-stock.o: qe-stock.C
	g++ -c -o $@ $(TABLE_PM) $(CXXFLAGS) $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem

table-pm.o: indexer.C
	g++ -c -o $@ $(TABLE_PM) $(CXXFLAGS) $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem

qe-table-pm.o: qe-table-pm.C
	g++ -c -o $@ $(TABLE_PM) $(CXXFLAGS) $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem

qe-table-pm-seq.o: qe-table-pm-seq.C
	g++ -c -o $@ $(TABLE_PM) $(CXXFLAGS) $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem

qe-cmap-pm-seq.o: qe-cmap-pm-seq.C
	g++ -c -o $@ $(CMAP_PM) $(CXXFLAGS) $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem

table-sst.o: indexer.C
	g++ -c -o $@ $(TABLE_SST) $(CXXFLAGS) $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem

qe-table-sst.o: qe-table-sst.C
	g++ -c -o $@ $(TABLE_SST) $(CXXFLAGS) $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem

cmap-pm: $(OBJS1)
	g++ -o $@ $(CXXFLAGS)  $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem
	mv cmap-pm bin

qe-cmap-pm: $(OBJS2)
	g++ -o $@ $(CXXFLAGS)  $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem
	mv qe-cmap-pm bin

table-dram: $(OBJS3)
	g++ -o $@ $(CXXFLAGS)  $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem
	mv table-dram bin

table-pm: $(OBJS4)
	g++ -o $@ $(CXXFLAGS)  $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem
	mv table-pm bin

qe-stock: $(OBJS5)
	g++ -o $@ $(CXXFLAGS)  $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem
	mv qe-stock bin

myTest: $(OBJS6)
	g++ -o $@ $(CXXFLAGS)  $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem
	mv myTest bin

qe-table-pm: $(OBJS7)
	g++ -o $@ $(CXXFLAGS)  $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem
	mv qe-table-pm bin


qe-table-pm-seq: $(OBJS8)
	g++ -o $@ $(CXXFLAGS)  $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem
	mv qe-table-pm-seq bin

qe-cmap-pm-seq: $(OBJS9)
	g++ -o $@ $(CXXFLAGS)  $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem
	mv qe-cmap-pm-seq bin


table-sst: $(OBJS10)
	g++ -o $@ $(CXXFLAGS)  $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem
	mv table-sst bin


qe-table-sst: $(OBJS11)
	g++ -o $@ $(CXXFLAGS)  $(LDFLAGS) $^ -ldb -lpthread -lpmemkv -lpmem
	mv qe-table-sst bin

.PHONY: clean
clean:
	rm -f pedsort queryEval primes.C $(OBJS) $(OBJS1)

