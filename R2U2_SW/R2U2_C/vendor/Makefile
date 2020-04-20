all:
	mkdir -p ../target/vendor/CsvParser/
	gcc -c -I CsvParser/include/ CsvParser/src/csvparser.c -o ../target/vendor/CsvParser/csvparser.o
	mkdir -p ../target/vendor/lib
	ar rs ../target/vendor/lib/libcsv.a ../target/vendor/CsvParser/csvparser.o
	mkdir -p ../target/vendor/include
	cp CsvParser/include/csvparser.h ../target/vendor/include/csvparser.h

# clean files list
DISTCLEAN_LIST := ../target/vendor/

CLEAN_LIST := ../target/vendor/lib/libcsv.a \
			  ../target/vendor/include/csvparser.h \
			  $(DISTCLEAN_LIST)

.PHONY: clean
clean:
	@echo CLEAN $(CLEAN_LIST)
	@rm -rf $(CLEAN_LIST)

.PHONY: distclean
distclean:
	@echo DISTCLEAN $(DISTCLEAN_LIST)
	@rm -rf $(DISTCLEAN_LIST)