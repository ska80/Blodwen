PREFIX = ${HOME}/.blodwen
export BLODWEN_PATH = ${CURDIR}/prelude/build:${CURDIR}/base/build
export BLODWEN_DATA = ${CURDIR}/support

.PHONY: ttimp blodwen prelude test base clean lib_clean

all: ttimp blodwen prelude base test

ttimp:
	idris --build ttimp.ipkg

blodwen: src/BlodwenPaths.idr
	idris --build blodwen.ipkg

src/BlodwenPaths.idr:
	echo 'module BlodwenPaths; export bprefix : String; bprefix = "${PREFIX}"' > src/BlodwenPaths.idr

prelude:
	make -C prelude BLODWEN=../blodwen

base: prelude
	make -C base BLODWEN=../blodwen

libs : prelude base

clean: lib_clean
	make -C src clean
	make -C tests clean
	rm -f blodwen
	rm -f runtests
	rm -f ttimp

lib_clean:
	make -C prelude clean
	make -C base clean

test:
	idris --build test.ipkg
	make -C tests

install:
	mkdir -p ${PREFIX}/bin
	mkdir -p ${PREFIX}/blodwen/support/chez
	mkdir -p ${PREFIX}/blodwen/support/chicken
	mkdir -p ${PREFIX}/blodwen/support/racket
	mkdir -p ${PREFIX}/blodwen/support/lispworks
	make -C prelude install BLODWEN=../blodwen
	make -C base install BLODWEN=../blodwen

	install --mode 755 blodwen ${PREFIX}/bin
	install --mode 644 support/chez/* ${PREFIX}/blodwen/support/chez
	install --mode 644 support/chicken/* ${PREFIX}/blodwen/support/chicken
	install --mode 644 support/racket/* ${PREFIX}/blodwen/support/racket
	install --mode 644 support/lispworks/* ${PREFIX}/blodwen/support/lispworks
