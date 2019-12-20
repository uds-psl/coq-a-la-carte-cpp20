all:
	cd metacoq && ./configure.sh local && make checker -j 8
	cd coq && make -j 8
