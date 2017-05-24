FROM ubuntu:16.04
MAINTAINER Afsoon Afzal (afsoona@cs.cmu.edu)

RUN apt-get update && \
	apt-get install -y subversion vim git

# For llvm

RUN cd && mkdir llvm && cd llvm && \
	svn co http://llvm.org/svn/llvm-project/llvm/trunk llvm && \
	mkdir build

RUN cd ~/llvm/llvm/tools && \
	svn co http://llvm.org/svn/llvm-project/cfe/trunk clang
ADD 0001-Binary-operation.patch /root/llvm/llvm/tools/clang
RUN cd ~/llvm/llvm/tools/clang && cat 0001-Binary-operation.patch | patch -p0

RUN apt-get install -y g++ python cmake
#RUN add-apt-repository ppa:george-edison55/cmake-3.x && apt-get update && \
#	apt-get install -y cmake
ENV CXX=g++
RUN cd ~/llvm/build && cmake -G Unix\ Makefiles ../llvm

#For KLEE
RUN apt-get install -y build-essential curl libcap-dev \
	 libncurses5-dev python-minimal python-pip unzip wget \
	groff

RUN  mkdir ~/KLEE && cd ~/KLEE && git clone https://github.com/llvm-mirror/llvm.git && \
	cd llvm && git checkout release_34 && mkdir build && cd tools && \
	git clone https://github.com/llvm-mirror/clang.git && cd clang && git checkout release_34 && \
	cd ../../build && ../configure --enable-optimized && make -j4 && make install

RUN apt-get install -y bison flex libboost-all-dev perl zlib1g-dev

RUN cd ~/KLEE && git clone https://github.com/stp/minisat.git && cd minisat && \
	mkdir build && cd build && cmake -DSTATIC_BINARIES=ON -DCMAKE_INSTALL_PREFIX=/usr/ ../ && \ 
	make install && cd ../../ && git clone https://github.com/stp/stp.git && \
	cd stp && git checkout tags/2.1.2 && mkdir build && cd build && \
	cmake -DBUILD_SHARED_LIBS:BOOL=OFF -DENABLE_PYTHON_INTERFACE:BOOL=OFF .. && \
	make && make install && ulimit -s unlimited

RUN ln -sf /usr/bin/llvm-config-3.4 /usr/bin/llvm-config

RUN cd ~/KLEE && git clone https://github.com/klee/klee-uclibc.git && \
	cd klee-uclibc && ./configure --make-llvm-lib && make -j2

RUN cd ~/KLEE && git clone https://github.com/klee/klee.git && \ 
	cd klee && ./configure --with-stp=/root/KLEE/stp/build --with-uclibc=/root/KLEE/klee-uclibc --enable-posix-runtime && \
	make

ENV PATH="/root/KLEE/klee/Release+Asserts/bin:${PATH}"

# Z3 and Postgres

RUN cd && git clone https://github.com/Z3Prover/z3.git && cd z3 && \
	python scripts/mk_make.py && cd build && \
	make

RUN apt-get install -y postgresql

USER postgres

RUN  /etc/init.d/postgresql start && \
    psql --command "CREATE USER afsoon WITH SUPERUSER PASSWORD 'aa';" &&\
    createdb -O afsoon testdb

# For SOSRepair

USER root

RUN pip install --upgrade pip && pip install ipython==5.3.0 && \
	pip install postgres && ssh-keygen -t rsa -N "" -f /root/.ssh/id_rsa

ADD ssh/* /root/.ssh/

RUN cd && git clone git@bitbucket.org:afsafzal/searchrepair.git && \
	cd searchrepair && git checkout FSE17

ENV PYTHONPATH="/root/llvm/llvm/tools/clang/bindings/python:${PYTHONPATH}"

CMD /etc/init.d/postgresql start
