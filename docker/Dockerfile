# TODO: clean-up after apt-get commands
#       see: https://docs.docker.com/engine/userguide/eng-image/dockerfile_best-practices/
#
# SOSRepair requires two different versions of LLVM/Clang:
#
# * SOSRepair itself uses the "latest" version of Clang (TODO: fix this to a particular version)
# * KLEE, a dependency of SOSRepair, requires LLVM/Clang 3.4
#
#
FROM ubuntu:16.04
MAINTAINER Afsoon Afzal (afsoona@cs.cmu.edu)

# Install basic dependencies
# - we install binutils-gold to speed up compilation
# TODO: install Ninja
RUN apt-get update && \
    apt-get install -y  subversion \
                        vim \
                        git \
                        g++ \
                        python \
                        perl \
                        cmake \
                        unzip \
                        wget \
                        curl \
                        build-essential \
                        bison \
                        flex \
                        binutils-gold
ENV CXX=g++

# Download LLVM source code
ENV LLVM_LOCATION /opt/llvm
RUN mkdir -p /opt/llvm && cd /opt/llvm && \
	  svn co http://llvm.org/svn/llvm-project/llvm/trunk llvm && \
	  mkdir build

# Download Clang source code
ENV CLANG_LOCATION /opt/llvm/tools/clang
RUN cd /opt/llvm/llvm/tools && \
    svn co http://llvm.org/svn/llvm-project/cfe/trunk clang

# Apply a patch to the Clang source code
ADD 0001-Binary-operation.patch /opt/llvm/llvm/tools/clang
RUN cd /opt/llvm/llvm/tools/clang && \
    cat 0001-Binary-operation.patch | patch -p0 && \
    rm 0001-Binary-operation.patch

# Compile LLVM ... wait, this doesn't build?
RUN cd /opt/llvm/build && \
    cmake -G "Unix Makefiles" ../llvm

# Install KLEE dependencies
# TODO: if these are run-time dependencies, this could be a problem
RUN apt-get install -y  libcap-dev \
	                      libncurses5-dev \
                        python-minimal \
                        python-pip \
                        groff \
                        libboost-all-dev \
                        zlib1g-dev

# Download a different version of LLVM/Clang for use with KLEE
ENV KLEE_LOCATION /opt/klee
RUN mkdir -p "${KLEE_LOCATION}" && \
    git clone https://github.com/llvm-mirror/llvm.git "${KLEE_LOCATION}/llvm" && \
	  cd "${KLEE_LOCATION}/llvm" && \
    git checkout release_34 && \
    mkdir build && \
    cd tools && \
	  git clone https://github.com/llvm-mirror/clang.git && \
    cd clang && \
    git checkout release_34 && \
	  cd ../../build && \
    ../configure --enable-optimized --prefix="${KLEE_LOCATION}" && \
    make -j4 && \
    make install && \
    cd / && \
    rm -rf /tmp/*

# Install minisat
# WARNING: this isn't fixed to a particular version!
RUN git clone https://github.com/stp/minisat.git /tmp/minisat && \
    cd /tmp/minisat && \
	  mkdir build && \
    cd build && \
    cmake -DSTATIC_BINARIES=ON -DCMAKE_INSTALL_PREFIX="${KLEE_LOCATION}" ../ && \ 
	  make -j install && \
    cd / && \
    rm -rf /tmp/*

# Install stp
RUN cd "${KLEE_LOCATION}" && \
    wget --quiet https://github.com/stp/stp/archive/2.1.2.tar.gz && \
    tar -xf 2.1.2.tar.gz && \
    rm 2.1.2.tar.gz && \
    mv stp-2.1.2 stp && \
    cd stp && \ 
    mkdir build && \
    cd build && \
	  cmake -DSTATIC_BINARIES=ON \
          -DBUILD_SHARED_LIBS:BOOL=OFF \
          -DENABLE_PYTHON_INTERFACE:BOOL=OFF \
          -DCMAKE_INSTALL_PREFIX="${KLEE_LOCATION}" .. && \
    make -j && \
    make install && \
    ulimit -s unlimited && \
    rm -rf /tmp/*

# Install uclibc
# WARNING: this isn't fixed to a particular version!
# TODO: this is hanging on to more than it ought to
RUN git clone https://github.com/klee/klee-uclibc.git "${KLEE_LOCATION}/uclibc" && \
	  cd "${KLEE_LOCATION}/uclibc" && \
    ./configure --with-llvm-config "${KLEE_LOCATION}/bin/llvm-config" \
                --make-llvm-lib && \
    make -j && \
    rm -rf .git

# Install KLEE
#
# TODO: this is a problem! We're going to end up adding two versions of LLVM to
#       the PATH
ENV PATH="${KLEE_LOCATION}/bin:${PATH}"
RUN git clone https://github.com/klee/klee.git /tmp/klee && \
    cd /tmp/klee && \
	  ./configure prefix="${KLEE_LOCATION}" \
                --with-stp="${KLEE_LOCATION}/stp" \
                --with-uclibc="${KLEE_LOCATION}/uclibc" \
                --enable-posix-runtime \
                LDFLAGS="-L${KLEE_LOCATION}/lib" \
                CPPFLAGS="-I${KLEE_LOCATION}/include" && \
	  make -j
#    make install
#ENV PATH="/opt/KLEE/KLEE/Release+Asserts/bin:${PATH}"
#
## Install Z3 from source
## TODO: discard everything except the Z3 executable
##       alternatively, "make install" to /opt/z3
#ENV Z3_LOCATION /opt/z3
#    git clone https://github.com/Z3Prover/z3.git /opt/z3 &&
#    cd /opt/z3 && \
#	  python scripts/mk_make.py && \
#    cd build && \
#	  make -j
#
## Install postgres
## TODO: this breaks portability
#RUN apt-get install -y postgresql
#USER postgres
#RUN  /etc/init.d/postgresql start && \
#    psql --command "CREATE USER afsoon WITH SUPERUSER PASSWORD 'aa';" &&\
#    createdb -O afsoon testdb
#USER root
#
## Install SOS dependencies
##
## TODO: what are these SSH keys being used for?
#RUN pip install --upgrade pip && \
#    pip install ipython==5.3.0 && \
#	  pip install postgres && ssh-keygen -t rsa -N "" -f /root/.ssh/id_rsa
#ADD ssh /root/.ssh
#
## Install SOS
#ENV SOS_LOCATION /opt/sos
#RUN git clone git@bitbucket.org:afsafzal/searchrepair.git /opt/sos && \
#	  cd /opt/sos && \
#    git checkout FSE17
#ENV PYTHONPATH="/opt/llvm/llvm/tools/clang/bindings/python:${PYTHONPATH}"
#
## Add an entrypoint script responsible for starting up postgres upon launch
#RUN mkdir -p /entrypoint/sos
#ADD entrypoint.sh /entrypoint/sos/entrypoint.sh
#ENTRYPOINT /entrypoint/sos/entrypoint.sh
