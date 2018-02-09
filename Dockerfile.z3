# TODO: clean-up after apt-get commands
#       see: https://docs.docker.com/engine/userguide/eng-image/dockerfile_best-practices/
#
# SOSRepair requires two different versions of LLVM/Clang:
#
# * SOSRepair itself uses the "latest" version of Clang (TODO: fix this to a particular version)
# * KLEE, a dependency of SOSRepair, requires LLVM/Clang 3.4
#
#
FROM ubuntu:14.04
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
RUN apt-get install -y patchelf
ENV CXX=g++

###############################################################################
# Z3
###############################################################################
ENV Z3_REV ce123d9dbcc1b5902bf831c4730e5628387c79dc
RUN git clone https://github.com/Z3Prover/z3.git /tmp/z3 && \
    cd /tmp/z3 && \
    git checkout "${Z3_REV}" && \
    python scripts/mk_make.py && \
    cd build && \
    make -j$(nproc) && \
    make install PREFIX=/opt/sosrepair && \
    rm -rf /tmp/*

###############################################################################
# Clang 3.4.2
###############################################################################
RUN cd /tmp && \
    wget -nv http://releases.llvm.org/3.4.2/clang+llvm-3.4.2-x86_64-linux-gnu-ubuntu-14.04.xz && \
    tar -xf clang+llvm-3.4.2-x86_64-linux-gnu-ubuntu-14.04.tar.xz && \
    cd clang+llvm-3.4.2-x86_64-linux-gnu-ubuntu-14.04
RUN mkdir -p /opt/sosrepair/libexec && \
    mkdir -p /opt/sosrepair/share
RUN cd /tmp/clang* && \
    mv bin/* /opt/sosrepair/bin && \
    mv include/* /opt/sosrepair/include && \
    mv lib/* /opt/sosrepair/lib && \
    mv libexec/* /opt/sosrepair/libexec && \
    mv share/* /opt/sosrepair/share && \
    rm -rf /tmp/*

###############################################################################
# uclibc
###############################################################################
# WARNING: this isn't fixed to a particular version!
# TODO: this is hanging on to more than it ought to
RUN mkdir -p /opt/sosrepair
RUN apt-get install -y  libcap-dev \
	                libncurses5-dev \
                        python-minimal \
                        python-pip \
                        groff \
                        libboost-all-dev \
                        zlib1g-dev
RUN git clone https://github.com/klee/klee-uclibc.git /tmp/uclibc && \
    cd /tmp/uclibc && \
    ./configure --with-llvm-config /opt/sosrepair/bin/llvm-config \
                --make-llvm-lib && \
    make -j && \
    make install PREFIX=/opt/sosrepair && \
    rm -rf /tmp/*

###############################################################################
# minisat
###############################################################################
# WARNING: this isn't fixed to a particular version!
ENV MINISAT_REV 37dc6c67e2af26379d88ce349eb9c4c6160e8543
RUN git clone https://github.com/stp/minisat.git /tmp/minisat && \
    cd /tmp/minisat && \
    git checkout "${MINISAT_REV}" && \
    mkdir build && \
    cd build && \
    cmake -DSTATIC_BINARIES=ON -DCMAKE_INSTALL_PREFIX=/opt/sosrepair ../ && \
    make -j install && \
    cd / && \
    rm -rf /tmp/*

###############################################################################
# stp
###############################################################################
RUN cd /tmp && \
    wget --quiet https://github.com/stp/stp/archive/2.1.2.tar.gz && \
    tar -xf 2.1.2.tar.gz && \
    cd stp* && \
    mkdir build && \
    cd build && \
    cmake -DSTATIC_BINARIES=ON \
          -DBUILD_SHARED_LIBS:BOOL=OFF \
          -DENABLE_PYTHON_INTERFACE:BOOL=OFF \
          -DCMAKE_INSTALL_PREFIX=/opt/sosrepair .. && \
    make -j && \
    make install && \
    ulimit -s unlimited && \
    rm -rf /tmp/*

###############################################################################
# KLEE
###############################################################################
RUN git clone https://github.com/klee/klee.git /tmp/klee && \
    cd /tmp/klee && \
    git checkout v1.4.0
RUN cd /tmp/klee && \
    PATH="/opt/sosrepair/bin:${PATH}" ./configure prefix=/opt/sosrepair \
      --with-stp=/opt/sosrepair/bin/stp \
      --with-uclibc=/opt/sosrepair/bin/uclibc \
      --enable-posix-runtime \
      LDFLAGS=-L$/opt/sosrepair/lib \
      CPPFLAGS=-I/opt/sosrepair/include && \
    make install -j$(nproc) && \
    cd / && \
    rm -rf /tmp/*

# # TODO: mechanize this!
# # RUN mkdir "${Z3_LOCATION}/lib64" && \
# #     cp -r /lib/x86_64-linux-gnu/* "${Z3_LOCATION}/lib" && \
# #     cp -r /usr/lib/x86_64-linux-gnu/* "${Z3_LOCATION}/lib" && \
# #     cp -r /lib64/* "${Z3_LOCATION}/lib64" && \
# #     patchelf --set-rpath "${Z3_LOCATION}/lib" "${Z3_LOCATION}/bin/z3" && \
# #     patchelf --set-interpreter "${Z3_LOCATION}/lib/ld-2.23.so" "${Z3_LOCATION}/bin/z3"
# # VOLUME "${Z3_LOCATION}"
