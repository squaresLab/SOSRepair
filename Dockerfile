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
                        flex
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
RUN echo "deb http://llvm.org/apt/trusty/ llvm-toolchain-trusty-3.4 main" >> /etc/apt/sources.list && \
    echo "deb-src http://llvm.org/apt/trusty/ llvm-toolchain-trusty-3.4 main" >> /etc/apt/sources.list && \
    wget -nv -O - http://llvm.org/apt/llvm-snapshot.gpg.key | apt-key add - && \
    apt-get update && \
    apt-get install -y clang-3.4 llvm-3.4 llvm-3.4-dev llvm-3.4-tools

###############################################################################
# uclibc
###############################################################################
# WARNING: this isn't fixed to a particular version!
RUN mkdir -p /opt/sosrepair
RUN apt-get install -y  libcap-dev \
	                libncurses5-dev \
                        python-minimal \
                        python-pip \
                        groff \
                        libboost-all-dev \
                        zlib1g-dev
RUN git clone https://github.com/klee/klee-uclibc.git /tmp/uclibc && \
    ls /usr/bin && \
    cd /tmp/uclibc && \
    ./configure --with-llvm-config /usr/bin/llvm-config-3.4 \
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
    ln -s /usr/bin/llvm-config-3.4 /usr/bin/llvm-config && \
    ./configure prefix=/opt/sosrepair \
      --with-stp=/opt/sosrepair \
      --with-uclibc=/opt/sosrepair/usr/x86_64-linux-uclibc/usr/ \
      --enable-posix-runtime \
      LDFLAGS=-L$/opt/sosrepair/lib \
      CPPFLAGS=-I/opt/sosrepair/include && \
    make install -j$(nproc) && \
    cd / && \
    rm -rf /tmp/*

###############################################################################
# patchelf
###############################################################################
RUN apt-get install -y autoconf && \
    cd /tmp && \
    wget -nv https://github.com/NixOS/patchelf/archive/0.9.tar.gz && \
    tar -xf 0.9.tar.gz && \
    cd patchelf-0.9 && \
    ./bootstrap.sh && \
    ./configure && \
    make install && \
    rm -rf /tmp/* && \
    apt-get remove -y autoconf

###############################################################################
# Customised Clang/LLVM installation
###############################################################################
#RUN apt-get install -y software-properties-common && \
#    add-apt-repository ppa:george-edison55/cmake-3.x
#RUN apt-get -y update
#RUN apt-get -y upgrade
ENV CMAKE_LOCATION /opt/cmake
RUN cd /tmp && wget "https://cmake.org/files/v3.10/cmake-3.10.2-Linux-x86_64.tar.gz" && \
    tar -xzvf "cmake-3.10.2-Linux-x86_64.tar.gz" && mv "cmake-3.10.2-Linux-x86_64" "${CMAKE_LOCATION}" 
RUN .$CMAKE_LOCATION/bin/cmake --version

ENV LLVM_LOCATION /opt/llvm
ADD docker/0001-Binary-operation.patch "/tmp/binary-op.patch"
RUN git clone https://git.llvm.org/git/llvm.git "${LLVM_LOCATION}" && \
    cd "${LLVM_LOCATION}" && mkdir build && \
    git checkout release_50 && \
    cd tools && git clone https://git.llvm.org/git/clang.git && \
    cd clang && git checkout release_50 && \
    cat "/tmp/binary-op.patch" | patch -p0
RUN cd "${LLVM_LOCATION}/build" && \
    ${CMAKE_LOCATION}/bin/cmake -G "Unix Makefiles" .. && \
    make -j8

ENV PYTHONPATH="${LLVM_LOCATION}/tools/clang/bindings/python:${PYTHONPATH}"

###############################################################################
# Uninstall build-time dependencies
###############################################################################




###############################################################################
# Create portable volume
###############################################################################
# ADD docker/port.py /port.py
# RUN ./port.py /opt/sosrepair /opt/sosrepair/bin/z3 && \
#     ./port.py /opt/sosrepair /opt/sosrepair/bin/minisat && \
#     ./port.py /opt/sosrepair /opt/sosrepair/bin/minisat_core && \
#     ./port.py /opt/sosrepair /opt/sosrepair/bin/stp-2.1.2 && \
#     ./port.py /opt/sosrepair /opt/sosrepair/bin/stp_simple && \
#     ./port.py /opt/sosrepair /opt/sosrepair/bin/kleaver \
#         libffi.so.6 libtinfo.so.5 libdl.so.2 && \
#     ./port.py /opt/sosrepair /opt/sosrepair/bin/klee \
#         libffi.so.6 libtinfo.so.5 libdl.so.2
# VOLUME /opt/sosrepair
