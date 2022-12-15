FROM messense/rust-musl-cross:x86_64-musl as builder

ARG OPENSSL_VERSION=1.1.1m
ARG ZLIB_VERSION=1.2.13

RUN rustup update nightly && \
    rustup target add --toolchain nightly x86_64-unknown-linux-musl

RUN apt-get -y -qq update  && \
    apt-get -y -qq upgrade  && \
    apt-get -y -qq install make \
            g++ \
            m4 \
            cmake \
            clang \
            libclang-dev \
            llvm \
            llvm-dev \
            musl \
            musl-dev \
            musl-tools \
            xutils-dev \
            autoconf \
            autoconf-archive \
            automake \
            libc-dev \
            linux-libc-dev \
            build-essential \
            pkgconf

# Build a static library version of OpenSSL using musl-libc.  This is needed by
# the popular Rust `hyper` crate.
#
# We point /usr/local/musl/include/linux at some Linux kernel headers (not
# necessarily the right ones) in an effort to compile OpenSSL 1.1's "engine"
# component. It's possible that this will cause bizarre and terrible things to
# happen. There may be "sanitized" header
RUN echo "Building OpenSSL" && \
    ls /usr/include/linux && \
    mkdir -p /usr/local/musl/include && \
    ln -s /usr/include/linux /usr/local/musl/include/linux && \
    ln -s /usr/include/x86_64-linux-gnu/asm /usr/local/musl/include/asm && \
    ln -s /usr/include/asm-generic /usr/local/musl/include/asm-generic && \
    cd /tmp && \
    short_version="$(echo "$OPENSSL_VERSION" | sed s'/[a-z]$//' )" && \
    curl -fLO "https://www.openssl.org/source/openssl-$OPENSSL_VERSION.tar.gz" || \
        curl -fLO "https://www.openssl.org/source/old/$short_version/openssl-$OPENSSL_VERSION.tar.gz" && \
    tar xvzf "openssl-$OPENSSL_VERSION.tar.gz" && cd "openssl-$OPENSSL_VERSION" && \
    env CC=musl-gcc ./Configure no-shared no-zlib -fPIC --prefix=/usr/local/musl -DOPENSSL_NO_SECURE_MEMORY linux-x86_64 && \
    env C_INCLUDE_PATH=/usr/local/musl/include/ make depend && \
    env C_INCLUDE_PATH=/usr/local/musl/include/ make && \
    make install && \
    rm /usr/local/musl/include/linux /usr/local/musl/include/asm /usr/local/musl/include/asm-generic && \
    rm -r /tmp/*

RUN echo "Building zlib" && \
    cd /tmp && \
    curl -fLO "http://zlib.net/zlib-$ZLIB_VERSION.tar.gz" && \
    tar xzf "zlib-$ZLIB_VERSION.tar.gz" && cd "zlib-$ZLIB_VERSION" && \
    CC=musl-gcc ./configure --static --prefix=/usr/local/musl && \
    make && make install && \
    rm -r /tmp/*

WORKDIR /usr/src/purplecoin

COPY . .
RUN cargo +nightly build --release --no-default-features --features "rpc wallet disk miner blake3sum" --target x86_64-unknown-linux-musl

FROM scratch

ENV RUST_LOG=purplecoin

# Network settings
ENV PURPLECOIN_NETWORK_LISTENADDR=
ENV PURPLECOIN_NETWORK_LISTENPORTMAINNET=8098
ENV PURPLECOIN_NETWORK_LISTENPORTTESTNET=8031
ENV PURPLECOIN_NETWORK_RPCENABLED=
ENV PURPLECOIN_NETWORK_RPCLISTENPORTMAINNET=8067
ENV PURPLECOIN_NETWORK_RPCLISTENPORTTESTNET=8037
ENV PURPLECOIN_NETWORK_RPCUSERNAME=
ENV PURPLECOIN_NETWORK_RPCPASSWORD=
ENV PURPLECOIN_NETWORK_SEEDSMAINNET=
ENV PURPLECOIN_NETWORK_SEEDSTESTNET=

# Node settings
ENV PURPLECOIN_NODE_NETWORKNAME=
ENV PURPLECOIN_NODE_VERIFIERTHREADS=
ENV PURPLECOIN_NODE_NETWORKTHREADS=
ENV PURPLECOIN_NODE_RANDOMXFASTMODE=
ENV PURPLECOIN_NODE_ARCHIVALMODE=
ENV PURPLECOIN_NODE_PRUNEHEADERS=
ENV PURPLECOIN_NODE_PRUNETRANSACTIONS=
ENV PURPLECOIN_NODE_PRUNEUTXOS=
ENV PURPLECOIN_NODE_DATADIR=
ENV PURPLECOIN_NODE_MEMORYONLY=
ENV PURPLECOIN_NODE_MEMPOOLSIZE=
ENV PURPLECOIN_NODE_DHTBRIDGEENABLED=
ENV PURPLECOIN_NODE_DHTBRIDGESTORAGEMB=
ENV PURPLECOIN_NODE_SAVEUTXOADDRESSES=
ENV PURPLECOIN_NODE_SAVEUTXOASSETS=
ENV PURPLECOIN_NODE_BRIDGEPUBLICQUERIES=
ENV PURPLECOIN_NODE_BRIDGEHTTPQUERIES=
ENV PURPLECOIN_NODE_BRIDGEHTTPLISTENPORT=8080
ENV PURPLECOIN_NODE_BRIDGEHTTPHMACKEY=

# Miner settings
ENV PURPLECOIN_MINER_ONLYSECTORS=
ENV PURPLECOIN_MINER_ONLYALGOS=
ENV PURPLECOIN_MINER_COINBASEADDRESS=
ENV PURPLECOIN_MINER_MINERTHREADS=

# Cluster settings
ENV PURPLECOIN_CLUSTER_CLUSTERENABLED=
ENV PURPLECOIN_CLUSTER_CLUSTERDISCOVERYPORT=3034
ENV PURPLECOIN_CLUSTER_CLUSTERDISCOVERYLISTENADDR=
ENV PURPLECOIN_CLUSTER_CLUSTERCOOKIE=
ENV PURPLECOIN_CLUSTER_VNODESPERSHARD=
ENV PURPLECOIN_CLUSTER_VNODESREPLICATIONFACTOR=
ENV PURPLECOIN_CLUSTER_BLOCKWRITES=
ENV PURPLECOIN_CLUSTER_REPLICATIONMODE=
ENV PURPLECOIN_CLUSTER_REPLICATIONDATACENTER=
ENV PURPLECOIN_CLUSTER_CLUSTERIPS=

# Expose ports
EXPOSE $PURPLECOIN_NETWORK_LISTENPORT/tcp
EXPOSE $PURPLECOIN_NETWORK_LISTENPORT/udp
EXPOSE $PURPLECOIN_NETWORK_RPCLISTENPORT/tcp
EXPOSE $PURPLECOIN_NETWORK_RPCLISTENPORT/udp
EXPOSE $PURPLECOIN_NODE_BRIDGEHTTPLISTENPORT/tcp
EXPOSE $PURPLECOIN_NODE_BRIDGEHTTPLISTENPORT/udp
EXPOSE $PURPLECOIN_CLUSTER_CLUSTERDISCOVERYPORT/tcp
EXPOSE $PURPLECOIN_CLUSTER_CLUSTERDISCOVERYPORT/udp

WORKDIR /purplecoin

# Copy our build
COPY --from=builder /usr/src/purplecoin/target/x86_64-unknown-linux-musl/release/purplecoin ./

# Use an unprivileged user.
USER purplecoin:purplecoin

CMD ["/purplecoin/purplecoin"]
