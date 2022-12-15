FROM rustlang/rust:nightly AS builder

RUN rustup target add x86_64-unknown-linux-musl
RUN apt-get -y -q update  && \
    apt-get -y -q upgrade  && \
    apt-get -y -q install make \
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
            build-essential \
            pkgconf

RUN update-ca-certificates
RUN ln -s /bin/g++ /bin/musl-g++

WORKDIR /usr/src/purplecoin

COPY . .

RUN cargo +nightly build --release --no-default-features --features "rpc wallet disk miner blake3sum" --target x86_64-unknown-linux-musl
RUN rm -rf /usr/src/purplecoin

FROM scratch

ENV RUST_LOG purplecoin

WORKDIR /purplecoin

# Copy our build
COPY --from=builder /purplecoin/target/x86_64-unknown-linux-musl/release/purplecoin ./

# Use an unprivileged user.
USER purplecoin:purplecoin

CMD ["/purplecoin/purplecoin"]
