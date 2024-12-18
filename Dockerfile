FROM ubuntu:24.04
WORKDIR /root

ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update -y && \
    apt-get install -y software-properties-common build-essential curl cvc5 unzip git && \
    add-apt-repository ppa:deadsnakes/ppa && apt-get update -y && \
    apt-get install -y python3.12 && \
    apt-get install -y python3-z3 python3-cvc5 python3-sexpdata && \
    apt-get clean

#RUN apt install -y python3-properties

RUN bash -c 'curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain leanprover/lean4:stable'

RUN mkdir veil
COPY veil.zip /root
RUN unzip veil.zip  && mv .veil.tmp/* veil && rm veil.zip


