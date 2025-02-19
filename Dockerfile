FROM ubuntu:24.04
WORKDIR /root

ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update -y && \
    apt-get install -y software-properties-common build-essential curl unzip git z3 cvc5 && \
    apt-get clean

RUN bash -c 'curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain leanprover/lean4:stable'
RUN bash -c 'curl -LsSf https://astral.sh/uv/install.sh | sh'

RUN mkdir veil
COPY veil.zip /root
RUN unzip veil.zip  && mv .veil.tmp/* veil && rm veil.zip


