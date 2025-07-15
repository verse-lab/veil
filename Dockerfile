FROM mcr.microsoft.com/devcontainers/base:noble

ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update -y && \
    apt-get install -y software-properties-common build-essential curl unzip git \
    clang lld libc++-dev libc++abi-dev && \
    apt-get clean
# RUN update-alternatives --install /usr/bin/cc cc /usr/bin/clang 100

USER vscode
WORKDIR /home/vscode

RUN bash -c 'curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain leanprover/lean4:4.20.0'
ENV PATH="/home/vscode/.elan/bin:${PATH}"