FROM ubuntu:24.04
WORKDIR /root

ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update -y && \
    apt-get install -y software-properties-common build-essential curl unzip git cmake \
    python3 python3-pip python3-ply python3-pygraphviz python3-tk python3-matplotlib python3-numpy \
    tix pkg-config libssl-dev libreadline-dev sudo && \
    apt-get clean

RUN bash -c 'curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain leanprover/lean4:stable'

RUN git clone --recurse-submodules https://github.com/kenmcmil/ivy.git
WORKDIR /root/ivy
RUN apt-get install -y python-is-python3 && apt-get clean
RUN python3 build_submodules.py
RUN pip3 install . --break-system-packages
ENV PATH="/root/.local/bin:${PATH}"

WORKDIR /root
RUN mkdir veil
COPY . /root/veil

SHELL ["/bin/bash", "--login", "-c"]

WORKDIR /root/veil
# RUN lake clean && lake build