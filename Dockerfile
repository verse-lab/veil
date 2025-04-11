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

COPY ./Test /root/veil/Test
COPY ./Tutorial /root/veil/Tutorial
COPY ./Veil /root/veil/Veil
COPY ./dependencies.toml /root/veil/dependencies.toml
COPY ./lake-manifest.json /root/veil/lake-manifest.json
COPY ./lakefile.lean /root/veil/lakefile.lean
COPY ./lean-toolchain /root/veil/lean-toolchain
COPY ./LICENSE /root/veil/LICENSE
COPY ./Veil.lean /root/veil/Veil.lean

SHELL ["/bin/bash", "--login", "-c"]

WORKDIR /root/veil
RUN lake build

COPY ./lakefile.lean /root/veil/lakefile.lean
COPY ./Benchmarks /root/veil/Benchmarks
RUN lake build Benchmarks.Veil.Blockchain
RUN lake build Benchmarks.Veil.ChordRingMaintenance
RUN lake build Benchmarks.Veil.DecentralizedLock
RUN lake build Benchmarks.Veil.MultiSigAll
RUN lake build Benchmarks.Veil.MultiSigMajority
RUN lake build Benchmarks.Veil.PaxosEPR
RUN lake build Benchmarks.Veil.PaxosFirstOrder
RUN lake build Benchmarks.Veil.Rabia
RUN lake build Benchmarks.Veil.ReliableBroadcast
RUN lake build Benchmarks.Veil.RicartAgrawala
RUN lake build Benchmarks.Veil.Ring
RUN lake build Benchmarks.Veil.SCP
RUN lake build Benchmarks.Veil.SCPTheory
RUN lake build Benchmarks.Veil.SuzukiKasami
RUN lake build Benchmarks.Veil.SuzukiKasamiInts
RUN lake build Benchmarks.Veil.TwoPhaseCommit
RUN lake build Benchmarks.Veil.VerticalPaxosFirstOrder

RUN lake build Benchmarks.Veil.RabiaMore

COPY ./*.sh /root/veil/
COPY ./scripts /root/veil/scripts
COPY ./logs /root/veil/logs
COPY ./README_artifact.md ./root/veil/README.md
COPY ./README.md /root/veil/Veil_README.md
