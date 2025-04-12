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

COPY ./Benchmarks/Veil/Blockchain.lean /root/veil/Benchmarks/Veil/Blockchain.lean
RUN lake build Benchmarks.Veil.Blockchain

COPY ./Benchmarks/Veil/ChordRingMaintenance.lean /root/veil/Benchmarks/Veil/ChordRingMaintenance.lean
RUN lake build Benchmarks.Veil.ChordRingMaintenance

COPY ./Benchmarks/Veil/DecentralizedLock.lean /root/veil/Benchmarks/Veil/DecentralizedLock.lean
RUN lake build Benchmarks.Veil.DecentralizedLock

COPY ./Benchmarks/Veil/MultiSigAll.lean /root/veil/Benchmarks/Veil/MultiSigAll.lean
RUN lake build Benchmarks.Veil.MultiSigAll

COPY ./Benchmarks/Veil/MultiSigMajority.lean /root/veil/Benchmarks/Veil/MultiSigMajority.lean
RUN lake build Benchmarks.Veil.MultiSigMajority

COPY ./Benchmarks/Veil/PaxosEPR.lean /root/veil/Benchmarks/Veil/PaxosEPR.lean
RUN lake build Benchmarks.Veil.PaxosEPR

COPY ./Benchmarks/Veil/PaxosFirstOrder.lean /root/veil/Benchmarks/Veil/PaxosFirstOrder.lean
RUN lake build Benchmarks.Veil.PaxosFirstOrder

COPY ./Benchmarks/Veil/Rabia.lean /root/veil/Benchmarks/Veil/Rabia.lean
RUN lake build Benchmarks.Veil.Rabia

COPY ./Benchmarks/Veil/ReliableBroadcast.lean /root/veil/Benchmarks/Veil/ReliableBroadcast.lean
RUN lake build Benchmarks.Veil.ReliableBroadcast

COPY ./Benchmarks/Veil/RicartAgrawala.lean /root/veil/Benchmarks/Veil/RicartAgrawala.lean
RUN lake build Benchmarks.Veil.RicartAgrawala

COPY ./Benchmarks/Veil/Ring.lean /root/veil/Benchmarks/Veil/Ring.lean
RUN lake build Benchmarks.Veil.Ring

COPY ./Benchmarks/Veil/SCPTheory.lean /root/veil/Benchmarks/Veil/SCPTheory.lean
RUN lake build Benchmarks.Veil.SCPTheory

COPY ./Benchmarks/Veil/SCP.lean /root/veil/Benchmarks/Veil/SCP.lean
RUN lake build Benchmarks.Veil.SCP

COPY ./Benchmarks/Veil/SuzukiKasami.lean /root/veil/Benchmarks/Veil/SuzukiKasami.lean
RUN lake build Benchmarks.Veil.SuzukiKasami

COPY ./Benchmarks/Veil/SuzukiKasamiInts.lean /root/veil/Benchmarks/Veil/SuzukiKasamiInts.lean
RUN lake build Benchmarks.Veil.SuzukiKasamiInts

COPY ./Benchmarks/Veil/TwoPhaseCommit.lean /root/veil/Benchmarks/Veil/TwoPhaseCommit.lean
RUN lake build Benchmarks.Veil.TwoPhaseCommit

COPY ./Benchmarks/Veil/VerticalPaxosFirstOrder.lean /root/veil/Benchmarks/Veil/VerticalPaxosFirstOrder.lean
RUN lake build Benchmarks.Veil.VerticalPaxosFirstOrder

COPY ./Benchmarks/Veil/RabiaMore.lean /root/veil/Benchmarks/Veil/RabiaMore.lean
RUN lake build Benchmarks.Veil.RabiaMore

COPY ./Benchmarks/Ivy /root/veil/Benchmarks/Ivy

COPY ./Tutorial /root/veil/Tutorial
RUN lake lean Tutorial/Ring.lean

COPY ./*.sh /root/veil/
COPY ./scripts /root/veil/scripts
COPY ./logs /root/veil/logs
COPY ./README_artifact.md /root/veil/README.md
COPY ./README.md /root/veil/Veil_README.md
