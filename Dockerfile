FROM ubuntu:24.04
SHELL ["/bin/bash", "-o", "pipefail", "-c"]
WORKDIR /root

RUN apt-get update && \
    DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
      ca-certificates curl git unzip clang lld libc++-dev libc++abi-dev && \
    rm -rf /var/lib/apt/lists/*

RUN curl -fsSL https://raw.githubusercontent.com/nvm-sh/nvm/v0.40.7/install.sh | bash
RUN . "$HOME/.nvm/nvm.sh" && nvm install 24
RUN curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | \
    sh -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:${PATH}"

WORKDIR /root/veil
COPY . .
RUN . "$HOME/.nvm/nvm.sh" && lake exe cache get && lake build
CMD ["bash"]
