FROM ubuntu:latest

RUN apt-get update \
    && apt-get install -y clang-15 libc++-15-dev curl git unzip sudo \
    && apt-get clean

RUN useradd --create-home --shell /bin/bash lean
USER lean
WORKDIR /home/lean

RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
RUN mkdir -p "$HOME/.local/bin" \
    && curl https://github.com/HanielB/cvc5/releases/download/leanPrinter-v0.0.4/cvc5-Linux-2023-03-10-f9e30de2dd -L > "$HOME/.local/bin/cvc5" \
    && chmod +x "$HOME/.local/bin/cvc5"
RUN echo "export PATH="$HOME/.elan/bin:$PATH"" >> "$HOME/.bashrc"

# ENV PATH="/home/lean/.elan/bin:${PATH}"
# RUN lake update