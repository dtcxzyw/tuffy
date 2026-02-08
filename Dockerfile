from mcr.microsoft.com/devcontainers/rust:latest

RUN apt-get update && export DEBIAN_FRONTEND=noninteractive \
    && apt-get -y install --no-install-recommends \
       build-essential \
       cmake \
       ninja-build \
       gdb \
       gdbserver \
       vim \
       tmux \
       curl \
       coreutils

# Install elan (Lean 4 toolchain manager)
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:${PATH}"
