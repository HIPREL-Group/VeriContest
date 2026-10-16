# Official VeriContest evaluation image. Build from the repository root:
#   docker build -f evaluation/Dockerfile --build-arg VCEVAL_REVISION=$(git rev-parse HEAD) -t vericontest-eval .
FROM ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update \
 && apt-get install -y --no-install-recommends ca-certificates curl git build-essential python3 python3-pip \
 && rm -rf /var/lib/apt/lists/*

# Rust 1.94.0 is the toolchain the bundled Verus build expects.
ENV RUSTUP_HOME=/opt/rustup CARGO_HOME=/opt/cargo PATH=/opt/cargo/bin:$PATH
RUN curl -sSf https://sh.rustup.rs | sh -s -- -y --profile minimal --default-toolchain 1.94.0

WORKDIR /vericontest
COPY . /vericontest
RUN python3 -m pip install --no-cache-dir -r evaluation/requirements.txt \
 && evaluation/setup_tools.sh \
 && rm -rf evaluation/tools/src /opt/cargo/registry /opt/cargo/git

ARG VCEVAL_REVISION=""
ENV VCEVAL_REVISION=$VCEVAL_REVISION

# Submitted programs are untrusted: run with --network none, mounted outputs,
# and the test-case dataset mounted read-only (see evaluation/README.md).
ENTRYPOINT ["python3", "evaluation/score.py"]
