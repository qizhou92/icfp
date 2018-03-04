FROM haskell:8

COPY src ./src
COPY app ./app
COPY package.yaml /
COPY stack.yaml /
COPY README.md /

ARG APT_MIRROR=deb.debian.org
RUN apt-get update
RUN apt-get install -y nginx git python-setuptools python-dev make

RUN git clone https://github.com/daheath/z3 z3
WORKDIR /z3
RUN python scripts/mk_make.py
WORKDIR /z3/build
RUN make && \
    make install
WORKDIR /
