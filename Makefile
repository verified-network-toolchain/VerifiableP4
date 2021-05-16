.PHONY: all build install clean

all: build

build:
	dune build -p prod3

install:
	dune install -p prod3

clean:
	dune clean -p prod3
