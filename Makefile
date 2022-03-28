.PHONY: help all clean

help:
	@echo "- make all  : build all the .vo files (under _build)"
	@echo "- make clean: clean the build tree"

all:
	dune build

install:
	dune install -p coq-vcg

clean:
	dune clean
