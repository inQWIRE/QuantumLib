all:
	@dune build

clean:
	@dune clean

install:
	@dune install

uninstall:
	@dune uninstall

# hacky :) we should replace with dune in a future version
FILES=$(shell find . -name "*.v" -depth 1) 
doc: all
	mkdir -p docs
	cd _build/default && coqdoc -g --utf8 --toc --no-lib-name -d ../../docs -R . QuantumLib $(FILES)

.PHONY: all clean install uninstall doc
