all:
	@dune build

clean:
	@dune clean

install:
	@dune install

uninstall:
	@dune uninstall

.PHONY: all clean install uninstall
