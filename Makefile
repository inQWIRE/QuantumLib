all: Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile

clean:
	rm -f CoqMakefile CoqMakefile.conf .*.aux *.vo* *.glob