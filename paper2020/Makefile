all: paper.pdf

UNAME_S := $(shell uname -s)

default: paper.pdf
ifeq ($(UNAME_S),Linux)
	gio open $<
else
	open $<
endif

paper.pdf: paper.tex ../PaperTools/bibtex/jp.bib
	nix-shell --pure --run "latexmk paper -pdf"

# %.tex: %.lhs  Suite.tex
# 	nix-shell --pure --run "lhs2TeX -o $@ $<"

../PaperTools/bibtex/jp.bib:
	git submodule update --init

clean:
	rm -f *.aux *.pdf *.bbl *.blg *.bcf Suite.tex Suite.hs

