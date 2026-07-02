MAIN=main
ROOT=$(abspath ..)
AGDATEX=/Users/thiemann/git/agdatex/agdatex.py
AGDATEX_SRCS=\
	$(ROOT)/Core/Types.agda \
	$(ROOT)/Core/PRFO.agda \
	$(ROOT)/Core/PRFOFold.agda \
	$(ROOT)/Core/PRHO.agda \
	$(ROOT)/Core/Equations/PRFO.agda \
	$(ROOT)/Core/Models/Setoids/PRFO.agda

.PHONY: all agda-snippets clean

all: agda-snippets
	latexmk -pdf $(MAIN).tex

agda-snippets:
	$(AGDATEX) -r $(ROOT) -o $(abspath .) -e $(abspath agda-generated.tex) $(AGDATEX_SRCS)

clean:
	latexmk -C $(MAIN).tex
