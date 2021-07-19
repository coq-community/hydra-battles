all:  hydras.pdf

DEP_FILES = hydras.tex          \
	    part-hydras.tex     \
	    chapter-powers.tex  \
	    chapter-primrec.tex \
	    thebib.bib          \
	    coqmacros.tex       \
	    epsilon0.jpg        \

hydras.pdf: ${DEP_FILES}
	@+${MAKE} -C movies all
	lualatex hydras.tex
	lualatex hydras.tex
	makeindex coq
	makeindex maths
	makeindex hydras
	makeindex primrec
	makeindex additions
	lualatex hydras.tex
	bibtex hydras
	lualatex hydras.tex

.PHONY:clean
clean:
	@+${MAKE} -C movies clean
