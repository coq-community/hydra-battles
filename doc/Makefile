DEP_FILES = hydras.tex          \
	    part-hydras.tex     \
	    chapter-powers.tex  \
	    chapter-primrec.tex \
	    gaia-chapter.tex    \
	    thebib.bib          \
	    coqmacros.tex       \
	    epsilon0.jpg        \
	tuto.tex

.PHONY:all
all: hydras.pdf

hydras.pdf: ${DEP_FILES}
	@+${MAKE} -C movies all
	lualatex hydras.tex
	bibtex hydras
	lualatex hydras.tex
	makeindex gaiabridge
	makeindex coq
	makeindex maths
	makeindex hydras
	makeindex primrec
	makeindex additions
	lualatex hydras.tex
	lualatex hydras.tex

.PHONY:clean
clean:
	@+${MAKE} -C movies clean
	@${RM} hydras.pdf *.aux *.ind *.idx *.idl *.ilg *.bbl *.log *.toc *.out
