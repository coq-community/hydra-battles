all:    project pdf vo doc


pdf:
	(cd doc; make)

vo:
	(cd src; make -f CoqMakefile all)

clean:
	(cd src ; make -f CoqMakefile clean)

project: 
	(cd src ; source make_make)

doc:	html pdf

html:
	(cd src ; mkdir -p html; coqdoc -R . hydras -g -d html -utf8 -toc */*.v)


