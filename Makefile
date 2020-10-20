all:    project pdf vo doc


pdf:
	(cd doc; make)

vo:
	(cd src; make  all)

clean:
	(cd src ; make clean)

project: 
	(cd src ; source make_project)

doc:	html pdf

html:
	(cd src ; mkdir -p html; coqdoc -R . hydras -g -d html -utf8 -toc */*.v)


