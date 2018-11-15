AGDA=agda
AFLAGS=-i. --latex --only-scope-checking
SOURCE=thesis
POSTPROCESS=postprocess-latex.pl
LATEX=latexmk -pdf -use-make -xelatex

all: build

build:
	$(AGDA) $(AFLAGS) $(SOURCE).lagda
	cd latex/ && \
	$(LATEX) $(SOURCE).tex && \
	mv $(SOURCE).pdf ..

watch:
	while inotifywait -e close_write thesis.lagda; do make; done

