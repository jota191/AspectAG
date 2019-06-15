
TEX = pdflatex -shell-escape -interaction=nonstopmode -file-line-error
LHS2TEX = ./lhs2TeX


.PHONY: all view

all : pdf

view : Main.tex
	evince Main.pdf&

pdf : Main.lhs myformat.fmt ExprPaper.lhs GenRecord.lhs bib.bib
	$(LHS2TEX) Main.lhs > Main.tex
	$(TEX) Main.tex
	pdflatex Main.tex
	bibtex Main
	pdflatex Main.tex


quotes : Main.tex
	perl -pe 's/'\''\[/\\tk \[/g' ./Main.tex | perl -pe 's/'\''\(/\\tk \(/g' | perl -pe 's/'\''\:/\\tk \\\! \\\!\:/g' > Main2.tex
	mv Main2.tex Main.tex
	pdflatex Main.tex

.PHONY: clean
clean:
	rm -f *.log *.aux *~ *.pdf *bbl
