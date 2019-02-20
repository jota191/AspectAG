
TEX = pdflatex -shell-escape -interaction=nonstopmode -file-line-error
LHS2TEX = lhs2TeX
REPORTE = Main

.PHONY: all view

all : pdf view

view : Main.tex
	evince Main.pdf&

pdf : Main.lhs
	$(LHS2TEX) --verb $(REPORTE).lhs > $(REPORTE).tex
	$(TEX) $(REPORTE).tex
	pdflatex $(REPORTE).tex
	bibtex $(REPORTE)
	pdflatex $(REPORTE).tex
	cp Main.pdf ../Doc.pdf
	cp Main.pdf ../dist/doc/html/AspectAG/AAG-Reporte.pdf


.PHONY: clean
clean:
	rm -f *.log *.aux *~ *.pdf *bbl
