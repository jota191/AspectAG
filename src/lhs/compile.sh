rm Main.tex
touch Main.tex
lhs2TeX Main.lhs > Main.tex
pdflatex Main.tex
evince Main.pdf &
