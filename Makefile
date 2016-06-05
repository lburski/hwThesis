default:
	pdflatex HWThesis.tex
	bibtex HWThesis
	makeglossaries HWThesis
	pdflatex HWThesis.tex
	pdflatex HWThesis.tex
clean:
	rm -f *~ *.aux *.toc *.log *.lot *.dvi *.acn *.ist
