default:
	bibtex HWThesis
	makeglossaries HWThesis
	pdflatex HWThesis.tex
	pdflatex HWThesis.tex
	
	#pdflatex firstyearr.tex
	#pdflatex firstyearr.tex

clean:
	rm *~ *.pdf *.aux *.toc
