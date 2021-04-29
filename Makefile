default: quick

quick:
	pdflatex HOPE-sigplanned.tex

full:
	pdflatex HOPE-sigplanned.tex
	bibtex HOPE-sigplanned
	pdflatex HOPE-sigplanned.tex
	pdflatex HOPE-sigplanned.tex
