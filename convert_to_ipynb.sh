
## Convert the references to formatted text with haskell-citeproc
pandoc groebner-bases-report.tex \
    --bibliography=ref.bib --csl=~/Templates/CSL/nature.csl  --citeproc --standalone \
    -o groebner-bases.ipynb

## OR Just use markdown
pandoc groebner-bases-report.tex        \
    --bibliography=ref.bib --standalone \
    -f latex -t markdown+raw_tex        \
    -o groebner-bases.md

    ## Append the bibtex file
    echo '```bibtex' >> groebner-bases.md
    cat ref.bib      >> groebner-bases.md
    echo '```'       >> groebner-bases.md

