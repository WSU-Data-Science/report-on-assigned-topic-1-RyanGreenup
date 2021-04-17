
FILENAME="groebner-bases.md"

## OR Just use markdown
pandoc groebner-bases-report.tex        \
    --bibliography=ref.bib --standalone \
    -f latex -t markdown+raw_tex        \
    -o "${FILENAME}"

    ## Fix the Headings 
    sd '(^# .+) \{#.+\}$' '$1' "${FILENAME}"

    ## Superscript the References
    sd '(\[@.*\])' '<sup>  $1  </sup>' "${FILENAME}"

    ## Append the bibtex file
    echo '```bibtex' >> groebner-bases.md
    cat ref.bib      >> groebner-bases.md
    echo '```'       >> groebner-bases.md


## Convert the references to formatted text with haskell-citeproc
pandoc groebner-bases-report.tex \
    --bibliography=ref.bib --csl=$HOME/Templates/CSL/nature.csl  --citeproc --standalone \
    -o groebner-bases_citeproc.ipynb
