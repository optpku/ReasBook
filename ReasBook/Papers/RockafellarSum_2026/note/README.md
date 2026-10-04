# Mathematical source note

The Lean formalization is based on *Technical note: a counterexample to the
Rockafellar sum conjecture on c₀*.

**Authors:** Junyu Zhang, Jinbiao Chen, Zichen Wang, Benqi Liu, and Zaiwen Wen.

The note discloses that Junyu Zhang and Jinbiao Chen developed it with the
assistance of GPT-5.6.

- [Read the PDF](rockafellar_sum_technical_note.pdf).
- [LaTeX source](rockafellar_sum_technical_note.tex), based on the supplied v3 manuscript.
- [Bibliography](references.bib).

The note develops the monotone seed construction underlying the formalization.
The final Lean declaration is `C0Seq.exists_maximalMonotone_sum_not_maximal`;
`Lorentz.exists_seedCounterexample` retains the radius-12 normal-cone witness.

Build locally with pdfLaTeX and BibTeX through latexmk:

```sh
cd note
latexmk -pdf -interaction=nonstopmode -halt-on-error rockafellar_sum_technical_note.tex
```

The PDF is intentionally versioned as a reading copy. LaTeX intermediate files
are ignored. The mathematical text is preserved from the supplied manuscript;
the bibliography includes the Minty (1962) entry cited in its introduction.
