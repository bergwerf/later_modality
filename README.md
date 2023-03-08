A Complete Proof System for the Later Modality
==============================================

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.6347180.svg)](https://doi.org/10.5281/zenodo.6347180)

The aim of this project is to formalize propositional logic with the *later*
modality. This modality is used by the *Iris* framework ([1]) as a technique to
prove properties of recursive programs ([2]), which is also called guarded
recursion ([3]). We introduce a new axiom to prove completeness:

*For all formulas P and Q, either P implies Q, or later Q implies P.*

Verify
------
```
coq_makefile -f _CoqProject -o CoqMakefile
make -f CoqMakefile
```

[1]: https://iris-project.org/
[2]: https://iris-project.org/tutorial-pdfs/lecture7-later.pdf
[3]: https://ncatlab.org/nlab/show/guarded+recursion
