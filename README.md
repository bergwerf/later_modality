The Logic of Delay
==================
The aim of this project is to formalize propositional logic with the later
modality. This modality is used by the Iris framework to prove properties of
recursive programs [1]. This technique is also called guarded recursion [2]. We
introduce a new axiom to prove completeness. This axiom states the following:
For all formulas P and Q, either P implies Q, or later Q implies P.

To build the files in this repository, use:
```
coq_makefile -f _CoqProject -o CoqMakefile
make -f CoqMakefile
```

[1]: https://iris-project.org/tutorial-pdfs/lecture7-later.pdf
[2]: https://ncatlab.org/nlab/show/guarded+recursion
