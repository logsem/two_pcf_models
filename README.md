# Two models of PCF in siProp/Iris

In this repository you can find two formalized models of PCF in a form
of "guarded type theory" provided by Iris.

The first model is the "typed" model, described in [2]. It interprests
every type as a certain pointed "guarded domain".

The second model is an "untyped" model, a-la Scott's model for untyped
λ-calculus. It interprets all types in the same "guarded domain".

The formalization is organized as follows:

- `lang.v` contains the syntax and operational semantics of PCF, using
  the well-typed representation as in [1].
- `typed/model.v` contains the interpretation of PCF in the "typed"
  model, with the lift functor, and `typed/logrel.v` contains the
  logical relation for proving adequacy of the model
- `untyped/model.v` contains the intepretation of PCF in the "untyped"
  model, with the guarded-recursive universal domain, and
  `untyped/logrel.v` contains the logical relation for adequacy
- `prelude.v` contains some material that has been missing from Iris

To compile the source code, make sure that you have Iris and std++ installed, and then run:
```
coq_makefile -f _CoqProject -o Makefile
make -j 2
```

[1]: "Strongly Typed Term Representations in Coq", N. Benton, C.-K. Hur, A. Kennedy, C. McBride, 2012
[2]: "A Model of PCF in Guarded Type Theory", M. Paviotti, R. Møgelberg, L. Birkedal, 2015
