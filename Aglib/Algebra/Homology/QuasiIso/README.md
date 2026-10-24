# Quasi-isomorphisms and exact colimits

`Colimit` proves `HomologicalComplex.quasiIso_colimMap`: a natural
transformation of diagrams of native homological complexes induces a
quasi-isomorphism on their native colimits whenever every component is a
quasi-isomorphism. The hypotheses are `Abelian C`,
`HasColimitsOfShape J C`, and `HasExactColimitsOfShape J C`.
The diagram object and morphism universes, coefficient-category object and
morphism universes, and complex-shape universe remain independent. There is
no boundedness or filteredness assumption beyond the stated exact-colimit
hypothesis.

The proof forms only the complex of evaluated functors and its original
component map. It uses the native homology-preservation theorem for the exact
colimit functor, together with the original `coconeOfHasColimitEval` and its
canonical comparison with `colimit F`. The comparison retains the original
colimit injections and the original `colim.map` naturality equation. No new
colimit carrier, full functor-category equivalence, or duplicate acyclic-colimit
theorem is used as a replacement interface.

`Transfinite` is the downstream morphism-property wrapper. It transports the
native theorem to arbitrary colimit cocones and supplies filtered-colimit
stability in the stated Grothendieck universe. Its current consumer is the transfinite replacement
augmentation in `DerivedCategory/KInjective/Existence/Tower/QuasiIso`.
Neither this family nor a quasi-isomorphic augmentation alone proves that a
final complex is K-injective.

The sole compiler accepted `Colimit` in graph 089, including the original
comparison and naturality proofs, and `Transfinite` in graph 091. These are
source compilation results, not final audit evidence or a global replacement
existence theorem.
