# Finite generation and exact pairs

[Exact](Exact.lean) owns
`Module.Finite.of_exact_of_isNoetherian`. For linear maps `A → B → C`
with exact image/kernel, finite generation of `A` and Noetherianity of `C`
give finite generation of `B`. The second map need not be surjective:
the proof applies the native exact-surjective theorem to its actual range.
The ring and three module universes are independent.

For a Noetherian ring, finite generation of `C` supplies its Noetherianity.
Actual scheme-cohomology long exact sequences consume this lower theorem
in [Cohomology/Finiteness/Modules](../../AlgebraicGeometry/Cohomology/Finiteness/Modules.lean).
