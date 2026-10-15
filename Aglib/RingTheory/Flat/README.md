# Flat extension of torsion-free modules

[TorsionFreeBaseChange](TorsionFreeBaseChange.lean), imported as `Aglib.RingTheory.Flat.TorsionFreeBaseChange`, exports `Module.torsionFree_baseChange`. For a commutative domain `R`, a commutative flat `R`-algebra `S` and a torsion-free `R`-module `M`, it proves torsion freeness of the actual `S ⊗[R] M` over `S`. No domain assumption on `S` is required.

The module need not be projective. The exact algebra, flatness and torsion-free premises remain those in the source statement; the conclusion concerns the actual extended module. Local support/length base-change arguments and external algebraic applications consume this lower interface.

[Exact](Exact.lean), imported as `Aglib.RingTheory.Flat.Exact`, proves
`Module.Flat.of_universally_lTensor_injective`: if the original map `M →ₗ[R] P`
is injective after tensoring with every scalar-universe module and `P` is flat,
then `M` is flat. The native tensor square proves the tensor-injectivity criterion;
no purity interface is assumed. `Module.Flat.ker_of_surjective` then proves that
the actual kernel of a surjection between flat modules is flat, using native
flat-quotient tensor exactness. The ring is commutative, and the scalar, source
and target module universes are independent. The current consumer is the lower
universal-tensor terminal-cycle criterion for bounded flat cohomology models.

The Exact leaf was compiled alone through the shared serialized wrapper,
receipt `1792086884716582000-29290`.
The external `work/proper-validation/FlatExactConsumer.lean` checks both native
interfaces in independent scalar/source/target universes and passed with receipt
`1792086931469921000-29690`. The inspected proofs use only `propext`,
`Classical.choice` and `Quot.sound`.
