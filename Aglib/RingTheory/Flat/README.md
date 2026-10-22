# Flat modules and regular principal quotients

[TorsionFreeBaseChange](TorsionFreeBaseChange.lean), imported as `Aglib.RingTheory.Flat.TorsionFreeBaseChange`, exports `Module.torsionFree_baseChange`. For a commutative domain `R`, a commutative flat `R`-algebra `S` and a torsion-free `R`-module `M`, it proves torsion freeness of the actual `S ⊗[R] M` over `S`. No domain assumption on `S` is required.

The module need not be projective. The exact algebra, flatness and torsion-free premises remain those in the source statement; the conclusion concerns the actual extended module. Local support/length base-change arguments and external algebraic applications consume this lower interface.

[Local criteria](LocalCriterion/README.md) give cyclic-quotient tensor tests, adic injectivity and the Noetherian local cokernel-flatness criterion. [Regular principal quotients](PrincipalQuotient/README.md) supply `Algebra.regular_and_flat_of_fibre_regular` for arbitrary flat finitely presented algebras, with no Noetherian or reducedness guard on the base. Its proved [finite-presentation prerequisites](FinitePresentation/README.md) construct the finite coefficient stage and actual local polynomial model. Scheme chart and line-bundle consumers remain downstream.

[LocalBasis](LocalBasis.lean) gives an actual finite basis after one localization outside a specified prime for a finitely presented flat module. The algebra corollary retains module finiteness and algebra finite presentation; rings and modules keep the source universe.

[IdealBaseChange](IdealBaseChange.lean), imported as `Aglib.RingTheory.Flat.IdealBaseChange`, supplies actual quotient-flat kernel comparisons for tensor products and algebra pushouts, with the original surjectivity and scalar-tower data. [Quotient](Quotient.lean) transports base-flatness of the actual kernel quotient through a surjective ring map; it adds no ambient or base-change flatness premise.

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

[EquationalCriterion](EquationalCriterion.lean), imported as
`Aglib.RingTheory.Flat.EquationalCriterion`, proves
`Module.Flat.of_forall_exists_lift_relation`: a module is flat if every finite
relation `∑ fᵢ xᵢ = 0` lifts, through a linear map from one module of a family
of flat modules, to a relation among preimages of the `xᵢ`. The proof is a
corollary of Mathlib's equational criterion (Stacks Project, Tag 00HK). The
consumer is the flatness of chart sections in Nitsure's Lemma 3.2,
`AlgebraicGeometry/Cohomology/Projective/FlatOfSections`.

[KernelCriterion](KernelCriterion.md) proves quotient-kernel tensor
injectivity and a flatness criterion for arbitrary rings and module universes.
Flatness after a surjective quotient and tensor injectivity for every ideal
contained in its actual kernel imply flatness before quotienting. The separate
annihilated-cokernel lemma has exactly its stated restricted scope. No
Noetherian, nilpotence or local-ring assumption is used. The
[Milnor flatness theorem](../Etale/MilnorPatching/Flat.md) supplies the kernel
conditions from the two actual component base changes.

[Adic/FiniteFree](Adic/FiniteFree.lean) gives
`Module.free_of_flat_quotient_pow`: a finite module over a Noetherian local
ring is free if its scalar extensions to `R ⧸ J ^ n` are flat for every
positive `n`, for any proper ideal `J`. Neither the ring nor the module is
assumed complete, and the basis may be empty. The proof retains one original
surjection and detects its kernel through the actual quotient base changes.
The [adic etale criterion](../Etale/Adic/LocalCriterion.lean) uses this
freeness before applying the discriminant criterion.
