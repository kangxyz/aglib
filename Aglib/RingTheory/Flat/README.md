# Flat modules and regular principal quotients

[TorsionFreeBaseChange](TorsionFreeBaseChange.lean), imported as `Aglib.RingTheory.Flat.TorsionFreeBaseChange`, exports `Module.torsionFree_baseChange`. For a commutative domain `R`, a commutative flat `R`-algebra `S` and a torsion-free `R`-module `M`, it proves torsion freeness of the actual `S ⊗[R] M` over `S`. No domain assumption on `S` is required.

The module need not be projective. The exact algebra, flatness and torsion-free premises remain those in the source statement; the conclusion concerns the actual extended module. Local support/length base-change arguments and external algebraic applications consume this lower interface.

[Local criteria](LocalCriterion/README.md) give cyclic-quotient tensor tests, adic injectivity and the Noetherian local cokernel-flatness criterion. [Regular principal quotients](PrincipalQuotient/README.md) supply `Algebra.regular_and_flat_of_fibre_regular` for arbitrary flat finitely presented algebras, with no Noetherian or reducedness guard on the base. Its proved [finite-presentation prerequisites](FinitePresentation/README.md) construct the finite coefficient stage and actual local polynomial model. Scheme chart and line-bundle consumers remain downstream.

[LocalBasis](LocalBasis.lean) gives an actual finite basis after one localization outside a specified prime for a finitely presented flat module. The algebra corollary retains module finiteness and algebra finite presentation; rings and modules keep the source universe.

[IdealBaseChange](IdealBaseChange.lean), imported as `Aglib.RingTheory.Flat.IdealBaseChange`, supplies actual quotient-flat kernel comparisons for tensor products and algebra pushouts, with the original surjectivity and scalar-tower data. [Quotient](Quotient.lean) transports base-flatness of the actual kernel quotient through a surjective ring map; it adds no ambient or base-change flatness premise.
