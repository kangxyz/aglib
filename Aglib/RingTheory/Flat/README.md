# Flat extension of torsion-free modules

[TorsionFreeBaseChange](TorsionFreeBaseChange.lean), imported as `Aglib.RingTheory.Flat.TorsionFreeBaseChange`, exports `Module.torsionFree_baseChange`. For a commutative domain `R`, a commutative flat `R`-algebra `S` and a torsion-free `R`-module `M`, it proves torsion freeness of the actual `S ⊗[R] M` over `S`. No domain assumption on `S` is required.

The module need not be projective. The exact algebra, flatness and torsion-free premises remain those in the source statement; the conclusion concerns the actual extended module. Local support/length base-change arguments and external algebraic applications consume this lower interface.
