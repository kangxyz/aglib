# Finite product maps and rotation

`FiniteProjection` uses literal modular index reduction from `Fin (m * n)` to
`Fin m`, constructs tuple pullback and its sheet-zero section, and proves their
rotation formulas. Nonzero levels remain explicit where needed. The chosen
index equivalence and precomposition direction are preserved for finite-cover
consumers.

The repeat maps delegate to `RingHom.pi` and `Pi.evalRingHom`. Permutation
precomposition delegates to `RingEquiv.piCongrLeft'` at `s.symm`, so its literal
forward arrow remains `p ↦ p ∘ s`. The apply equations expose that orientation.
