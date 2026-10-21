# Multiplication monodromy quotient

`MonodromyQuotient.lean` uses the actual cover given by multiplication on an
arbitrary commutative group scheme over a field in universe `u`. Finiteness and
etaleness of that displayed multiplication morphism are explicit throughout.
The origin is its actual unit section. `N` is the kernel of the actual pointed
arithmetic projection, using the chosen algebraic-closure point of the field.

`fiberEquiv` identifies the origin fibre with the same geometric torsion-point
subgroup from `MultiplicationKernel.lean`. `quotientMap` evaluates an element of
`N` on the zero lift. The literal fibre-pair cover has its original first and
second projections. Their quotient lands in the literal origin kernel, and
`difference_pairPoint` evaluates it as `t - s`, in that order. Naturality of
this map proves `rho_sub` and the translation formula `rho_kernel`, hence
`quotientMap_mul`, `quotientHom` and `additiveQuotient`.

`originFiberEquiv` uses actual origin pullback. `rho_section` is the original
absolute Galois action on the same torsion group, and `quotientMap_galois`
identifies section conjugation with that action. `quotientMap_continuous` uses
finite-coordinate evaluation and an explicitly discrete target topology.

Only `quotientMap_surjective` adds `IsProper E.X.hom`,
`GeometricallyConnected E.X.hom`, `CharZero F`, the Galois-category and
fibre-functor classes on the actual geometric base change, and the original
universal `Stacks0BTX F` and `Stacks0387 F` premises. It applies the connectedness
criterion to this same multiplication cover. No premise asserting transitivity
of a replacement action is introduced. Neither Stacks family is proved here.

Source: `R5Lab.AlgebraicGeometry.EllipticCurve.Torsion.MultiplicationMonodromy`,
packet lines 52–331 and 357–405, SHA-256
`6eef22e0460bc2a0ef72e577392b9b174e92dc762246d54b7787960087967e89`.
The elliptic wrapper contributes its properness and connectedness only to
surjectivity. Source lines 332–353, cyclotomic-square character pullback and its
injection, remain downstream. Current consumer: the literal finite-level
transition square in [Transitions.lean](Transitions.lean).
