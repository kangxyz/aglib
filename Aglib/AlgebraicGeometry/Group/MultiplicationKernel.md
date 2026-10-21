# Actual multiplication kernels

`MultiplicationKernel.lean` works over a field `F : Type u` with an actual
commutative group object `E : Grp (FScheme F)`. It admits every natural level,
including zero. Multiplication is literally `(𝟙 E.X)^n`; `multiplicationHom`
packages the same map in group objects.

`kernelGroup` reuses `Scheme.Group.Kernel.group`. Its canonical `kernelSquare`
yields `kernelSchemeIso` to the original scheme pullback of multiplication and
the unit section. The comparison preserves the original inclusion. The literal
pullback is used for the finite-etale cover constructions; it carries no
separately implemented group law.

`geometricPoints` is the additive group of actual morphisms
`Spec (AlgebraicClosure F) → E` over `Spec F`. `finiteTorsionPoints` is the
kernel of actual `n`-fold addition on those points. `point_multiplication`,
`torsion_fibre_equation`, `kernelPointEquiv` and `nativeKernelPointEquiv`
identify precisely these points with the literal and native kernels, with the
original inclusion formula. The Galois action is precomposition by the actual
contravariant spectrum map; `kernelPointEquiv_galois` records naturality.

Finiteness of the literal kernel and its torsion-point set requires
`IsFinite (multiplication E n).left`. Etaleness, positivity, characteristic zero,
a degree formula and rank-two structure are not consequences of these definitions.
[MultiplicationEtale.lean](MultiplicationEtale.lean) and the
[interface client](../../../AglibTest/MultiplicationEtale.lean) use these exact
kernel and point maps with explicit multiplication hypotheses.

Source: `R5Lab.AlgebraicGeometry.EllipticCurve.Torsion.FiniteLevel`, packet
lines 53–197, SHA-256
`4713f0f004da1f37065a679853621758c0a084e6380da28bfdfc2a4a01030473`.
Only the actual group object of its elliptic wrapper is used. The source
cyclotomic tensor twist at lines 198–237 remains downstream. The canonical
native-kernel comparison and Galois naturality are proved here on the same
maps; they introduce no theorem-family hypothesis.
