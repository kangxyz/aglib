# Finite free projections of the same affine Weierstrass ring

The target is the original native `Projective.affineRing W`, namely
`W.toAffine.CoordinateRing`. Its native global `Algebra (Polynomial R)` structure
sends the variable to the original `affineX W`. This structure is preserved.

The monic cubic presentation already belongs to `Weierstrass/Genus/Charts`:
`affineCubicPolynomial`, `affineCubicEquiv`, the original x/y identities and
`affineCubicBasis` are reused. No duplicate cubic quotient or coordinate-ring
comparison is implemented. The polynomial is

```text
Z³ + a₂ Z² + (a₄ − a₁ T) Z + (a₆ − a₃ T − T²).
```

`FiniteProjection.yProjection W` sends the polynomial variable `T` to the same
original `affineY W` and preserves the original base constants.
`yAlgebra W` is an explicit value, not a global instance. `yAlgEquiv W`
promotes the existing cubic comparison to an equivalence over this actual
y-coefficient map. `yProjection_finiteFree` gives finiteness and freeness over
every commutative base ring. For nontrivial `R`, `yBasis W` has basis vectors
`1, affineX W, affineX W²`, and `yProjection_finrank` gives rank three.
The x-projection retains Mathlib's original basis `CoordinateRing.basis` with
vectors `1, affineY W`.

Over `[IsLocalRing R]`, `projectionDegree R` is two if `IsUnit (2 : R)` and
three otherwise. In the second branch, `(-2) + 3 = 1` and localness prove that
three is already a unit in the original `R`. The chosen degree is also a unit
in the original polynomial coefficient ring; this selection is not based only
on the characteristic of a generic field.

`projectionAlgebra W` is another explicit scalar-structure value, selecting the
unchanged native x-structure or the actual y-structure. `projectionMap W`
is its actual coefficient homomorphism to the same ring. `projectionMap_X`
retains its original x/y coordinate, and `projectionMap_C` retains the base
constants. `projection_finiteFree` holds over every commutative base ring.
`projectionBasis` and `projection_finrank` give its displayed degree when `R`
is nontrivial, under this same explicit scalar structure.

`normalizedTrace W` is the actual polynomial-base-linear native algebra trace,
multiplied by `C (degreeUnit⁻¹)`. Its identities are

```text
normalizedTrace W (projectionMap W p) = p
normalizedTrace W ∘ₗ Algebra.linearMap = LinearMap.id.
```

The coefficient map is therefore injective. The trace formula uses the actual
displayed finite basis, so this retraction is for the full degree-two or
degree-three algebra. It is not automatically a retraction on each completed
local factor; a factor can have a different rank whose degree is not a unit.

These are finite projection and trace results. No discriminant condition is
needed for them. They do not prove that the affine ring is regular, that its
singularities are rational, or that a resolution terminates. The uniform
H¹-length bound over normal proper birational modifications and genuine
singular-resolution termination remain separate obligations. A full generic
fraction-field separability comparison is not part of this core package.
