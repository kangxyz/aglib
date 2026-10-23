# Finite closed supports

[FiniteClosedSupport](FiniteClosedSupport.lean) constructs a finite stage for point-supported
small-etale coefficients. Its declarations belong to
`AlgebraicGeometry.Scheme.EtaleCohomology.Curves.FiniteClosedSupport`.

For an arbitrary scheme `X : Scheme.{u}` and a set `Z : Set X`, the actual
objects are

- `pointScheme X Z = ∐ x : Z, Spec (X.residueField x.val)`;
- `inclusion X Z = Sigma.desc (fun x : Z => X.fromSpecResidueField x.val)`.

The source is a coproduct of the actual residue fields, not of geometric
closures and not a replacement for the possibly nonreduced ambient scheme.
The canonical map is retained throughout.

## Geometry

`range_inclusion` identifies the image with `Z`. The map is injective,
surjective on stalks, and a monomorphism even before imposing finiteness.
For `hfin : Z.Finite` and `hclosed : ∀ x ∈ Z, IsClosed {x}`,
`inclusion_isClosedImmersion` and `inclusion_isFinite` give the native morphism
properties. The closed-embedding proof uses the finite union of the images of
the actual closed components; stalk surjectivity is source-local.

For every field `K : Type u` and every actual point `s : Spec K ⟶ X`,
`exists_lift_iff` says that a morphism `t : Spec K ⟶ pointScheme X Z` with
`t ≫ inclusion X Z = s` exists exactly when `s (IsLocalRing.closedPoint K)`
belongs to `Z`. The lift is the native residue-field factorization followed by
the original coproduct inclusion. Algebraic closedness is unnecessary here.

## Arbitrary coefficients

For `hsep : ∀ x : Z, IsSepClosed (X.residueField x.val)`,
`globalSections_preservesEpimorphisms` gives exactness on epimorphisms for
original abelian sheaves of value universe `u + 1`. It uses the published
strictly-local component evaluation theorem and the published finite disjoint
cover gluing theorem. The actual component charts are those of
`Scheme.Etale.sigmaChart`.

`constant_integer_projective` transports projectivity of the existing free
terminal representable through the existing normalized
`constantIntegerFreeTerminalIso`. Consequently `subsingleton_H` proves

`Subsingleton (Sheaf.H.{w} F q)`

for every `F : AbelianSheaf.{u, u + 1} (pointScheme X Z)`, every positive `q`,
and the explicitly supplied
`HasExt.{w} (AbelianSheaf.{u, u + 1} (pointScheme X Z))`.
The Ext universe is independent of the scheme universe. No finite, torsion,
constructible, or coherent hypothesis on `F` is present. The empty support is
included. Closedness of the ambient points is needed for the closed-immersion
statement, not for the coefficient acyclicity statement.

The intended consumer is the original adjunction-unit identification for
coefficients supported on a finite closed stage. Generic finite direct-image
exactness and stalk comparisons remain in their existing `Finite` owners.
