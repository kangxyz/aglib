# Structural scalars in residue fields and stalks

The declarations live in `AlgebraicGeometry.Scheme`.
[Constants](Constants.lean) constructs `residueConstants X p x` from the
actual composite `X.fromSpecResidueField x ≫ p`; `residueAlgebra` is its
induced scalar structure. `residue_finite` requires an actual closed point and
local finite type of the displayed structure morphism to a field spectrum.

[StalkScalars](StalkScalars.lean) retains `stalkConstants` as a transparent
field specialization of the general `Scheme.Hom.stalkScalar` from
[Stalk.Scalar](../Stalk/Scalar.lean). The original global-section map and actual
germ are definitionally the same; `stalkConstants_eq_stalkScalar` is `rfl`. `residueConstants_eq_stalk` and
`residueAlgebra_eq_stalk` prove equality of the two scalar structures, rather
than choosing an unrelated residue-field isomorphism.
`residue_finite_from_stalk` transports the closed-point finiteness theorem
across that equality and keeps local finite type explicit.

The direct consumers are curve degree and principal-colength calculations.
The formulas apply to actual schemes over a field without a curve, properness
or smoothness assumption. Exact incoming source hashes are recorded against
R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.
