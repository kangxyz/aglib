# Conditional normalized-point resolution

API: [exists_regular_normalizedPointBlowupChain_of_initial_cones_of_complete_base](NormalizedResolution.lean#L33).

Import `Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.NormalizedResolution`.

`exists_regular_normalizedPointBlowupChain_of_initial_cones_of_complete_base`
assumes a commutative Noetherian Nagata local domain `R` of dimension two
with `NormalModificationH1Vanishing R`. The map `f : X ⟶ Spec R` is
proper and dominant, `X` is integral with normal stalks, and the original
`functionFieldMap f` is invertible.

The remaining inputs are:

- `hcones`: at each original singular stalk, a triple `(t,g₀,g₁)`
  generating its maximal ideal and a nonzero homogeneous quadratic `q`
  over its original residue field, such that the entire
  `RingHom.ker (CaseOne.canonicalConeMap t g)` is `Ideal.span {q}`.
- A commutative local domain `A` of dimension two, complete for its maximal
  ideal, and a local injective map `a : A →+* R` with finite original
  residue-field map. The theorem does not add Noetherianity of this `A`.

It constructs `Y`, `g : Y ⟶ X` and a finite literal
`NormalizedPointBlowupChain g`. The structural map is proper, dominant and
satisfies `BirationalOver g (𝟙 X)`; `Y` is integral with regular stalks.
For every original open `U` whose stalks are regular, `g ∣_ U` is an
isomorphism.

`FiniteResolution` first constructs the ordinary chain with proved normal
stages. `exists_normalizedPresentation` then supplies the normalized chain
and an explicit terminal isomorphism `E` satisfying
`E.hom ≫ normalizedMap = ordinaryMap`. Its comparison preserves length,
although this final endpoint does not export a length equation.
Properness, birationality, regularity and regular-open preservation are
transported through that same triangle, without equating the two schemes.

This is a conditional endpoint. Initial-cone recognition from arbitrary
rational or rational-Gorenstein input is not proved here. The theorem also
does not close the full RES or RES-QE construction.
