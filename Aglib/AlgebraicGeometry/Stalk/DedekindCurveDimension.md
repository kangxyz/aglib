# DedekindCurveDimension

`Scheme.DedekindBase.stalk_dimension_le_two_of_generic_curve` retains the
Dedekind domain, specified fraction field, integral model and dominant locally
finite-type structure morphism. Its `OverField.Curve.Properties` argument is
exactly the native predicate for the same pullback's second projection,
including smoothness of relative dimension one, properness and geometric
connectedness. The proof consumes only its smoothness field, as in the source.
It uses the proved smooth-field stalk bound and the actual horizontal lift and
projection-stalk equivalence. No model-specific input or asserted universal
dimension theorem is substituted for the proof.

Source basis: `f8a3314ddecffcada2ec721d26d56a937bed9690`.

- Source: `R5Lab.AlgebraicGeometry.ArithmeticSurface.RelativeDimension`.
  SHA-256: `4231f79caefdd9eca03ed9375cbae3c5e98c14ad7a7a2fc384086615709af529`.
  Selected source ranges: `[[35, 47]]`.
  - `stalk_dimension_le_two_of_generic_curve` → `AlgebraicGeometry.Scheme.DedekindBase.stalk_dimension_le_two_of_generic_curve`.

Compiler and native-client evidence, provider hashes and complete correspondence
are recorded in the assigned packet-2 scratch return. No existing provider,
family README, facade or published release file is modified.
