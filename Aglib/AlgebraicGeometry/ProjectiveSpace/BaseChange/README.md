# Base change of polynomial projective space

The Cartesian entry module is `Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange`.
It proves that the actual polynomial `Proj` commutes with every coefficient
ring homomorphism. The base rings and coordinate type lie in the common
scheme universe; there is no finiteness, flatness, Noetherianity or nonempty
coordinate hypothesis.

- `Map` uses the native `Proj.map` of `MvPolynomial.gradedMap`. Its identity,
  composition and inverse-image formulas retain the original coefficient
  morphism and standard chart opens.
- `Charts` identifies its original homogeneous-localization ring maps with
  the polynomial coefficient maps under the existing chart equivalences.
  It proves the exact equation with the original structural maps to spectra.
- `ChartPullback` proves the original chart-ring square is a pushout and
  identifies both the resulting affine Cartesian square and the actual
  inverse-image chart square.
- `Cartesian` uses the original coordinate affine cover to prove
  `isPullback_map`. The resulting `baseChangeIso` maps to Mathlib's native
  pullback by exactly `pullback.lift (map f ι) (toSpec S ι) (map_toSpec f ι)`.
  Both original projection equations are public.
- The separate focused import `Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Affine`
  identifies any supplied original Cartesian square over a spectrum
  with polynomial projective space over that spectrum's ring. The comparison
  is the native uniqueness isomorphism of the two pullback squares, with
  both forward and inverse projection equations. No open-immersion premise
  is needed for this geometric comparison.

The lower algebraic owner is
[`RingTheory/MvPolynomial/GradedMap`](../../../RingTheory/MvPolynomial/GradedMap.lean).
Relative projective projections use this scheme comparison to apply the
proved coherent cohomology theorem after restricting the base to an affine
open. Pullback formulas for the twisting modules are a separate later
interface and are not premises of the Cartesian theorem.
