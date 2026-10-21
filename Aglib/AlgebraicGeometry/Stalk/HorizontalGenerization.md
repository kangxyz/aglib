# HorizontalGenerization

`Scheme.DedekindBase.baseToStalk_injective` and
`localizationToStalk_injective` use the original integral dominant morphism
from a scheme to the spectrum of a Dedekind domain. The local-spectrum triangle
has only the arbitrary commutative-ring and scheme hypotheses retained by the
source omit clause. `CodimensionOnePoint.ofStalkPrime` uses the actual
`fromSpecStalk` and its stalk isomorphism; it has no integral-model premise.
The final generization theorem additionally requires local Noetherianity,
stalk dimension greater than one, and a nonzero actual image prime. Its output
is an actual horizontal dimension-one point specializing to the input point.

Source basis: `f8a3314ddecffcada2ec721d26d56a937bed9690`.

- Source: `R5Lab.Aglib.AlgebraicGeometry.Stalk.HorizontalGenerization`.
  SHA-256: `87dbbd6d7cd3403be57e4ee7dc7b01018cf2f445e4e0a85505ff2dc921972437`.
  Selected source ranges: `[[31, 134]]`.
  - `baseToStalk_injective` → `AlgebraicGeometry.Scheme.DedekindBase.baseToStalk_injective`.
  - `localizationToStalk_injective` → `AlgebraicGeometry.Scheme.DedekindBase.localizationToStalk_injective`.
  - `fromSpecStalk_comp_eq` → `AlgebraicGeometry.Scheme.DedekindBase.fromSpecStalk_comp_eq`.
  - `codimensionOneOfStalkPrime` → `AlgebraicGeometry.Scheme.CodimensionOnePoint.ofStalkPrime`.
  - `codimensionOneOfStalkPrime_specializes` → `AlgebraicGeometry.Scheme.CodimensionOnePoint.ofStalkPrime_specializes`.
  - `exists_horizontal_codimensionOne_generization` → `AlgebraicGeometry.Scheme.DedekindBase.exists_horizontal_codimensionOne_generization`.

Compiler and native-client evidence, provider hashes and complete correspondence
are recorded in the assigned packet-2 scratch return. No existing provider,
family README, facade or published release file is modified.
