# DedekindDimension

The source injection and local-spectrum triangle are reused exactly as
`DedekindBase.baseToStalk_injective f x` and `fromSpecStalk_comp_eq f x` from
`HorizontalGenerization`. The source's extra supplied fraction-field argument
is unused in the injection's conclusion; this reuse adds no hypothesis.
`baseToStalk_comap_maximalIdeal` retains the source's arbitrary-ring and
arbitrary-scheme scope. The dimension-two theorem retains an explicit supplied
fraction field, integral model, dominant locally finite-type morphism and the
bound on every actual horizontal stalk. Local Noetherianity is derived from
local finite type over the Dedekind base. There is no assumed dimension family
or contraction family.

Source basis: `f8a3314ddecffcada2ec721d26d56a937bed9690`.

- Source: `R5Lab.Aglib.AlgebraicGeometry.Stalk.DedekindDimension`.
  SHA-256: `2f0c4d567939ef186c377a33fcb188be26b2b593e736335bcf92e187c2082db9`.
  Selected source ranges: `[[36, 114]]`.
  - `baseToStalk_injective` → `AlgebraicGeometry.Scheme.DedekindBase.baseToStalk_injective`.
  - `baseToStalk_comap_maximalIdeal` → `AlgebraicGeometry.Scheme.DedekindBase.baseToStalk_comap_maximalIdeal`.
  - `fromSpecStalk_comp` → `AlgebraicGeometry.Scheme.DedekindBase.fromSpecStalk_comp_eq`.
  - `stalk_dimension_le_two_of_horizontal_stalk_le_one` → `AlgebraicGeometry.Scheme.DedekindBase.stalk_dimension_le_two_of_horizontal_stalk_le_one`.

Compiler and native-client evidence, provider hashes and complete correspondence
are recorded in the assigned packet-2 scratch return. No existing provider,
family README, facade or published release file is modified.
