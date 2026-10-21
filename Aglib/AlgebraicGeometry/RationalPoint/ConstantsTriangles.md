# ConstantsTriangles

The namespace is `Scheme.RationalPoint`. The source `affineMap f` is retired
to `Spec.map (CommRingCat.ofHom f)`. `affine_triangle` proves its literal
contravariant map equation. The existing `fieldStalkIso` has its actual
local-spectrum arrow, and `origin_constants_triangle` identifies the original
stalk's structural arrow with Spec of the canonical constants map.

For an integral scheme, `origin_fraction_constants` proves that
`(algebraMap q.localRing X.functionField).comp q.constants` is exactly
`Scheme.functionFieldConstants X q.structureMap`, the native global generic
germ, using its current Spec-map comparison. Formal smoothness and essential
finite type of this same scalar map require the original smooth structure
morphism. No arbitrary field identification or scalar algebra is supplied.

The selected source `ResidueData` aliases retire here without another leaf:
`residueEquiv` is the existing `q.residueEquiv`, of definitionally identical
actual local-residue-field type. `constants` is `q.functionFieldConstants`,
definitionally `(algebraMap q.localRing X.functionField).comp q.constants`,
and this leaf supplies the exact native scalar comparison. Its integral-scheme
condition remains. The source's DVR/K-theory data, valuation normalization,
unit-reduction compatibility and regular-local dimension-one constructor stay
downstream; none is discharged by this retargeting.

Source basis: `f8a3314ddecffcada2ec721d26d56a937bed9690`.

- Source: `R5Lab.Aglib.AlgebraicGeometry.Stalk.RationalSectionConstants`.
  SHA-256: `31fc1fc3ca61dd9ec761992a8ab59bcbb217fdcc53253ef3eabbd779a277e810`.
  Selected source ranges: `[[21, 109]]`.
  - `affineMap` → `Spec.map (CommRingCat.ofHom f)`.
  - `affine_triangle` → `AlgebraicGeometry.Scheme.RationalPoint.affine_triangle`.
  - `fieldStalkIso_spec` → `AlgebraicGeometry.Scheme.RationalPoint.fieldStalkIso_spec`.
  - `origin_constants_triangle` → `AlgebraicGeometry.Scheme.RationalPoint.origin_constants_triangle`.
  - `origin_fraction_constants` → `AlgebraicGeometry.Scheme.RationalPoint.origin_fraction_constants`.
  - `origin_fraction_formallySmooth` → `AlgebraicGeometry.Scheme.RationalPoint.origin_fraction_formallySmooth`.
  - `origin_fraction_essFiniteType` → `AlgebraicGeometry.Scheme.RationalPoint.origin_fraction_essFiniteType`.
- Source: `R5Lab.Aglib.AlgebraicGeometry.Stalk.ResidueData`.
  SHA-256: `9f560a1d512b26122b9fdd7dd342075b740ecaf19120ed13fde9588bf4495c51`.
  Selected source ranges: `[[18, 20], [56, 59]]`.
  - `residueEquiv` → `q.residueEquiv : IsLocalRing.ResidueField q.localRing ≃+* F`.
  - `constants` → `q.functionFieldConstants = (algebraMap q.localRing X.functionField).comp q.constants`.

Compiler and native-client evidence, provider hashes and complete correspondence
are recorded in the assigned packet-2 scratch return. No existing provider,
family README, facade or published release file is modified.
