# Horizontal

The namespace is `Scheme.LocalRing.GenericFiber`. The scheme, base map,
projection and stalk equivalence are the existing literal pullback objects.
Horizontal lifts are constructed from actual residue-field-valued arrows.
Projection injectivity, dimension transport and the canonical residue
comparison retain the source omit clauses and require no Dedekind premise.
The remaining horizontal scalar construction retains the Dedekind domain and
supplied fraction field. No integrality, normality, finite-type or smoothness
premise is added to these point and residue constructions.

The source `PreservesCodimensionOne` predicate is retired to the exact theorem
`projection_codimensionOne_dimension`; `codimensionOneProjection` is the actual
subtype image with that proof. No parallel preservation framework is defined.
The actual residue equivalence's forward map is proved to be precisely
`projection.residueFieldMap`, including reduction and structural constants.

The final local-to-function-field square retains the integral model, dominant
morphism and integral actual pullback hypotheses. It uses the current native
`FunctionField.DedekindGenericFiber.functionFieldRingEquiv`, whose forward map
is the actual `Scheme.functionFieldMap`, and `functionFieldMap_stalk` on the
same point. The focused client derives the fibre-integrality premise using
`FunctionField.DedekindGenericFiber.integral_genericFiber` on this same pullback.
That supplier is an existing read-only provider, not an assumed record.

Source basis: `f8a3314ddecffcada2ec721d26d56a937bed9690`.

- Source: `R5Lab.Aglib.AlgebraicGeometry.Stalk.GenericFiberCodimensionOne`.
  SHA-256: `3a7aff19070984be943d67839f1e1510a24fcdda2eb67d6ec67be02f1aa84b25`.
  Selected source ranges: `[[39, 214]]`.
  - `projection_injective` → `AlgebraicGeometry.Scheme.LocalRing.GenericFiber.projection_injective`.
  - `projection_over_genericPoint` → `AlgebraicGeometry.Scheme.LocalRing.GenericFiber.projection_over_genericPoint`.
  - `projection_imagePrime_eq_bot` → `AlgebraicGeometry.Scheme.LocalRing.GenericFiber.projection_imagePrime_eq_bot`.
  - `horizontalResidueConstants` → `AlgebraicGeometry.Scheme.LocalRing.GenericFiber.horizontalResidueConstants`.
  - `horizontalResidue_triangle` → `AlgebraicGeometry.Scheme.LocalRing.GenericFiber.horizontalResidue_triangle`.
  - `horizontalResidueLift` → `AlgebraicGeometry.Scheme.LocalRing.GenericFiber.horizontalResidueLift`.
  - `horizontalLift` → `AlgebraicGeometry.Scheme.LocalRing.GenericFiber.horizontalLift`.
  - `horizontalLift_projection` → `AlgebraicGeometry.Scheme.LocalRing.GenericFiber.horizontalLift_projection`.
  - `existsUnique_horizontalLift` → `AlgebraicGeometry.Scheme.LocalRing.GenericFiber.existsUnique_horizontalLift`.
  - `codimensionOneHorizontalLift` → `AlgebraicGeometry.Scheme.LocalRing.GenericFiber.codimensionOneHorizontalLift`.
  - `horizontalCodimensionOneEquiv` → `AlgebraicGeometry.Scheme.LocalRing.GenericFiber.horizontalCodimensionOneEquiv`.
  - `horizontalCodimensionOneEquiv_image` → `AlgebraicGeometry.Scheme.LocalRing.GenericFiber.horizontalCodimensionOneEquiv_image`.
  - `residueFieldRingEquiv` → `AlgebraicGeometry.Scheme.LocalRing.GenericFiber.residueFieldRingEquiv`.
  - `residueFieldRingEquiv_apply` → `AlgebraicGeometry.Scheme.LocalRing.GenericFiber.residueFieldRingEquiv_apply`.
  - `residueFieldRingEquiv_toRingHom` → `AlgebraicGeometry.Scheme.LocalRing.GenericFiber.residueFieldRingEquiv_toRingHom`.
  - `residueFieldRingEquiv_reduction` → `AlgebraicGeometry.Scheme.LocalRing.GenericFiber.residueFieldRingEquiv_reduction`.
  - `stalkEquiv_isUnit_iff` → `AlgebraicGeometry.Scheme.LocalRing.GenericFiber.stalkEquiv_isUnit_iff`.
  - `stalkEquiv_irreducible_iff` → `AlgebraicGeometry.Scheme.LocalRing.GenericFiber.stalkEquiv_irreducible_iff`.
  - `fibreResidueConstants` → `AlgebraicGeometry.Scheme.LocalRing.GenericFiber.fibreResidueConstants`.
  - `residueFieldRingEquiv_constants` → `AlgebraicGeometry.Scheme.LocalRing.GenericFiber.residueFieldRingEquiv_constants`.
  - `functionFieldRingEquiv_toFunctionField` → `AlgebraicGeometry.Scheme.LocalRing.GenericFiber.functionFieldRingEquiv_toFunctionField`.
  - `projection_preservesCodimensionOne` → `AlgebraicGeometry.Scheme.LocalRing.GenericFiber.projection_codimensionOne_dimension`.

Compiler and native-client evidence, provider hashes and complete correspondence
are recorded in the assigned packet-2 scratch return. No existing provider,
family README, facade or published release file is modified.
