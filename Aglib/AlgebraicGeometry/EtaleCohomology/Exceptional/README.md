# Exceptional direct image

This family develops extension by zero and exceptional direct images on the
actual small-etale site. It uses the native sheaf, module, complex and derived
category carriers and retains the original adjunction maps. This is an active
implementation, not a completed exceptional calculus.

## Current source families

- `Open/`: actual abelian lower shriek from the existing slice equivalence and
  hom-indexed coproduct/sheafification construction; adjunction, exactness,
  open full faithfulness/stalks, and comparisons are being implemented.
  Abelian source is an intermediate supplier, not the arbitrary-ring endpoint.
  [LowerShriekExt](Open/LowerShriekExt.lean) retains the original exact-functor
  and adjunction Ext APIs.
- `Coefficients/`: actual constant ring sheaves, genuine `SheafOfModules`, and
  comparisons with module-valued sheaves. The standard explicit scalar/value
  range is `u+1` for schemes in `u`. No torsion or Noetherian condition belongs
  to these ordinary constructions. Native pullback/pushforward and original
  units must be compared, not replaced by unrelated functors.

- `Derived/`: native bounded-below ordinary module direct images and the
  original derived adjunction/unit, as suppliers for exceptional comparisons;
  this does not assert proper base change or choice independence.

- `Refinement/`: the actual original-derived-unit map for a proper refinement,
  using its genuine Cartesian open square. The original transformation now
  satisfies identity and composition coherence. Its invertibility and
  compactification independence remain separate proper-base-change obligations.

The associated compactification geometry belongs to
`AlgebraicGeometry/Compactification/Refinements`; genuine unbounded replacement
existence belongs to `Algebra/Homology/DerivedCategory/KInjective/Existence`.
The native unbounded image consumer uses the completed functorial K-injective
replacement and its original natural quasi-isomorphism, not a supplied-model
hypothesis or only a first injective successor operation.

## Completion boundaries

A definition from one compactification does not prove independence. The intended
bounded-below torsion calculus must include actual unit-induced comparisons,
choice independence, identity/composition coherence, original arbitrary base
change, localization and proper/open normalizations.

Unbounded work uses a torsion ring with a positive annihilator of its unit,
without requiring invertibility on the base. The actual functorial
K-injective replacement, original unbounded direct image and adjunction, exact
open image, and original unbounded localization triangle are supplied. Finite
relative-dimensional acyclic computation and unbounded proper exchange remain
additional obligations. No finite absolute dimension of the base is assumed.

Principal proper base change and Agent C's uniform proper relative bound remain
explicit external suppliers. Construction/coherence of the exchange does not
establish its invertibility. Existing `Proper`, `Finite`, `Constructible`, Nagata
and ordinary exchange sources are read-only here. Generic coefficient pullback
extensions use their native site owner rather than duplicating scheme functors.

Precise current acceptance is recorded separately with successful source hashes
and native receipts; uncompiled source is not described here as a closed result.
Generated imports and shared publication are serialized by the principal.

The ordinary module comparison adapters use the complete categorical
original-unit, selected-adjoint and source-pasting constructions. Their
valued comparisons retain the original coefficient equivalences and
preimage maps. The derived underlying mate is the canonical three-factor
comparison from exact forgetting and the existing relative-acyclicity
argument. The dense refinement map uses the same lower comparison-pasting
constructor. These interfaces preserve the existing coefficient ranges and
selected worlds; their publication does not assert the remaining torsion,
localization or chosen-exceptional coherence endpoints.

[Open/ModuleStalk](Open/ModuleStalk.lean) specializes the [general constant-ring point fibre](../../../Algebra/Category/ModuleCat/Sheaf/ConstantRing/PointFibre.lean) to the actual native site and coefficient worlds. The underlying additive comparison and outside-open zero-stalk conclusion use the original coefficient forgetting and original lower-shriek stalk.
