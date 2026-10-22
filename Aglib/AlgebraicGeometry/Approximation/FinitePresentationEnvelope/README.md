# Arithmetic systems and closed finite-presentation envelopes

```lean
import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.Absolute
```

[Absolute](Absolute.lean) proves
`AlgebraicGeometry.Scheme.FinitePresentationEnvelope.nonempty_system X` for
`X : Scheme.{u}` with `[CompactSpace X] [QuasiSeparatedSpace X]`. It constructs
an arithmetic approximation of the original scheme. The auxiliary
`nonempty_system_compactOpen` constructs the same data for a compact open of
a quasi-separated scheme.

In [System](System.lean), `Scheme.FinitePresentationEnvelope.System X` stores
`Index : Type u`, `Category.{u} Index`, `IsCofiltered Index`, and an actual
`diagram : Index ⥤ Scheme.{u}`. Its natural transformation `projection` has
source the constant diagram at `X`, and `isLimit` proves that
`Cone.mk X projection` is limiting. `M.cone.pt` is definitionally `X`.
Every transition is affine, every stage is compact, and each stage's native
map to `Spec (.of (ULift ℤ))` is locally of finite type.
`System.stage_isLocallyNoetherian` and
`System.stage_locallyOfFinitePresentation` derive the corresponding stage
properties. The stages need not be affine or separated over the integers.

The construction starts with finite-coefficient affine systems and extends
across one affine open at a time. Finite affine-cover induction glues the
systems with their actual overlaps, and the top-open isomorphism returns the
cone to the original scheme. The existence theorem supplies this process;
`System` itself is only its data interface.

[AffineExtension](AffineExtension.lean) proves
`nonempty_system_of_affine_open_union` for a quasi-separated `X`, an affine
open `U`, and a compact open `V` with `U ⊔ V = ⊤`. It extends the supplied
`System V.toScheme` to a system on the original `X`.
[Overlap](Overlap.lean) proves `exists_quasiAffine_open_preimage_eq` for a
cofiltered limit with affine transitions and quasi-separated stages. A
specified compact quasi-affine open `W` of the limit is the exact inverse
image `c.π.app i ⁻¹ᵁ U = W` of a compact quasi-affine open at some stage.

## Closed envelopes over an affine base

```lean
import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.FiniteType
```

In [FiniteType](FiniteType.lean),
`AlgebraicGeometry.Scheme.exists_closed_finitePresentation_envelope f`
assumes `f : X ⟶ S` between `Scheme.{u}`, `[IsAffine S]`,
`[LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]`. It returns
`Y : Scheme.{u}`, `g : Y ⟶ S`, and `i : X ⟶ Y` with

```lean
IsClosedImmersion i ∧ LocallyOfFinitePresentation g ∧
  QuasiCompact g ∧ IsSeparated g ∧ i ≫ g = f
```

It constructs the arithmetic system, captures the finite-type graph at an
actual stage, and uses finite-type kernel ideals to select a separated
finitely presented closed approximant. No Noetherian base or
finite-presentation assumption on `f` is needed.

This affine-base envelope is consumed by
[proper approximation](../Proper/README.md). The
[finite-type morphism guide](../../Morphisms/FiniteType/README.md) gives the
closed hull over a quasi-separated target with compact source, as well as its
qcqs-base specialization. The same arithmetic systems supply
[qcqs compactification](../../Compactification/QCQS.md).
