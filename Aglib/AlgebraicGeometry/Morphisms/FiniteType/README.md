# Closed finite-presentation hulls

```lean
import Aglib.AlgebraicGeometry.Morphisms.FiniteType.FinitePresentationHull
```

[FinitePresentationHull](FinitePresentationHull.lean) proves the following
in `AlgebraicGeometry.Scheme`:

```lean
theorem exists_separated_finitePresentation_factorization_of_compactSpace
    {X S : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace S]
    (f : X ⟶ S) [LocallyOfFiniteType f] [IsSeparated f] :
    ∃ (Y : Scheme.{u}) (e : X ⟶ Y) (g : Y ⟶ S),
      CompactSpace Y ∧ QuasiSeparatedSpace Y ∧ IsClosedImmersion e ∧
      LocallyOfFinitePresentation g ∧ QuasiCompact g ∧ IsSeparated g ∧ e ≫ g = f
```

Thus a separated locally finite-type map from a compact scheme to a
quasi-separated target has a separated finitely presented hull containing
its original source as a closed subscheme. The target need not be compact.
The source and all output schemes remain in universe `u`, and the final
composite is the specified `f`.

`exists_separated_finitePresentation_factorization_of_qcqs` has the same
conclusion under `[CompactSpace S] [QuasiSeparatedSpace S]`,
`[QuasiCompact f] [LocallyOfFiniteType f] [IsSeparated f]`. It derives
compactness of `X` from these hypotheses. Neither theorem assumes a
Noetherian base, finite presentation of `f`, or an approximation diagram.

The proof derives quasi-separatedness of `X`, constructs its actual
[arithmetic system](../../Approximation/FinitePresentationEnvelope/README.md),
and applies
`Scheme.exists_separated_finitePresentation_factorization_of_integerFiniteType_isLimit`
in [IntegerFiniteTypeHull](../../Descent/FiniteType/IntegerFiniteTypeHull.lean).
The conditional [descent interface](../../Descent/FiniteType/README.md)
retains its supplied diagram; this import discharges that premise.
Finite-type subideals of the native kernel provide closed approximants, and
fixed-target separatedness descent chooses a separated stage.

The conclusion is a closed finite-presentation factorization. Properness of
`g` is not asserted. [Nagata compactification](../../Compactification/QCQS.md)
separately embeds the original source openly in a proper scheme over a qcqs
base. The affine-base
[closed envelope](../../Approximation/FinitePresentationEnvelope/README.md)
is the interface used to construct
[proper fixed-base approximation](../../Approximation/Proper/README.md).
