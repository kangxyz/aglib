# Nagata compactification over a qcqs base

```lean
import Aglib.AlgebraicGeometry.Compactification.QCQS
```

The declarations in [QCQS.lean](QCQS.lean) belong to
`AlgebraicGeometry.Scheme.Hom`. For schemes in one universe, the strongest
existence statement is:

```lean
theorem exists_schematicallyDense_compactification_of_qcqs
    {X S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ C : f.Compactification, IsSchemeTheoreticallyDominant C.j
```

`exists_compactification_of_qcqs` has the same hypotheses and conclusion
`Nonempty f.Compactification`. Here finite type is expressed by
`LocallyOfFiniteType f` and `QuasiCompact f`. The base is qcqs, expressed by
`CompactSpace S` and `QuasiSeparatedSpace S`.

A [compactification](Basic.lean) contains the original `X` as an open
subscheme of `C.Xbar`, with a proper `C.p : C.Xbar ⟶ S` and the equality
`C.j ≫ C.p = f`. The theorem makes this original open immersion schematically
dominant. The source may be empty or nonreduced. Neither the source nor the
base is assumed Noetherian, and `f` need not be finitely presented or
projective. No approximation diagram, hull, or stage model is a premise of
these public theorems.

## Approximation and return to the original morphism

The proof constructs arithmetic approximation systems for both `X` and `S`
using `Scheme.FinitePresentationEnvelope.nonempty_system` in
[Absolute](../Approximation/FinitePresentationEnvelope/Absolute.lean).
Quasi-compactness of `f` makes `X` compact; separatedness over the
quasi-separated base makes `X` quasi-separated. Each system has a small
cofiltered index in universe `u`, affine transitions, and a limiting cone
whose point is the original scheme. Its stages are finite type over
`Spec (.of (ULift ℤ))` and Noetherian.

[ActualDiagrams](ActualDiagrams.lean) exposes the conditional assembly as
`exists_schematicallyDense_compactification_of_integerFiniteType_isLimits`.
It uses the supplied source diagram to obtain a closed factorization
`X ⟶ Y ⟶ S`, where `Y` is qcqs and `Y ⟶ S` is separated and finitely
presented. The equation of this factorization is the original structural
map `f`. The unconditional
[finite-presentation hull](../Morphisms/FiniteType/README.md) also exposes
this construction for reuse.

For the finitely presented map `Y ⟶ S`,
`Scheme.exists_separated_model_of_isLimit` in
[SeparatedModels](../Descent/FinitePresentation/SeparatedModels.lean)
constructs a separated stage model over the base diagram. Separatedness is
obtained at a later stage by actual base-change descent; it is not an extra
field assumed in every finite-presentation model.

[NoetherianLimit](NoetherianLimit.lean) applies Noetherian compactification
at that stage. `C.baseChange (c.π.app i)` returns to the original base, and
`C.ofSourceIso f M.rawIso M.rawIso_hom_fst` transports to the original
morphism. The [base-change projection equations](BaseChange.lean) retain both
maps of the native pullback.

Finally, the original closed immersion `X ⟶ Y` followed by the open immersion
of `Y` into its proper model is a quasi-compact immersion.
`Compactification.ofImmersion` takes its native schematic image. This last
step supplies schematic dominance while retaining `C.j ≫ C.p = f`.

The lower [Noetherian theorem](Noetherian.lean) builds its compactification
using finite admissible blowup sequences, boundary control on a schematic
image in a finite product, and a common enlargement proved proper by
proper-surjective descent. Those constructions are internal suppliers of the
existence theorem, rather than caller-provided compactification data.
