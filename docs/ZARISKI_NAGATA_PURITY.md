# Zariski–Nagata purity

The finite branch-purity interfaces concern the original algebra or morphism.
They retain generic separability and codimension-one unramifiedness. Neither
flatness nor an abstract purity theorem is an input to the final results.

## Algebraic interface

Import
`Aglib.RingTheory.Etale.ZariskiNagataPurity` for
`Algebra.etale_of_unramified_height_one`. Its hypotheses are:

- a commutative regular domain `A`, with native `IsRegularRing A`;
- a finite, faithful `A`-algebra `B` which is an integrally closed domain;
- separability of the canonically induced extension
  `FractionRing A → FractionRing B`;
- `Algebra.IsUnramifiedAt A q` for every prime ideal `q` of `B` of height one.

The conclusion is `Algebra.Etale A B` for the original algebra structure.
There is no characteristic or dimension bound. Generic separability remains
necessary when the codimension-one condition is vacuous.

The explicit-model theorem
`Algebra.etale_of_unramified_height_one_of_isRegularRing` accepts a field `E`
with the original `IsFractionRing B E`, compatible `A` and `FractionRing A`
actions, and separability over `FractionRing A`. It exposes the corresponding
scalar towers and independent universes directly. This is useful when the
fraction field already comes from a scheme or a specified realization.

See the [algebraic proof](../Aglib/RingTheory/Etale/ZariskiNagataPurity.lean)
and [focused consumers](../AglibTest/ZariskiNagataPurity.lean).

## Scheme interface

Import
`Aglib.AlgebraicGeometry.Morphisms.Etale.ZariskiNagataPurity` for
`Scheme.Hom.etale_of_unramified_coheight_one_of_regularStalks`.
For a finite dominant `f : X ⟶ Y`, it assumes:

- integral `X` and `Y`, with locally Noetherian `Y`;
- normal stalks on `X` and regular stalks on `Y`;
- separability of the actual function-field map induced by `f`;
- formal unramifiedness of `f.stalkMap x` at every source point of coheight one.

It concludes the native morphism property `Etale f`. The equivalent
`etale_of_unramified_stalk_dimension_one_of_regularStalks` interface states the
last condition using the dimension of the original source stalk. The
`etale_app_of_unramified_coheight_one_of_regularStalks` interface gives the
actual section-map conclusion on each nonempty affine target chart.

The chart algebra, generic germ and fraction-field actions use the original
maps. Empty affine charts are handled separately. All schemes in these
interfaces have the same universe parameter.

See the [scheme proof](../Aglib/AlgebraicGeometry/Morphisms/Etale/ZariskiNagataPurity.lean)
and [focused consumers](../AglibTest/ZariskiNagataPurityScheme.lean).

## Proof dependencies

The algebraic proof constructs the actual normal closure of the specified
fraction-field extension and its integral closure `C` over `A`.

1. Generic Galois endomorphisms and their height-one local comparisons give
   the coefficient map. Reflexive reconstruction extends its local
   surjectivity to the original module.
2. The resulting actual endomorphism-module equivalence has the form
   `End_A(C) ≃ₗ[A] (Fin r → C)`.
3. The all-dimensional Auslander criterion makes `C` flat over the regular
   base. Its local proof derives punctured freeness rather than accepting it
   at the final regular-ring interface.
4. Finite-flat purity makes this normalization étale. Étale descent and the
   original-algebra comparison return the conclusion for `B`.

The [reflexive-module guide](../Aglib/RingTheory/Reflexive/README.md) describes
the local dimension induction, quotient biduals and canonical localization
maps. Its global regular-ring endpoint concludes flatness and freeness at
each prime localization; global freeness over an arbitrary nonlocal base is
not asserted.

The scheme proof applies the algebraic theorem to the full inverse image of
each nonempty affine target chart. The
[function-field provider](../Aglib/AlgebraicGeometry/Morphisms/Finite/FunctionField.lean)
identifies the actual generic maps and scalar towers. The
[stalk-map provider](../Aglib/AlgebraicGeometry/Morphisms/FormallyUnramified/StalkMap.lean)
transports the original codimension-one hypothesis to those section algebras.

## Applying purity

Use the final theorem when its hypotheses concern the actual algebra or
morphism under consideration. For the actual finite generic normalization, import
`Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.RegularBase`.
`Scheme.FiniteEtale.GenericNormalization.etale_of_regularStalks` takes integral,
locally Noetherian `X`, regular base stalks, an arbitrary finite-etale cover of
its function field, and etaleness of the original target-stalk pullbacks at
codimension-one base points. It concludes etaleness of the original
normalization structure map, including for disconnected and empty generic
covers. It proves the component comparisons and needs none of the former
`Stacks0BMB`, `NormalizationLocalDimension` or `EtaleFromStalkBaseChange`
arguments; regularity also supplies the former explicit base-normality input.
See the [normalization guide](../Aglib/AlgebraicGeometry/Normalization/GenericFiniteEtale/RegularBase.md).

The full local quasi-finite `Stacks0BMB` statement is a separate interface; it
is not asserted by the finite integral-source theorem or this normalization
application.

The native focused tests include canonical fraction fields, specified
fraction-field models, and the actual scheme stalk/section interfaces.
