# Purely inseparable field comparison

This family proves invariance under arbitrary purely inseparable field
extensions, including infinite-degree extensions and imperfect base fields.
It uses the existing finite-etale categories and their original base-change
functors, rather than a replacement Galois category.

- [Stages](Stages.lean) obtains finite-stage equivalences from the existing finite-pure
  descent theorem. Actual field-limit object descent proves essential
  surjectivity for base change on quasi-compact, quasi-separated schemes.
- [Fullness](Fullness.lean) descends an actual map between field-base-changed covers to a
  finite intermediate field, then uses the finite-stage full functor to
  reconstruct the original map.
- [FiniteEtale](FiniteEtale.lean) supplies `specBaseChange_isEquivalence` in namespace
  `AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable`, assembles the
  equivalence for the literal `baseChange (Spec.algebraMap K L)` functor.
  Faithfulness is the existing faithfully-flat result.
- [RootsPullback](RootsPullback.lean) composes this equivalence with the existing Artin-site
  comparison. Its theorem
  `Kummer.rootsCohomologyPullback_bijective_of_isPurelyInseparable` proves
  bijectivity of the original root-cohomology pullback in every degree for
  positive invertible order. Source and target Ext universes are independent.

The comparison retains positive invertible root order and independent Ext
universes. No invariance of the multiplicative sheaf is asserted, and no
finite-degree or perfectness hypothesis is imposed on the field extension.

For finite purely inseparable extensions,
[FiniteConstants/SectionUnit](FiniteConstants/SectionUnit.lean) proves
invertibility of the original adjunction unit on finite constant abelian
sheaves on every scheme over the base field. It uses the original
represented coefficient unit, followed by general isomorphism cancellation
and naturality transport.
