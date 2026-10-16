# Native derived categories of scheme module sheaves

[Basic](Basic.lean), imported as `Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic`, defines the local instance choice `Scheme.Modules.standardHasDerivedCategory`. For `X : Scheme.{u}` it uses exactly `HasDerivedCategory.standard` with morphisms in universe `u + 1`. Consumers activate this choice locally; the leaf imposes no perfectness or restriction construction.

[Restriction](Restriction.lean) constructs the exact native functor `Scheme.Modules.derivedRestrict j : DerivedCategory X.Modules ⥤ DerivedCategory U.Modules` for an actual open immersion `j : U ⟶ X`, with its shift and triangulated structures. `derivedRestrictFactors` retains the native `Q` factorization, and `restrictDerivedIso` transports an actual derived isomorphism using its original source and target components. The mathematical declaration namespace and canonical maps are unchanged.

The lower input is [ordinary complex restriction](../Complex/Restriction.lean). Local perfectness and its open-restriction results consume these native interfaces; no additional derived model, localization or perfect-derived category is introduced.

[RestrictionHom](RestrictionHom.lean) expresses actual derived morphism
restriction at native chain endpoints using the inverse source and forward
target components of `derivedRestrictFactors`. Its composition, chain-map,
isomorphism and inverse formulas preserve those original components.
[LiftedHom](LiftedHom.lean) gives the same endpoint-normalized Hom transport for
any supplied derived functor and specified factorization of an actual complex
functor; the factorization is data. Neither leaf requires perfectness or bounds.
Native Mathlib `Q_map_eq_of_homotopy` and `left_fac`/`right_fac` supply homotopy
equality and fractions directly; no old `toDerived_*` facade is introduced.

The [bounded-above family](Minus/README.md) constructs arbitrary derived
pullback on Mathlib's existing `DerivedCategory.Minus` using actual flat models.
The object/map equations, localization factorization, flat-input agreement and
natural identity/composition isomorphisms retain the original chain maps and
independent chosen derived-category universes. No flatness of the scheme map,
quasicoherence or Noetherian hypothesis is imposed.
