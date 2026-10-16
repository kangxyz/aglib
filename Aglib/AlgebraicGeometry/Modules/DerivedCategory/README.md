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

[Coherent](Coherent.lean) defines
`Scheme.Modules.coherentHomologyObjects X` on Mathlib's actual
`DerivedCategory.Plus X.Modules`. Under the explicit locally Noetherian
guard, it says exactly that every original native homology sheaf is
coherent. The property imposes no upper cohomological bound and no
termwise condition on a representative. It retains the supplied native
`HasDerivedCategory` instance with a derived universe independent of the
scheme universe; it does not select another derived model.

The property contains zero, is invariant under original isomorphisms and
is closed under distinguished-triangle extensions. The last proof uses
the actual mapped triangle, the original native homology connecting maps
and exact sequence, and the sole lower
`ObjectProperty.prop_middle_of_exact_five`. Coherent kernels and cokernels
are taken only for maps between known coherent homology objects, followed
by the proved actual extension closure. No arbitrary-subsheaf closure or
ambient Serre-class assertion is used.

The source passed with receipt `1792117566074302000-73788` in 2.5 seconds
at the default budget. `CoherentDerivedHomologyConsumer.lean` passed with
receipt `1792117773247131000-76697`. The inspected exported definition
retains its explicit `IsLocallyNoetherian X` parameter. The consumer checks the four native interfaces
and the shared `DerivedCategory.Plus.property_of_homology_bounds` for a
triangulated functor applied to a cohomologically bounded source. Five
universe levels remain independent; only the source's actual homology
layers enter the Postnikov argument. The inspected declarations use only
the three standard axioms.

This target property is used by coherent direct-image and closed-support
induction. It does not assert finiteness of a proper direct image by
itself, supply a bounded finite-projective model, or introduce a separate
notion of perfectness.

[Coherent/Shift](Coherent/Shift.lean) supplies
`modulePlusHomologyShiftIso` from the original native homology shift
sequence, including coefficient naturality. Under the same explicit
locally Noetherian guard, `coherentHomologyObjects_shift` and its iff
form show invariance under every integer shift. The resulting native
`IsTriangulated` instance lets a triangulated functor pull back this
property directly; the shared finite Postnikov theorem then applies
without another local extension-closure instance. The source passed
with receipt `1792117842355771000-77917` in 2.6 seconds, and the independent
five-universe `CoherentDerivedShiftConsumer.lean` passed with receipt
`1792117898358616000-79631`. The inspected declarations use only the
three standard axioms.

[Coherent/Single](Coherent/Single.lean) supplies
`coherentHomologyObjects_single X M hM i` and its iff form: the original
native single has coherent homology exactly when its original coefficient
is coherent. The proof uses the sole native single/homology comparison
in its specified integer degree and the native zero homology in every
other degree. The locally Noetherian guard and arbitrary supplied derived
universe remain explicit. The source passed with receipt
`1792118937024541000-94987` in 2.6 seconds, and the independent consumer
`CoherentDerivedSingleConsumer.lean` passed with receipt
`1792119008710727000-95844`, with only the three standard axioms.
