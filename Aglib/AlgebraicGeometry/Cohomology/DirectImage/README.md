# Native resolution sections and higher direct images

[ResolutionSections](ResolutionSections.lean) defines
`moduleGlobalSectionsFunctorOfHom X α` as the original whole-space module
evaluation followed by native scalar restriction along
`α : R →+* Γ(X, ⊤)`. It is additive and preserves finite limits. A supplied
actual module injective resolution `I` gives
`moduleResolutionSectionComplex X α I`, its original integer-indexed section
complex; no replacement cohomology object is defined.
`moduleTopSectionsFunctorIso` is the shared natural identification from
top presheaf sections to this native global-section functor; its components
are the original `moduleTopSectionsIso`, the identity on section values.

`moduleResolutionSectionExtClass` sends actual section cycles to the
original Ext classes of `I`. It is surjective, and its zero criterion is
exactly the original section-boundary criterion, including degree zero.
`moduleResolutionSectionExtClass_eq_extMk` identifies the forward map with
native `InjectiveResolution.extMk` applied to the original representing
module morphism. Its scalar formula is original source precomposition with
`unitMul`, followed by the canonical module Ext/cohomology map.

`moduleResolutionSectionsCohomologyLinearEquiv X α I n` identifies native
homology of these same sections with unchanged additive `Sheaf.H` in every
nonnegative degree. Both scalar actions are the original actions through
`α`; the comparison uses native homology data and the actual class map.
Its `_apply_mk` formula preserves the original Ext class on native cycle
quotient representatives. The section homology remains in the native module
universe, while the original Ext cohomology remains in universe `u + 1`.
No shrinking or transported scalar action is used.

[ResolutionSections/Coefficients](ResolutionSections/Coefficients.lean)
proves coefficient naturality for every supplied native resolution lift.
The actual lifted cycle map retains its original component on sections.
`moduleResolutionSectionsCohomologyLinearEquiv_naturality` identifies the
native homology map of the original section-complex lift with the existing
`moduleCohomologyMapOfHom`. The native cycle and homology isomorphisms
preserve the original section values and cycle projection, respectively.

[ResolutionSections/Open/Basic](ResolutionSections/Open/Basic.lean)
evaluates the sole original `moduleSectionsPresheafFunctor` on each open.
`moduleResolutionOpenSectionComplex` is literal evaluation of the actual
integer-indexed module resolution, with its native structural ring action.
The original presheaf restrictions give
`moduleResolutionOpenSectionRestriction`; its component formula is
definitionally the original resolution-term restriction.

[ResolutionSections/Open/Cycles](ResolutionSections/Open/Cycles.lean)
sends native open-section cycles to original module-open Ext classes of
the supplied resolution. Its map is literally the native `extMk` of the
original represented module morphism. Surjectivity and the exact original
section-boundary criterion hold uniformly in every degree, including zero.
Scalars are the original scalar-center multiplication and the existing
native linear-category Ext action.

[ResolutionSections/Open](ResolutionSections/Open.lean) composes those
original classes with the canonical
[`moduleOpenExtCohomologyMap`](../Modules/Ext/Open.lean).
`moduleResolutionOpenSectionsCohomologyLinearEquiv X α U I n` identifies
native homology of actual `Γ_R(U, I.cochainComplex)` with the unchanged
native `Sheaf.H'` in every nonnegative degree. The quotient representative
and native homology-projection formulas retain the original cycle value
and Ext class. This comparison applies to every actual module sheaf and
open set; its scalar action is the specified original structural action.

[ResolutionSections/Open/Naturality](ResolutionSections/Open/Naturality.lean)
proves that original open restrictions and every actual coefficient-resolution
lift induce precisely the unchanged native `H'` maps. The statements are
equalities for the original linear comparisons and original native section
complexes. The represented module morphisms retain the actual open-free
precomposition and lift components; the original `extMk` and native cycle
projection formulas determine the forward maps.

[ResolutionSections/Presheaf](ResolutionSections/Presheaf.lean) assembles
these maps with the native evaluation/homology comparison.
`moduleResolutionSectionsHomologyPresheafIso` has native homology of
`((moduleSectionsPresheafFunctor X α).mapHomologicalComplex _).obj I.cochainComplex`
as source and the unchanged `moduleHPrimePresheaf` as target. Only the
small native source is lifted in universe; original `H'` is retained.
Its component formula is the original open-section class map. Open
naturality uses the native `NatTrans.app_homology`, and actual coefficient
maps retain every supplied native module-resolution lift. No alternative
cohomology-presheaf definition is introduced.

[ResolutionSections/Presheaf/Forget](ResolutionSections/Presheaf/Forget.lean)
factors the sole structural-ring section functor through the original
variable-ring module-presheaf forgetting functor. Its subsequent
initial-ring conversion and scalar restriction are exact. For every actual
module complex of any shape, `moduleComplexSectionsHomologyUnit` therefore
maps native homology of actual sections to actual sections of its homology
sheaf. It is the native presheaf-homology reflection unit, with the original
exact-conversion homology isomorphism. Its normalization and chain-map
naturality are explicit. This does not assume that sheaf forgetting
preserves homology.

[ResolutionSections/Pushforward](ResolutionSections/Pushforward.lean)
identifies actual pushforward sections with the original sections on
inverse-image opens, for every morphism and structural ring. The component
maps and their inverses are the identity on original section values.
The comparison is natural in coefficients and applies termwise to actual
module complexes of any shape.

[ResolutionSections/Pushforward/Spec](ResolutionSections/Pushforward/Spec.lean)
specializes this native comparison to an affine base. In particular,
`moduleSpecPushforwardGlobalSectionsIso f` identifies native
`moduleSpecΓFunctor` after the actual pushforward with the original source
global-section functor over `f.appTop.hom.comp (ΓSpecIso R).inv.hom`.
The forward and inverse maps retain the original section value. Its complex
version has the actual native section complexes as endpoints, and the
original top-to-open restriction square commutes as an equality of chain
maps.

[ResolutionSections/Open/Top](ResolutionSections/Open/Top.lean) identifies
the open-resolution comparison at the whole space with the original global
resolution comparison. The complex comparison is the original top-section
identity. The unchanged `H'`-to-`H` map takes its original class to precisely
the global class, through the canonical open-free-to-structure-module arrow.

These statements require no quasicoherence, affineness, flatness,
Noetherianity or finiteness. The actual affine computation of
`(Modules.pushforward f).rightDerived n` and its quasicoherence for qcqs
morphisms use the additional producer below; they do not follow from the
resolution comparison alone.

[Affine/Resolution](Affine/Resolution.lean) now proves the actual native
counit chain map a quasi-isomorphism for every qcqs morphism to a spectrum
and every quasicoherent module coefficient, using any supplied original
module injective resolution. Its principal section-homology maps are the
proved original localizations. The [affine family guide](Affine/README.md)
records the exact cohomology mate, original restriction normalization and
supplied principal square. This producer needs no flatness, Noetherianity,
cohomological finiteness or additional theorem-family premise.

[Affine](Affine.lean) now proves the actual higher-direct-image endpoint
over a spectrum. For qcqs `f` and arbitrary quasicoherent `M`,
`moduleHigherDirectImageAffineIso` identifies the native right-derived
pushforward with the tilde of homology of sections of the original
integer injective resolution. Its forward-map equation retains the
original resolution comparison and tilde--Gamma counit. Actual higher
direct images are quasicoherent in every nonnegative degree, over an
arbitrary ring. The independent public consumer passed
`1792108251788846000-25675` with only the standard three axioms. Passage
to a general target is proved by [QuasiCoherent](QuasiCoherent.lean),
and [derived flat base change](../BaseChange/Derived/README.md) is proved
for qcqs morphisms, flat base change and bounded-below objects with
quasicoherent homology.

[Restriction](Restriction.lean) gives `Scheme.Modules.derivedOpenBaseChangeIso`
on an actual cartesian square whose horizontal maps are open immersions.
It is the installed bounded-below derived pushforward/restriction comparison:
exact target restriction supplies one native composition iso and injective
preservation by source restriction supplies the other. Its `_unit` equation
retains the original ordinary `cartesianOpenBaseChange` and both installed
composite-derived units. The functor isomorphism is natural in all original
coefficients. `higherDirectImageOpenRestrictionIso` takes native homology,
through the shared original Rn/single comparison and exact restriction maps,
to compute the actual `rightDerived n` pushforward. The specialization
`higherDirectImageRestrictionIso f U n` uses the actual inverse-image open and
`f ∣_ U`. No quasicoherence, qcqs, Noetherianity or finiteness is required.

[Restriction/Resolution](Restriction/Resolution.lean) is the sole owner of
`openBaseChangeResolutionMapPlus` and
`higherDirectImageOpenRestrictionIso_app_resolution`. The literal cartesian
open map on a supplied original resolution, followed by its native
exact-restriction comparison, computes the unchanged native higher-image
open isomorphism. Its components retain the original ordinary cartesian
mate. The statements apply to all module sheaves and natural degrees,
without qcqs or quasicoherence assumptions.

[Restriction/Composition](Restriction/Composition.lean) proves
`higherDirectImageOpenRestrictionIso_comp`: successive original open
comparisons paste through the actual restriction-composition maps. It
applies to arbitrary module coefficients and every natural degree, with
the supplied Cartesian open squares and no finiteness or quasicoherence
premise. This does not construct a general nonflat base-change sheaf map.

[QuasiCoherent](QuasiCoherent.lean) proves
`moduleHigherDirectImage_isQuasicoherent`: for qcqs `f : X ⟶ Y` and any
quasicoherent `M`, the actual `((Modules.pushforward f).rightDerived n).obj M`
is quasicoherent for every natural degree on an arbitrary target scheme.
The original supplied-square open-restriction iso reduces each actual affine
chart to the completed native affine computation. No Noetherianity,
separatedness, relative coefficient flatness or finite generation is used.
This is the shared quasicoherence input for proper coherent direct images
and sheaf-valued flat base change.

[Proper/Coherent](Proper/Coherent.lean) descends the proved affine-base
proper theorem to every locally Noetherian target using the original
higher-image open comparison. All natural degrees and arbitrary coherent
coefficients are included, without a quasi-compact-target or relative-flatness
premise. See its [focused guide](Proper/README.md).
