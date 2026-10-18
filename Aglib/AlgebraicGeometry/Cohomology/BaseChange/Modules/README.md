# Canonical base change with arbitrary module coefficients

[Sections/Basic](Sections/Basic.lean), imported as `Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Sections.Basic`, uses the native `moduleSectionsPresheaf` from the lower [Modules/Sections](../../Modules/Sections.lean). For a scheme map `p : Y ⟶ X`, structural ring maps `α : A →+* Γ(X, ⊤)`, `β : B →+* Γ(Y, ⊤)`, a ring map `σ : A →+* B` and the equality `p.appTop.hom.comp α = β.comp σ`, an actual coefficient arrow `φ : M ⟶ p_* N` gives `moduleSectionsMapAlong` on the original section presheaves. `moduleSectionsTensorMapAlong` is its transpose under the native scalar adjunction on the functor categories. Its `_unit` and `_one_tmul` formulas retain the actual coefficient arrow on every original open; naturality in opens is part of the constructed natural transformation.

`moduleSectionsTensorComparison` specializes the coefficient arrow to the original geometric pullback unit. These constructions require neither quasicoherence nor flatness.

[Sections/AffineGlobal](Sections/AffineGlobal.lean) identifies the native affine tilde/global-section functor with the original top-section module and its structural scalar action. `moduleAffineTopSectionsIso` compares the original structural section presheaf at the top with restriction of these same affine sections; its forward and inverse maps are identity on section elements.

[Sections/Coefficients](Sections/Coefficients.lean) proves `moduleSectionsTensorMapAlong_comp_app`, the actual target-coefficient composition equation on each open. It uses the unique `moduleSectionsPresheafFunctor` from the lower section owner; that functor delegates its objects to the existing presheaves and its maps to native scalar restriction.

[Sections/AffinePullback](Sections/AffinePullback.lean) proves `moduleSectionsTensorComparison_top_eq_scalar`: for affine source and target and arbitrary quasicoherent coefficients, the original top-section tensor map is the canonical scalar base-change mate followed by the original affine pullback-section comparison. `moduleSectionsTensorComparison_top_isIso` proves invertibility when the displayed structural-ring square is a pushout. [Sections/OpenRestriction](Sections/OpenRestriction.lean) proves compatibility with the actual restriction isomorphisms, original open base-change coefficient map and geometric units. Its affine-chart theorem then uses the same scalar pushout comparison.

[Sections](Sections.lean), imported as `Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Sections`, constructs `moduleSectionsBaseChangeMap f σ M` for `f : X ⟶ Spec A` and every ring homomorphism `σ : A →+* B`. Its target uses the actual fibre product, actual first projection, actual pulled-back module and the structural maps obtained through `ΓSpecIso`. The `_one_tmul` formula retains the original geometric unit. `moduleSectionsBaseChangeMap_isIso_app` proves invertibility on every affine open for arbitrary quasicoherent `M`, without flatness, Noetherianity or finite-generation assumptions. `moduleSectionsTensorComparison_isIso_app_of_isPullback` also retains a supplied fibre square rather than requiring chosen canonical pullback objects. The structural-ring pushout is proved from the native affine pullback pushout and naturality of `ΓSpecIso`.

[Cech/ModuleBaseChange](../../Cech/ModuleBaseChange.lean) constructs `moduleCechTensorMapAlong` and its actual-fibre-product specialization `moduleCechBaseChangeMap`. The maps combine the native finite-product coefficient comparison, the original section tensor map and the native preimage-of-opens comparison. The projection equations retain those original forward maps; `moduleCechTensorMapAlong_forget_unit` proves the exact square with `extendScalarsForgetUnit` and `additiveCechGeometricMap` for `moduleCoefficientPullback`. `moduleCechBaseChangeMap_isIso` needs a finite affine family in a separated scheme and arbitrary quasicoherent coefficients. No covering hypothesis or flatness is needed for this complex isomorphism; these enter separately when computing cohomology and commuting it with tensor products.

[Map](Map.lean) constructs `moduleCohomologyRestrictionMap` and `moduleCohomologyTensorMap` on the unchanged additive `Sheaf.H`, for an actual coefficient arrow and compatible structural ring maps. Its original-unit and unit-pure-tensor formulas identify the canonical geometric forward map. The Ext cohomology universe is `u + 1`; construction does not require quasicoherence or flatness, and invertibility is a separate assertion.

[Map/Open](Map/Open.lean) constructs `moduleHPrimeTensorMap` on the native
open-Ext cohomology presheaves with their actual structural scalar actions.
It is the native scalar-adjunction transpose of the original geometric map
with the supplied coefficient arrow. Its unit and unit-pure-tensor formulas
retain that forward map on every open. `moduleHPrimeTensorMap_top` identifies
its whole-space component with `moduleCohomologyTensorMap` under the original
linear top comparisons, and `_top_isIso_iff` transfers invertibility in both
directions. Construction and identification use no quasicoherence or flatness
hypothesis.

[CechComparison](CechComparison.lean) constructs the native tensor map on
actual module Cech homology. Under exact scalar extension, its unit formula
follows from the actual additive geometric square of the supplied complex
map. [CechTransport](CechTransport.lean) transports an invertible complex map
through the original linear Cech computation and proves that its forward map
equals `moduleCohomologyTensorMap` in positive degrees. The covering family,
affine intersections, quasicoherence and the actual geometric square remain
explicit in these comparison lemmas. The geometric construction supplies the
complex map and its square; these lemmas alone do not assert a new base-change
endpoint.

[Map/Spec](Map/Spec.lean) specializes the original mate to the actual fibre
product over `Spec B → Spec A`. `moduleCohomologyBaseChangeMap f σ M n` is an
abbreviation of that same map, with the original `ΓSpecIso` structural actions
and module pullback unit. Its unit-pure-tensor formula is the actual geometric
module cohomology pullback.

[Naturality](Naturality.lean): `moduleCohomologyBaseChangeMap_naturality`, the
base-change map over spectra, is natural in the coefficient module. Its inputs
are `moduleCohomologyPullback_map` (`Cohomology/Functoriality/Modules/Composition`)
and `zariskiCohomologyMap_map` (`Cohomology/Functoriality/Pullback`).

[Separated](Separated.lean) proves
`moduleCohomologyBaseChangeMap_isIso_of_isSeparated`: for
`f : X ⟶ Spec A` quasi-compact and separated, a flat map `σ : A →+* B` and any
quasicoherent `M`, the canonical map is invertible in every nonnegative degree.
The finite-affine-cover version exposes the actual cover used in the proof.
Degree zero uses the original sheaf augmentation and
[CechTransport/DegreeZero](CechTransport/DegreeZero.lean); positive degrees use
[SeparatedPositive](SeparatedPositive.lean). The endpoint has no field,
Noetherianity, properness, finite-presentation or cohomological-finiteness
assumption. The qcqs extension is supplied below. The
[derived D+ comparison](../Derived/README.md) and
[native higher-direct-image comparison](../HigherDirectImage.lean) are
proved over arbitrary bases under their qcqs, flat-base-change and
quasicoherence hypotheses.

[Separated/Cartesian](Separated/Cartesian.lean) proves
`moduleCohomologyTensorMap_isIso_of_isPullback` for an actual supplied
cartesian square over `Spec B → Spec A`. The source map is quasi-compact and
separated, the specified ring homomorphism is flat, and the coefficients
are arbitrary quasicoherent. The theorem covers every degree and retains
the original tensor map, original module unit and actual structural maps
without replacing the supplied square by a chosen pullback object. Its
finite-affine-cover version uses the
[supplied-square Cech isomorphism](../../Cech/ModuleBaseChange/Cartesian.lean).

[SeparatedPositive](SeparatedPositive.lean) proves
`moduleCohomologyTensorMap_isIso_succ_of_finite_affine_cover` from a finite
affine cover of a separated scheme, the native flatness premise `σ.Flat`, and
arbitrary quasicoherent coefficients. Its
`moduleCohomologyTensorMap_isIso_succ_of_quasiCompact` endpoint takes
`[QuasiCompact f] [IsSeparated f]` for `f : X ⟶ Spec A` and obtains the
cover from the native finite affine subcover. Both theorems concern the
unchanged `moduleCohomologyTensorMap`, with the actual fibre-product
projections, structural ring maps and geometric module unit. They use no
Noetherianity, finite generation or finiteness of cohomology hypothesis.

[Qcqs](Qcqs.lean) proves
`moduleCohomologyBaseChangeMap_isIso_of_quasiSeparated`: for
`f : X ⟶ Spec A` quasi-compact and quasi-separated, any flat ring map
`σ : A →+* B`, any quasicoherent `M` and every nonnegative degree, the
original actual-fibre-product cohomology tensor map is invertible.
`moduleCohomologyTensorMap_isIso_of_quasiSeparated_of_isPullback` retains
an arbitrary supplied cartesian square and the original module unit.
There is no separation, Noetherianity, properness, finite-presentation or
cohomological-finiteness assumption. Native compact-open induction glues
finite affine unions through the original Mayer–Vietoris tensor ladder.
The intersection with each added affine is compact by quasi-separatedness
and is separated because it is open in that affine. The
[owning guide](Qcqs/README.md) records the exact restriction and gluing
comparisons used to discharge all local invertibility statements.

[Transitivity](Transitivity.lean) proves `moduleCohomologyBaseChangeMap_isIso_comp`: for
`f : X ⟶ Spec A`, `σ : A →+* B` and `τ : B →+* C`, if the degree-`n` base-change maps of `M`
along `σ` and of its pullback `M_B` along `τ` are isomorphisms, so is that of `M` along `τ ∘ σ`,
in every degree. The comparison is `baseChangeTransIso`, `(X_B)_C ≅ X_C`, with the `C`-linear
bijective transport `baseChangeTransCohomologyHom`; the unit-tensor identity is
`moduleCohomologyPullback_pullbackSquare_apply`
([Functoriality/Modules/PullbackComposition](../../Functoriality/Modules/PullbackComposition.lean)).
This is the composition of base-change isomorphisms in Nitsure's (C) (arXiv:math/0504590v1, proof
of Thm 4.3, p. 21).

[Composite](Composite.lean) treats iterated base change through a commutative square of rings
`τ ∘ σ = ψ ∘ π`. The lift `baseChangeCompLift : (X_B)_C ⟶ X_K` is cartesian over `Spec ψ`. For
flat `ψ`, quasi-compact separated `f` and quasi-coherent `M`, the composite
`C ⊗_B (B ⊗_A H) ⟶ C ⊗_B H(X_B) ⟶ H((X_B)_C)` of two base-change maps is an isomorphism when
the base-change map along `π` is
(`isIso_moduleCohomologyBaseChangeMap_comp_of_isIso`), and vanishing passes to `(X_B)_C`
(`subsingleton_moduleCohomology_baseChangeComp`). The core is stated at variable data
(`isIso_moduleCohomologyTensorMap_comp_of_square`). The residue-field forms take
`κ(σ⁻¹ t) → κ(t)`, through `Ideal.ResidueField.mapComap`
([RingTheory/LocalRing/ResidueFieldComap](../../../../RingTheory/LocalRing/ResidueFieldComap.lean)).
Transitivity and Composite give opposite 2-of-3 conclusions of one commutative identity; the
unit-pure-tensor manipulations of scalar extension they share are
`ModuleCat.extendScalarsComp_hom_app_comp_map_comp_one_tmul` and `ModuleCat.extendScalarsCongrIso`
([Algebra/Category/ModuleCat/ChangeOfRings/UnitTensor](../../../../Algebra/Category/ModuleCat/ChangeOfRings/UnitTensor.lean)).
