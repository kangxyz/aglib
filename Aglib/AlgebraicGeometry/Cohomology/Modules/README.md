# Coefficients, structural scalars and H0

[Basic](Basic.lean), imported as `Aglib.AlgebraicGeometry.Cohomology.Modules.Basic`, defines `AlgebraicGeometry.Scheme.Cohomology.moduleAddSheaf`, `moduleScalar` and `moduleCohomology`. The last object is the actual additive `Sheaf.H` of a module sheaf on a field scheme, with scalar action induced by structural constants. `moduleCohomologyMap` and `moduleCohomologyIso` are the corresponding actual coefficient map/isomorphism.

`moduleH0Equiv` is a structural-field linear equivalence with actual global sections. `structureModuleCohomologyEquiv` compares the unit module's cohomology with the unchanged structure-sheaf cohomology and its scalar action. No finiteness premise is needed for these constructions or H0 comparisons.

[StructureSheaf](StructureSheaf.lean) owns `Scheme.structureAddSheaf`, `structureScalar`, `structureCohomology` and `structureH0Equiv`. [Constants](Constants.lean) separately owns `Scheme.constants` and `constantSection`: actual structural ring maps into section rings, with restriction compatibility. [StalkScalars](StalkScalars.lean) identifies the action on native module stalks with the action induced by `moduleScalar`, through constant-germ equality; it is not a finite-support-only result.

[Scalars/Open](Scalars/Open.lean) gives `moduleHPrimeModuleOfHom` on the
unchanged native open-Ext groups `Sheaf.H'`. The action is the existing
coefficient multiplication associated to the specified structural ring map.
Original coefficient and restriction maps are linear. `moduleHPrimePresheaf`
retains these same groups and restrictions in `ModuleCat`; forgetting scalars
recovers the original native cohomology presheaf by the literal identity
isomorphism. The structural ring and scheme universes may differ. No
quasicoherence, flatness or finiteness premise is needed for these objects.

Fields/schemes use universe `u`, while cohomology is in `Type (u+1)`. Focused imports follow these leaves. Functoriality, long exactness, finite support, finiteness and base change consume these same objects and actions.

[Scalars](Scalars.lean) treats an arbitrary commutative ring and an explicit map
`α : R →+* Γ(X, ⊤)`. `moduleScalarOfGlobal` multiplies the original additive
coefficient sheaf by a global function. `moduleCohomologyModuleOfHom` equips the
unchanged `Sheaf.H` with the corresponding `R`-action; it is explicit in `α`,
rather than a global instance that could confuse different structural maps.
`moduleCohomologyMapOfHom` and `moduleH0EquivOfHom` are the actual linear
coefficient map and global-section comparison. The two `..._constants` theorems
identify the existing field maps and module structures literally. No
quasicoherence, flatness or finite-generation assumption is used.

[Functor](Functor.lean) packages the same objects and coefficient maps as
`moduleCohomologyFunctorOfHom X α n : X.Modules ⥤ ModuleCat.{u + 1} R`, with
cohomology carriers in universe `u+1`. Forgetting the specified scalars
recovers the native additive sheaf-cohomology functor by `Iso.refl`.
Faithful forgetting proves additivity, so native finite-biproduct
preservation applies without a quasicoherence or finiteness hypothesis.

[Scalars/Iso](Scalars/Iso.lean) constructs `moduleCohomologyIsoOfHom` for
an actual module-sheaf isomorphism and a specified structural ring map.
Its forward and inverse maps are exactly the existing
`moduleCohomologyMapOfHom` applied to the original coefficient isomorphism
and its inverse. The application formulas are literal identities on the
unchanged additive `Sheaf.H`; no extra hypothesis is needed.
`bijective_sheafH_map_of_iso` records that the additive coefficient map of a
module-sheaf isomorphism is bijective in every degree.

[Sections](Sections.lean) owns `moduleSectionsPresheaf` and its coefficient
functor before any Cech or cohomology comparison. These are the native section
modules with scalars restricted through the specified structural ring map.
The coefficient functor is additive with the original sectionwise addition.
`moduleTopSectionsIso` is the identity on underlying elements at the whole
space. Geometric section base change and Cech computations share these objects.

[Ext](Ext.lean) compares original module-linear Ext from the structure module
with the unchanged additive `Sheaf.H` in every degree. The map is exactly
native scalar forgetting on Ext, precomposed with the constant-integer map
representing one. Its bijectivity uses the proved acyclicity of the additive
sheaves underlying module injectives. Original coefficient maps and Yoneda
composition are preserved, with no quasicoherence or finiteness assumption.

[Ext/Scalars](Ext/Scalars.lean) gives `moduleExtCohomologyLinearEquiv` for a
specified structural ring map. The source action is original precomposition
by structure-module multiplication; the target is the existing coefficient
action on `Sheaf.H`. The equivalence retains the same canonical forward map.
The [Ext guide](Ext/README.md) records these scalar and section normalizations.

[Fibers](Fibers.lean) defines `moduleFiberCohomologyDimension f M q` on
`PrimeSpectrum R`. It uses the actual pullback along `Spec κ(p) → Spec R`,
the ordinary pulled module, original additive `Sheaf.H` and literal
structural residue-field action. It defines no alternative fibre or
cohomology object. The projective semicontinuity and Euler-characteristic
theorems supply the finiteness hypotheses under which this dimension is
the finite fibre-cohomology rank.

`Fibers.EulerCharacteristic` defines `moduleFiberEulerChar` by the alternating
sum of these original fibre dimensions. A genuine vanishing bound gives
`moduleFiberEulerChar_eq_sum_range`; the definition uses no embedding or
chosen model. Projective local constancy is proved by the actual universal
model in `Cohomology.Projective.EulerCharacteristic`.

[StructuralH0](StructuralH0.lean) compares the actual degree-zero cohomology
and native sections linearly for the original structural field action. Its
naturality and cokernel comparisons keep the original coefficient morphism;
finite cokernel transfer retains its finite-dimensionality premise.

[UnitHom](UnitHom.lean) gives `unitHomH0Equiv : (𝟙_ ⟶ M) ≃ H^0(X, M)` for every scheme, natural
in `M` (`unitHomH0Equiv_comp`). [DegreeZero](DegreeZero.lean) evaluates degree-zero coefficient
maps on sections over `⊤` (`equiv₀_moduleCohomologyMapOfHom`,
`equiv₀_moduleCohomologyFunctorOfHom_mapIso`).
