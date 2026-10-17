# Affine and fppf descent of quasi-coherent sheaves

This subfamily works towards row F6 of [PICARD_PLAN.md](../../../../../doc/PICARD_PLAN.md):
`Pseudofunctor.IsStack Scheme.fppfTopology` for
`Scheme.Modules.quasicoherentPseudofunctor` (from [Pseudofunctor](../Pseudofunctor.lean)).
The affine input is ring-level faithfully flat descent of modules
(`CommRingCat.isStackFor_moduleCatExtendScalarsPseudofunctorOpOp_singleton`, in
`Algebra/Category/ModuleCat/Descent`). The two sides are compared through Aglib's
`Scheme.Modules.tildePullbackIso φ : tilde.functor R ⋙ pullback (Spec.map φ) ≅
extendScalars φ.hom ⋙ tilde.functor S`. The comparison needs the coherence of this isomorphism
with Mathlib's composition isomorphisms.

The coherence is [TildePullback](../../../Modules/QuasiCoherent/Affine/TildePullback.lean), in
the owner of `tildePullbackIso`
([QuasiCoherent/Affine](../../../Modules/QuasiCoherent/Affine/README.md)):
`tildePullbackIso_comp_hom` (natural transformations) and `tildePullbackIso_comp_hom_app`
(components, for an arbitrary proof `h : Spec.map (a ≫ b) = Spec.map b ≫ Spec.map a`). Its proof
uses the existing Aglib lemma `conjugateEquiv_associator_inv` of
[Adjunction/Mates](../../../../CategoryTheory/Adjunction/Mates.lean).

[ChosenPullback](ChosenPullback.lean): for `f : A ⟶ B` in `CommRingCat`, chosen pullbacks
of `f.op` for Mathlib's `Pseudofunctor.DescentData'` on `CommRingCatᵒᵖ`. The rings and maps are
named definitions: `pushout₂ f` (`B ⊗_A B`), `pushoutInl`, `pushoutInr`, `pushout₃ f` (the
threefold object), `pushout₃Inl`, `pushout₃Inr`, `pushout₃Outer`, and the three factor maps
`pushout₃ι₁`, `pushout₃ι₂`, `pushout₃ι₃`. Their equations and `isPushout₂`, `isPushout₃` are also
provided. Named definitions keep one `HasPushout` instance term in every later occurrence;
differing instance terms made kernel checks fail in development.

The chosen pullbacks themselves are reducible (`abbrev`): `CommRingCat.opChosenPullback f :
ChosenPullback f.op f.op` and `opChosenPullback₃ f`. `Spec` maps them to pullbacks of schemes
whose projections are `Spec.map` of the named ring maps (see `AffineStack`).

[AffineStack](AffineStack.lean): the affine stack statement, conditional on the comparison
transformation: `isStackFor_quasicoherentPseudofunctor_singleton_specMap_of_compTransAlong`.
For `η : Pseudofunctor.CompTransAlong Scheme.Spec quasicoherentPseudofunctor
moduleCatExtendScalarsPseudofunctorOpOp` with equivalence components and a faithfully flat
`f : A ⟶ B`, `quasicoherentPseudofunctor.IsStackFor (Presieve.singleton (Spec.map f))`. It is
obtained from F5's ring-level theorem by the generic transfer lemmas of
[CategoryTheory/Sites/Descent](../../../../CategoryTheory/Sites/Descent/README.md):

- `specQuasicoherentPseudofunctor`: the quasi-coherent pseudofunctor restricted along
  `Spec : CommRingCatᵒᵖ ⥤ Scheme` (`Pseudofunctor.restrictAlong`);
- `specTransApp` (Mathlib's `tildeEquiv.functor`, an equivalence) and `specTransNat`
  (`tildePullbackIso`, lifted to the full subcategories, with `specTransNat_hom_app_hom`,
  `specTransNat_inv_app_hom`): the components and pseudonaturality isomorphisms of the intended
  transformation;
- `isPullback_spec_opChosenPullback`, `isPullback_spec_opChosenPullback₃`: `Spec` maps the chosen
  pullbacks of `ChosenPullback.lean` to pullbacks of schemes;
- the final theorem: `CompTrans.isStackFor_of_isStackFor`, then
  `Pseudofunctor.isStackFor_ofArrows_map_of_restrictAlong` along `Spec`.

The transformation with components `specTransApp`, `specTransNat` is `specCompTransAlong`, and the
unconditional theorem is in [CompTransCoherence](CompTransCoherence.lean).

[CompTransCoherence](CompTransCoherence.lean): the coherence of the comparison transformation,
the transformation itself, and the affine stack theorem
`isStackFor_quasicoherentPseudofunctor_singleton_specMap`: for a faithfully flat
`f : A ⟶ B` in `CommRingCat`, `quasicoherentPseudofunctor.IsStackFor
(Presieve.singleton (Spec.map f))`. All declarations compile at the default heartbeat budget,
without `backward.*` options beyond the two inherited ones on `natComp_of_natCompAmbient` and
`natCompAmbient_of_natCompPullback`.

- `Pseudofunctor.NatCompAmbient` and `natComp_of_natCompAmbient`: for a
  `CompTransAlong G Pr.fullsubcategory F₁` with generic `G`, `Pr`, `F₁`, `app`, `nat`, the field
  `nat_comp` follows from the same identity in the ambient pseudofunctor `P` (the proofs `p`, `q`
  of the composite equations are implicit parameters);
- `Pseudofunctor.NatCompPullback` and `natCompAmbient_of_natCompPullback`: for
  `P := pullbackPseudofunctor`, the ambient identity follows from the identity written with
  Mathlib's `pullbackCongr` and `pullbackComp` (F3's bridge); `natCompAlong_of_natCompPullback`
  composes the two, with the field stated through `Pseudofunctor.NatCompAlong` (in
  [SiteChange](../../../../CategoryTheory/Sites/Descent/SiteChange.lean));
- `comp_eq_of_leaves` and `comp_eq_of_leaves_heq`: the rearrangement of
  `tildePullbackIso_comp_hom_app` into the shape of `nat_comp`, with every factor of both
  identities given separately; in the second form the objects and factors of the two identities
  are related by equations of objects and `HEq`s. `Functor.map_heq_of_heq` and
  `pullbackCongr_hom_app_heq` are the congruences used for the factors;
- `Pseudofunctor.natCompAlong_of_transport`: for an arbitrary functor `G : CommRingCatᵒᵖ ⥤ Scheme`
  and arbitrary `app`, `nat`, the coherence `NatCompAlong` from the identity of
  `tildePullbackIso_comp_hom_app` with the schemes, the morphisms `Spec.map _`, the functors
  `tilde.functor _` and the isomorphisms `tildePullbackIso _` replaced by variables, and from the
  identifications of these variables with `G`, `app` and `nat` (equations of schemes; `HEq`s of
  morphisms of schemes, of the objects and morphisms in the image of `app`, and of the components
  of `nat`). The proof substitutes the variables and applies `comp_eq_of_leaves_heq`;
- `moduleCat_mapComp'_hom_app_op'`: F5's composition isomorphism, for morphisms of
  `CommRingCatᵒᵖ`, as `extendScalarsComp`;
- `specNatCompAlong`: the coherence of `specTransNat`, i.e. `natCompAlong_of_transport` at
  `Scheme.Spec`, `specTransApp`, `specTransNat` with the hypothesis
  `tildePullbackIso_comp_hom_app f.unop g.unop (Spec.map_comp _ _) M` and every identification
  `rfl` or `HEq.rfl`; `specCompTransAlong := CompTransAlong.mk' … specTransApp specTransNat
  specNatCompAlong`, with the instance that its components are equivalences;
- `isStackFor_quasicoherentPseudofunctor_singleton_specMap`: the conditional theorem of
  [AffineStack](AffineStack.lean) at `specCompTransAlong`.

[Precoverage](Precoverage.lean): the instance
`Scheme.instHasIsosFppfPrecoverage : fppfPrecoverage.HasIsos`. Mathlib's `fppfPrecoverage`
derives only `IsStableUnderBaseChange` and `IsStableUnderComposition`; with the third instance,
Mathlib's `Pseudofunctor.IsStack.of_precoverage` and `IsPrestack.of_precoverage` apply to
`Scheme.fppfTopology`. Its intended owner is Mathlib's `AlgebraicGeometry/Sites/Fpqc.lean`.

What remains of row F6:
- the fppf `IsStack` reduction: `Pseudofunctor.IsStack Scheme.fppfTopology` for
  `quasicoherentPseudofunctor`, from Zariski descent (F3) and the affine theorem above, through
  locality on the base, refinement of a covering by affines, quasi-compactness of an affine base,
  and a finite affine family turned into one faithfully flat map `A ⟶ ∏ Bᵢ`, then
  `IsStack.of_precoverage`;
- the line-bundle substack (invertible sheaves);
- the fppf stack form of closed subschemes (descent along one morphism is in
  [Descent/IdealSheaf](../../IdealSheaf/README.md));
- descent of open subschemes.

Kernel note: prove coherence lemmas for arbitrary morphisms of schemes and instantiate them, so
that the kernel never compares two presentations of the same term at `Spec R`.

Development observations: every kernel comparison at `Spec` of two composites whose factors or
implicit objects differ in presentation, and of two components of `pullbackCongr` (`eqToIso` of a
`Spec.map` equation) or of `mapComp'` with differently presented arguments, timed out or exhausted
memory, while comparisons of components of `tildePullbackIso`, `specTransNat`, `specTransApp`,
`pullbackComp`, and of objects and morphisms of schemes, took seconds.

Working hypothesis (not checked against the kernel implementation): projections such as `≫` and
`NatTrans.app` are unfolded rather than compared through their arguments; reducing the `Eq.rec`
inside `pullbackCongr` then makes the kernel try to decide the `Spec.map` equation by unfolding
`Spec.map`; and the kernel first compares the arguments of two applications of a definition,
falling back to unfolding only when the arguments are not cheaply definitionally equal.

The proofs follow these rules, which worked in development:
- state an identity to be proved at `Spec` through a definition (`NatCompAlong`,
  `NatCompPullback`);
- prove it as one application of a generic lemma whose hypothesis is the source identity with its
  `Spec`-dependent parts replaced by variables (`natCompAlong_of_transport`), so that the source
  identity matches the hypothesis syntactically, and whose remaining hypotheses are equations and
  `HEq`s between the cheap pieces above, proved by `rfl`;
- do every substitution of one presentation for another inside the generic proof.
Pass the scheme arguments of `pullHom` explicitly (`X₁ := Spec B` and so on); otherwise
unification can assign the unfolded structure of `Spec B`. Take proofs inside `pullbackCongr` as
variables, and substitute them (`obtain rfl : h = Spec.map_comp a b := rfl`). Obtain
componentwise statements from natural-transformation statements by `rfl` identifications.

Focused consumers:
[AglibTest/AlgebraicGeometry/Descent/Modules/Fppf/AffineStack.lean](../../../../../AglibTest/AlgebraicGeometry/Descent/Modules/Fppf/AffineStack.lean),
[CompTransCoherence.lean](../../../../../AglibTest/AlgebraicGeometry/Descent/Modules/Fppf/CompTransCoherence.lean)
(including the axiom guard of the affine stack theorem) and
[Precoverage.lean](../../../../../AglibTest/AlgebraicGeometry/Descent/Modules/Fppf/Precoverage.lean);
the coherence of `tildePullbackIso` has its consumer at
[AglibTest/AlgebraicGeometry/Modules/QuasiCoherent/Affine/TildePullback.lean](../../../../../AglibTest/AlgebraicGeometry/Modules/QuasiCoherent/Affine/TildePullback.lean).
