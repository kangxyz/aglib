/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildePullback
public import Aglib.AlgebraicGeometry.Descent.Modules.Fppf.ChosenPullback
public import Aglib.AlgebraicGeometry.Descent.Modules.Pseudofunctor
public import Aglib.AlgebraicGeometry.Descent.Modules.Substack
public import Aglib.Algebra.Category.ModuleCat.Descent.FaithfullyFlat
public import Aglib.CategoryTheory.Sites.Descent.Transfer
public import Aglib.CategoryTheory.Sites.Descent.SiteChange

/-!
# Faithfully flat descent of quasi-coherent sheaves on affine schemes

For a faithfully flat `f : A ⟶ B` in `CommRingCat`, Aglib's pseudofunctor of quasi-coherent
sheaves `Scheme.Modules.quasicoherentPseudofunctor` is a stack for the singleton presieve of
`Spec.map f`, given a comparison transformation over `Spec` from the module pseudofunctor
(`isStackFor_quasicoherentPseudofunctor_singleton_specMap_of_compTransAlong`).

The proof transfers the ring-level descent theorem
`CommRingCat.isStackFor_moduleCatExtendScalarsPseudofunctorOpOp_singleton` in two generic steps:
- a transformation (`Pseudofunctor.CompTransAlong Scheme.Spec`) from the module pseudofunctor on
  `CommRingCatᵒᵖ` to the quasi-coherent pseudofunctor, with components Mathlib's `tildeEquiv`
  (`specTransApp`) and pseudonaturality isomorphisms Aglib's `tildePullbackIso` (`specTransNat`);
  by `CompTrans.isStackFor_of_isStackFor`, the restriction `specQuasicoherentPseudofunctor` of
  the quasi-coherent pseudofunctor along `Spec` is a stack for `{f.op}`;
- the site change `Pseudofunctor.isStackFor_ofArrows_map_of_restrictAlong` along `Spec`, which
  maps the chosen pullbacks `CommRingCat.opChosenPullback f`, `opChosenPullback₃ f` to pullbacks
  of schemes (Mathlib's `isPullback_SpecMap_of_isPushout`).

The theorem here takes the transformation as a hypothesis. The transformation with components
`specTransApp` and `specTransNat` is `specCompTransAlong` in `CompTransCoherence.lean`, whose
coherence field `nat_comp` is Aglib's `tildePullbackIso_comp_hom_app` transported through the
bridges `fullsubcategory_mapComp'_hom_app_hom`, `pullbackPseudofunctor_mapComp'_hom_app` (Zariski
descent) and `moduleCatExtendScalarsPseudofunctorOpOp_mapComp'_hom_app'` (ring level); the
unconditional theorem `isStackFor_quasicoherentPseudofunctor_singleton_specMap` is stated there.

No descent datum at a specific pushout is ever formed in a goal: the kernel only compares the
generic statements at their instances.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite Bicategory Limits CommRingCat

namespace AlgebraicGeometry.Scheme.Modules

/-- The quasi-coherent pseudofunctor restricted along `Spec : CommRingCatᵒᵖ ⥤ Scheme`: a
pseudofunctor on the site `CommRingCatᵒᵖ` of affine schemes. -/
abbrev specQuasicoherentPseudofunctor : LocallyDiscrete CommRingCat.{u}ᵒᵖᵒᵖ ⥤ᵖ Cat.{u, u + 1} :=
  quasicoherentPseudofunctor.{u}.restrictAlong Scheme.Spec

/-- The component of the comparison transformation over `X : CommRingCatᵒᵖ`: Mathlib's
`tildeEquiv.functor : ModuleCat X.unop ⥤ QCoh (Spec X.unop)`. -/
abbrev specTransApp (X : CommRingCat.{u}ᵒᵖ) :
    moduleCatExtendScalarsPseudofunctorOpOp.{u}.obj (.mk (op X)) ⥤
      quasicoherentPseudofunctor.{u}.obj (.mk (op (Scheme.Spec.obj X))) :=
  (tildeEquiv (R := X.unop)).functor

/-- The pseudonaturality isomorphism of the comparison transformation along `f : Y ⟶ X` in
`CommRingCatᵒᵖ`: Aglib's `tildePullbackIso f.unop`, lifted to the full subcategories of
quasi-coherent sheaves. -/
def specTransNat {X Y : CommRingCat.{u}ᵒᵖ} (f : Y ⟶ X) :
    (moduleCatExtendScalarsPseudofunctorOpOp.{u}.map f.op.toLoc).toFunctor ⋙ specTransApp Y ≅
      specTransApp X ⋙
        (quasicoherentPseudofunctor.{u}.map (Scheme.Spec.map f).op.toLoc).toFunctor :=
  ((SheafOfModules.isQuasicoherent (Scheme.Spec.obj Y).ringCatSheaf).fullyFaithfulι.whiskeringRight
    _).preimageIso (tildePullbackIso f.unop).symm

lemma specTransNat_hom_app_hom {X Y : CommRingCat.{u}ᵒᵖ} (f : Y ⟶ X) (N : ModuleCat.{u} X.unop) :
    ((specTransNat f).hom.app N).hom = (tildePullbackIso f.unop).inv.app N :=
  rfl

lemma specTransNat_inv_app_hom {X Y : CommRingCat.{u}ᵒᵖ} (f : Y ⟶ X) (N : ModuleCat.{u} X.unop) :
    ((specTransNat f).inv.app N).hom = (tildePullbackIso f.unop).hom.app N :=
  rfl

/-- The chosen pullback of `f.op` with itself is mapped by `Spec` to a pullback of schemes. -/
lemma isPullback_spec_opChosenPullback {A B : CommRingCat.{u}} (f : A ⟶ B) :
    IsPullback (Scheme.Spec.map (opChosenPullback f).p₁) (Scheme.Spec.map (opChosenPullback f).p₂)
      (Scheme.Spec.map f.op) (Scheme.Spec.map f.op) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout₂ f)

/-- The inner chosen pullback of the threefold chosen pullback of `f.op` is mapped by `Spec` to a
pullback of schemes. -/
lemma isPullback_spec_opChosenPullback₃ {A B : CommRingCat.{u}} (f : A ⟶ B) :
    IsPullback (Scheme.Spec.map (opChosenPullback₃ f).chosenPullback.p₁)
      (Scheme.Spec.map (opChosenPullback₃ f).chosenPullback.p₂)
      (Scheme.Spec.map (opChosenPullback f).p₂) (Scheme.Spec.map (opChosenPullback f).p₁) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout₃ f)

instance (X : CommRingCat.{u}ᵒᵖ) : (specTransApp.{u} X).IsEquivalence :=
  inferInstanceAs (tildeEquiv (R := X.unop)).functor.IsEquivalence

/-- **Faithfully flat descent of quasi-coherent sheaves on affine schemes, given the comparison
transformation.** For a transformation `η` over `Spec` from the module pseudofunctor to the
quasi-coherent pseudofunctor whose components are equivalences, and a faithfully flat ring map
`f : A ⟶ B`, the pseudofunctor of quasi-coherent sheaves is a stack for the singleton presieve of
`Spec.map f : Spec B ⟶ Spec A`. The transformation with components `specTransApp` and
pseudonaturality isomorphisms `specTransNat` is `specCompTransAlong` (in
`CompTransCoherence.lean`, which also states the unconditional theorem). -/
theorem isStackFor_quasicoherentPseudofunctor_singleton_specMap_of_compTransAlong
    (η : Pseudofunctor.CompTransAlong Scheme.Spec quasicoherentPseudofunctor.{u}
      moduleCatExtendScalarsPseudofunctorOpOp.{u})
    [∀ X, (η.toCompTrans.app X).IsEquivalence] {A B : CommRingCat.{u}}
    (f : A ⟶ B) (hf : f.hom.FaithfullyFlat) :
    quasicoherentPseudofunctor.{u}.IsStackFor (Presieve.singleton (Spec.map f)) := by
  have h₁ : specQuasicoherentPseudofunctor.{u}.IsStackFor (Presieve.singleton f.op) :=
    η.toCompTrans.isStackFor_of_isStackFor
      (isStackFor_moduleCatExtendScalarsPseudofunctorOpOp_singleton f hf)
  rw [← Presieve.ofArrows_pUnit.{0}] at h₁ ⊢
  exact Pseudofunctor.isStackFor_ofArrows_map_of_restrictAlong (G := Scheme.Spec)
    quasicoherentPseudofunctor.{u} (f := fun (_ : PUnit.{1}) ↦ f.op)
    (fun _ _ ↦ opChosenPullback f) (fun _ _ _ ↦ opChosenPullback₃ f)
    (fun _ _ ↦ isPullback_spec_opChosenPullback f)
    (fun _ _ _ ↦ isPullback_spec_opChosenPullback₃ f) h₁

end AlgebraicGeometry.Scheme.Modules
