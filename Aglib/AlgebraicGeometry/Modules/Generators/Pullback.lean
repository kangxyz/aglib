/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Generators.OpenFreeFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-!
# Pullback of the original open-free module generators

The original module pullback adjunction and section-representing equivalences
identify pullback of a free sheaf on a site object with the free sheaf on its
image. The whole natural isomorphism retains the literal universal section.
For schemes the site functor is inverse image of opens. No flatness is needed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe u v u'

namespace PresheafOfModules

private theorem freeYonedaEquiv_naturality_source
    {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}}
    {U V : C} (i : U ⟶ V) (M : PresheafOfModules.{v} R)
    (p : (free R).obj (yoneda.obj V) ⟶ M) :
    freeYonedaEquiv ((free R).map (yoneda.map i) ≫ p) =
      M.map i.op (freeYonedaEquiv p) := by
  have h := (freeAdjunction R).homEquiv_naturality_left (yoneda.map i) p
  change freeHomEquiv ((free R).map (yoneda.map i) ≫ p) =
    yoneda.map i ≫ freeHomEquiv p at h
  change yonedaEquiv (freeHomEquiv ((free R).map (yoneda.map i) ≫ p)) = _
  rw [h]
  exact (yonedaEquiv_naturality _ i).symm

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{v}) [HasSheafify J AddCommGrpCat.{v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- Native sheafification of the free module presheaves on representables. -/
def freeYonedaSheafFunctor : C ⥤ SheafOfModules.{v} R :=
  yoneda ⋙ PresheafOfModules.free R.obj ⋙
    PresheafOfModules.sheafification (𝟙 R.obj)

/-- The original free-module and sheafification adjunctions represent sections. -/
def freeYonedaSheafHomEquiv (U : C) (M : SheafOfModules.{v} R) :
    ((freeYonedaSheafFunctor R).obj U ⟶ M) ≃ M.val.obj (op U) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _).trans
    PresheafOfModules.freeYonedaEquiv

/-- The original section equivalence respects the original site arrows. -/
theorem freeYonedaSheafHomEquiv_naturality {U V : C} (i : U ⟶ V)
    (M : SheafOfModules.{v} R) (p : (freeYonedaSheafFunctor R).obj V ⟶ M) :
    freeYonedaSheafHomEquiv R U M ((freeYonedaSheafFunctor R).map i ≫ p) =
      M.val.map i.op (freeYonedaSheafHomEquiv R V M p) := by
  dsimp [freeYonedaSheafHomEquiv, freeYonedaSheafFunctor]
  erw [Adjunction.homEquiv_naturality_left]
  exact PresheafOfModules.freeYonedaEquiv_naturality_source i _ _

/-- Representable monomorphisms remain monic in the original free module sheaves. -/
theorem freeYonedaSheafFunctor_map_mono {U V : C} (i : U ⟶ V) [Mono i] :
    Mono ((freeYonedaSheafFunctor R).map i) := by
  have : Mono ((PresheafOfModules.free R.obj).map (yoneda.map i)) := by
    apply PresheafOfModules.mono_of_injective
    intro W
    apply Finsupp.mapDomain_injective
    intro a b hab
    exact (cancel_mono i).mp hab
  change Mono ((PresheafOfModules.sheafification (𝟙 R.obj)).map
    ((PresheafOfModules.free R.obj).map (yoneda.map i)))
  infer_instance

/-- The original free-module section equivalence respects coefficient maps. -/
theorem freeYonedaSheafHomEquiv_comp (U : C) {M N : SheafOfModules.{v} R}
    (p : (freeYonedaSheafFunctor R).obj U ⟶ M) (q : M ⟶ N) :
    freeYonedaSheafHomEquiv R U N (p ≫ q) =
      q.val.app (op U) (freeYonedaSheafHomEquiv R U M p) := by
  dsimp [freeYonedaSheafHomEquiv]
  erw [Adjunction.homEquiv_naturality_right]
  rfl

/-- The native free sheaf corepresents the native section evaluator. -/
def freeYonedaSheafCorepresentable (U : C) :
    Functor.CorepresentableBy
      (evaluation R (op U) ⋙ CategoryTheory.forget (ModuleCat.{v} (R.obj.obj (op U))))
      ((freeYonedaSheafFunctor R).obj U) where
  homEquiv := freeYonedaSheafHomEquiv R U _
  homEquiv_comp p q := freeYonedaSheafHomEquiv_comp R U q p

variable {D : Type u'} [Category.{v} D] {K : GrothendieckTopology D}
    {F : C ⥤ D} {R' : Sheaf K RingCat.{v}} [Functor.IsContinuous F J K]
    (φ : R ⟶ (F.sheafPushforwardContinuous RingCat.{v} J K).obj R')
    [HasSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [(pushforward.{v} φ).IsRightAdjoint]

/-- The original pullback adjunction corepresents sections on the image site object. -/
def freeYonedaSheafPullbackCorepresentable (U : C) :
    Functor.CorepresentableBy
      (evaluation R' (op (F.obj U)) ⋙
        CategoryTheory.forget (ModuleCat.{v} (R'.obj.obj (op (F.obj U)))))
      ((pullback.{v} φ).obj ((freeYonedaSheafFunctor R).obj U)) where
  homEquiv := ((pullbackPushforwardAdjunction.{v} φ).homEquiv _ _).trans
    (freeYonedaSheafHomEquiv R U _)
  homEquiv_comp p q := by
    dsimp only [Equiv.trans_apply]
    erw [Adjunction.homEquiv_naturality_right, freeYonedaSheafHomEquiv_comp]

/-- Pullback of the original free module sheaf on a site object is the original
free module sheaf on its image, by the same section-representing property. -/
def freeYonedaSheafPullbackIso (U : C) :
    (pullback.{v} φ).obj ((freeYonedaSheafFunctor R).obj U) ≅
      (freeYonedaSheafFunctor R').obj (F.obj U) :=
  (freeYonedaSheafPullbackCorepresentable R φ U).uniqueUpToIso
    (freeYonedaSheafCorepresentable R' (F.obj U))

/-- The whole original Hom equation fixes the actual pullback comparison and its generator. -/
theorem freeYonedaSheafPullbackIso_homEquiv (U : C) (M : SheafOfModules.{v} R')
    (f : (freeYonedaSheafFunctor R').obj (F.obj U) ⟶ M) :
    freeYonedaSheafHomEquiv R U ((pushforward.{v} φ).obj M)
        ((pullbackPushforwardAdjunction.{v} φ).homEquiv _ _
          ((freeYonedaSheafPullbackIso R φ U).hom ≫ f)) =
      freeYonedaSheafHomEquiv R' (F.obj U) M f := by
  change (freeYonedaSheafPullbackCorepresentable R φ U).homEquiv
      (((freeYonedaSheafPullbackCorepresentable R φ U).homEquiv.symm
        ((freeYonedaSheafCorepresentable R' (F.obj U)).homEquiv (𝟙 _))) ≫ f) =
    (freeYonedaSheafCorepresentable R' (F.obj U)).homEquiv f
  rw [Functor.CorepresentableBy.homEquiv_comp, Equiv.apply_symm_apply,
    ← Functor.CorepresentableBy.homEquiv_comp, Category.id_comp]

omit [HasSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}] in
private theorem freeYonedaSheafPullbackHomEquiv_naturality {U V : C} (i : U ⟶ V)
    (M : SheafOfModules.{v} R')
    (f : (pullback.{v} φ).obj ((freeYonedaSheafFunctor R).obj V) ⟶ M) :
    freeYonedaSheafHomEquiv R U ((pushforward.{v} φ).obj M)
        ((pullbackPushforwardAdjunction.{v} φ).homEquiv _ _
          ((pullback.{v} φ).map ((freeYonedaSheafFunctor R).map i) ≫ f)) =
      M.val.map (F.map i).op
        (freeYonedaSheafHomEquiv R V ((pushforward.{v} φ).obj M)
          ((pullbackPushforwardAdjunction.{v} φ).homEquiv _ _ f)) := by
  rw [Adjunction.homEquiv_naturality_left, freeYonedaSheafHomEquiv_naturality]
  rfl

/-- The original pullback comparison respects every original site arrow. -/
theorem freeYonedaSheafPullbackIso_naturality {U V : C} (i : U ⟶ V) :
    (pullback.{v} φ).map ((freeYonedaSheafFunctor R).map i) ≫
        (freeYonedaSheafPullbackIso R φ V).hom =
      (freeYonedaSheafPullbackIso R φ U).hom ≫
        (freeYonedaSheafFunctor R').map (F.map i) := by
  apply ((pullbackPushforwardAdjunction.{v} φ).homEquiv _ _).injective
  apply (freeYonedaSheafHomEquiv R U _).injective
  rw [freeYonedaSheafPullbackHomEquiv_naturality,
    freeYonedaSheafPullbackIso_homEquiv]
  have hV := freeYonedaSheafPullbackIso_homEquiv R φ V
    ((freeYonedaSheafFunctor R').obj (F.obj V)) (𝟙 _)
  simp only [Category.comp_id] at hV
  rw [hV]
  exact (freeYonedaSheafHomEquiv_naturality R' (F.map i)
    ((freeYonedaSheafFunctor R').obj (F.obj V)) (𝟙 _)).symm.trans (by rw [Category.comp_id])

/-- The whole open-indexed pullback comparison, before any Scheme specialization. -/
def freeYonedaSheafPullbackNatIso :
    freeYonedaSheafFunctor R ⋙ pullback.{v} φ ≅ F ⋙ freeYonedaSheafFunctor R' :=
  NatIso.ofComponents (freeYonedaSheafPullbackIso R φ)
    (fun i => freeYonedaSheafPullbackIso_naturality R φ i)

end SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry TopologicalSpace

variable {X Y : Scheme.{u}} (p : Y ⟶ X)

/-- Actual pullback of an original open-free module is the original free module
on the inverse-image open. No flatness assumption is used. -/
def openFreePullbackIso (U : X.Opens) :
    (Scheme.Modules.pullback p).obj (openFree X U) ≅ openFree Y (p ⁻¹ᵁ U) :=
  SheafOfModules.freeYonedaSheafPullbackIso X.ringCatSheaf p.toRingCatSheafHom U

/-- The original open-free pullback comparison is natural in the entire open variable. -/
def openFreePullbackNatIso :
    openFreeFunctor X ⋙ Scheme.Modules.pullback p ≅
      Opens.map p.base ⋙ openFreeFunctor Y :=
  SheafOfModules.freeYonedaSheafPullbackNatIso X.ringCatSheaf p.toRingCatSheafHom

/-- Naturality retains the original covariant maps of open-free modules. -/
theorem openFreePullbackIso_naturality {U V : X.Opens} (i : U ⟶ V) :
    (Scheme.Modules.pullback p).map ((openFreeFunctor X).map i) ≫
        (openFreePullbackIso p V).hom =
      (openFreePullbackIso p U).hom ≫
        (openFreeFunctor Y).map ((Opens.map p.base).map i) :=
  SheafOfModules.freeYonedaSheafPullbackIso_naturality X.ringCatSheaf p.toRingCatSheafHom i

/-- The canonical comparison is normalized by the original pullback adjunction
and both original Hom/section equivalences, for every coefficient and morphism. -/
theorem openFreePullbackIso_homEquiv (U : X.Opens) (M : Y.Modules)
    (f : openFree Y (p ⁻¹ᵁ U) ⟶ M) :
    openFreeHomEquiv X U ((Scheme.Modules.pushforward p).obj M)
        ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _
          ((openFreePullbackIso p U).hom ≫ f)) =
      openFreeHomEquiv Y (p ⁻¹ᵁ U) M f :=
  SheafOfModules.freeYonedaSheafPullbackIso_homEquiv X.ringCatSheaf p.toRingCatSheafHom U M f

/-- The literal original universal section determines the generator comparison. -/
theorem openFreePullbackIso_generator (U : X.Opens) :
    openFreeHomEquiv X U ((Scheme.Modules.pushforward p).obj (openFree Y (p ⁻¹ᵁ U)))
        ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _
          (openFreePullbackIso p U).hom) =
      openFreeHomEquiv Y (p ⁻¹ᵁ U) (openFree Y (p ⁻¹ᵁ U)) (𝟙 _) := by
  simpa only [Category.comp_id] using
    openFreePullbackIso_homEquiv p U (openFree Y (p ⁻¹ᵁ U)) (𝟙 _)

end AlgebraicGeometry.Scheme.Modules
