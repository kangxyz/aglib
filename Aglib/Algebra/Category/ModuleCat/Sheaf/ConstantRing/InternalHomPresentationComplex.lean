/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.InternalHomPresentation
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Additive
public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.Additive
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
# Whole presheaf and complex comparison on an actual constant presentation

Restriction and coefficient coherence of the original section comparison
assemble a whole presheaf-valued natural isomorphism. The native complex-map
constructor then retains the same differential maps in every degree. The
right-hand view is the original module-valued restricted complex followed by
actual Hom from the chart module; it is not another cohomology or resolution.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe c h

namespace ModuleCat.Sheaf.ConstantRing

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  (Λ : Type (max c h)) [CommRing Λ]
  [HasWeakSheafify J RingCat.{max c h}] [J.WEqualsLocallyBijective RingCat.{max c h}]
  [J.HasSheafCompose (CategoryTheory.forget RingCat.{max c h})]
  [J.HasSheafCompose (forget₂ CommRingCat.{max c h} RingCat.{max c h})]
  [HasWeakSheafify J AddCommGrpCat.{max c h}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c h}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{max c h} Λ) AddCommGrpCat.{max c h})]
  [∀ V : C, HasWeakSheafify (J.over V) RingCat.{max c h}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective RingCat.{max c h}]
  [∀ V : C, (J.over V).HasSheafCompose (CategoryTheory.forget RingCat.{max c h})]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max c h}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c h}]
  [∀ V : C, (J.over V).HasSheafCompose
    (forget₂ (ModuleCat.{max c h} Λ) AddCommGrpCat.{max c h})]
  (U : C)

/-- The original internal Hom, with its original additive presheaf restricted to this slice. -/
abbrev internalHomOverPresheafFunctor
    (M : ModuleSheaf.{c, h, max c h, max c h} J Λ) :
    ModuleSheaf.{c, h, max c h, max c h} J Λ ⥤ (Over U)ᵒᵖ ⥤ AddCommGrpCat.{max c h} :=
  SheafOfModules.InternalHom.homFunctor.{c, h, 0} (commutativeSheaf J Λ) M ⋙
    SheafOfModules.toSheaf (constantRing J Λ) ⋙ sheafToPresheaf J AddCommGrpCat.{max c h} ⋙
      (Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ AddCommGrpCat.{max c h}).obj (Over.forget U).op

/-- Original module-valued restriction, followed by actual Hom from the specified chart module. -/
abbrev valuedHomOverPresheafFunctor (M₀ : ModuleCat.{max c h} Λ) :
    ModuleSheaf.{c, h, max c h, max c h} J Λ ⥤ (Over U)ᵒᵖ ⥤ AddCommGrpCat.{max c h} :=
  (moduleSheafEquivalence J Λ).inverse ⋙ J.overPullback (ModuleCat.{max c h} Λ) U ⋙
    sheafToPresheaf (J.over U) (ModuleCat.{max c h} Λ) ⋙
      (Functor.whiskeringRight (Over U)ᵒᵖ (ModuleCat.{max c h} Λ) AddCommGrpCat.{max c h}).obj
        (preadditiveCoyoneda.obj (op M₀))

-- The commutative lift has the identical original RingCat parent.
set_option backward.isDefEq.respectTransparency false in
/-- The original restricted internal-Hom presheaf functor is additive. -/
instance internalHomOverPresheafFunctor_additive
    (M : ModuleSheaf.{c, h, max c h, max c h} J Λ) :
    (internalHomOverPresheafFunctor J Λ U M).Additive where
  map_add {X Y f g} := by
    apply NatTrans.ext
    funext V
    ext s
    exact congrArg (fun a : (SheafOfModules.InternalHom.homFunctor.{c, h, 0}
        (commutativeSheaf J Λ) M).obj X ⟶
        (SheafOfModules.InternalHom.homFunctor.{c, h, 0} (commutativeSheaf J Λ) M).obj Y =>
        a.val.app (op V.unop.left) s)
      ((SheafOfModules.InternalHom.homFunctor.{c, h, 0}
        (commutativeSheaf J Λ) M).map_add (f := f) (g := g))

/-- The original module-valued Hom presheaf functor is additive. -/
instance valuedHomOverPresheafFunctor_additive (M₀ : ModuleCat.{max c h} Λ) :
    (valuedHomOverPresheafFunctor J Λ U M₀).Additive := by
  dsimp only [valuedHomOverPresheafFunctor, GrothendieckTopology.overPullback,
    Functor.sheafPushforwardContinuous]
  infer_instance

variable (M : ModuleSheaf.{c, h, max c h, max c h} J Λ) (M₀ : ModuleCat.{max c h} Λ)
  (η : (Functor.const (Over U)ᵒᵖ).obj M₀ ⟶
    ((J.overPullback (ModuleCat.{max c h} Λ) U).obj
      ((moduleSheafEquivalence J Λ).inverse.obj M)).obj)
  [CategoryTheory.Presheaf.IsLocallySurjective (J.over U) η]
  [CategoryTheory.Presheaf.IsLocallyInjective (J.over U) η]

private theorem presentationSectionAddEquiv_congr {V : C}
    (η₁ η₂ : (Functor.const (Over V)ᵒᵖ).obj M₀ ⟶
      ((J.overPullback (ModuleCat.{max c h} Λ) V).obj
        ((moduleSheafEquivalence J Λ).inverse.obj M)).obj)
    [CategoryTheory.Presheaf.IsLocallySurjective (J.over V) η₁]
    [CategoryTheory.Presheaf.IsLocallyInjective (J.over V) η₁]
    [CategoryTheory.Presheaf.IsLocallySurjective (J.over V) η₂]
    [CategoryTheory.Presheaf.IsLocallyInjective (J.over V) η₂]
    (hη : η₁ = η₂) (N : ModuleSheaf.{c, h, max c h, max c h} J Λ) :
    presentationSectionAddEquiv J Λ V M M₀ η₁ N =
      presentationSectionAddEquiv J Λ V M M₀ η₂ N := by
  subst η₂
  rfl

include η in
-- Retain the identical original ring parent in the whole presheaf comparison.
set_option backward.isDefEq.respectTransparency false in
/-- The original chart comparison is a natural isomorphism of whole presheaf-valued functors. -/
def presentationPresheafNatIso :
    internalHomOverPresheafFunctor J Λ U M ≅ valuedHomOverPresheafFunctor J Λ U M₀ :=
  NatIso.ofComponents (fun N => NatIso.ofComponents
    (fun V => (presentationSectionAddEquiv J Λ V.unop.left M M₀
      (ModuleCat.Sheaf.overPresentationRestrict J
        ((moduleSheafEquivalence J Λ).inverse.obj M) M₀ V.unop.hom η) N).toAddCommGrpIso)
    (fun {V W} f => by
      ext s
      have h := presentationSectionAddEquiv_restrict J Λ V.unop.left M M₀
        (ModuleCat.Sheaf.overPresentationRestrict J
          ((moduleSheafEquivalence J Λ).inverse.obj M) M₀ V.unop.hom η)
        f.unop.left N s
      have hη := (ModuleCat.Sheaf.overPresentationRestrict_comp J
        ((moduleSheafEquivalence J Λ).inverse.obj M) M₀ V.unop.hom f.unop.left η).trans
        (congrArg (fun a : W.unop.left ⟶ U => ModuleCat.Sheaf.overPresentationRestrict J
          ((moduleSheafEquivalence J Λ).inverse.obj M) M₀ a η) (Over.w f.unop))
      rw [presentationSectionAddEquiv_congr J Λ M M₀ _ _ hη N] at h
      change presentationSectionAddEquiv J Λ W.unop.left M M₀
          (ModuleCat.Sheaf.overPresentationRestrict J
            ((moduleSheafEquivalence J Λ).inverse.obj M) M₀ W.unop.hom η) N
          ((SheafOfModules.InternalHom.sheaf (commutativeSheaf J Λ) M N).val.map
            f.unop.left.op s) = _
      exact h))
    (fun {N N'} b => by
      apply NatTrans.ext
      funext V
      ext s
      change presentationSectionAddEquiv J Λ V.unop.left M M₀
          (ModuleCat.Sheaf.overPresentationRestrict J
            ((moduleSheafEquivalence J Λ).inverse.obj M) M₀ V.unop.hom η) N'
          ((SheafOfModules.InternalHom.map (commutativeSheaf J Λ) (𝟙 M) b).val.app
            (op V.unop.left) s) = _
      exact presentationSectionAddEquiv_postcompose J Λ V.unop.left M M₀
        (ModuleCat.Sheaf.overPresentationRestrict J
          ((moduleSheafEquivalence J Λ).inverse.obj M) M₀ V.unop.hom η) b s)

/-- A component of the whole map is the same original section comparison. -/
theorem presentationPresheafNatIso_hom_app_app_apply
    (N : ModuleSheaf.{c, h, max c h, max c h} J Λ) (V : (Over U)ᵒᵖ)
    (s : (SheafOfModules.InternalHom.sheaf (commutativeSheaf J Λ) M N).val.obj
      (op V.unop.left)) :
    ((presentationPresheafNatIso J Λ U M M₀ η).hom.app N).app V s =
      presentationSectionAddEquiv J Λ V.unop.left M M₀
        (ModuleCat.Sheaf.overPresentationRestrict J
          ((moduleSheafEquivalence J Λ).inverse.obj M) M₀ V.unop.hom η) N s := rfl

/-- Native mapping of the whole comparison gives the original complex isomorphism. -/
def presentationComplexIso {ι : Type*} (shape : ComplexShape ι)
    (I : HomologicalComplex (ModuleSheaf.{c, h, max c h, max c h} J Λ) shape) :
    ((internalHomOverPresheafFunctor J Λ U M).mapHomologicalComplex shape).obj I ≅
      ((valuedHomOverPresheafFunctor J Λ U M₀).mapHomologicalComplex shape).obj I :=
  (NatIso.mapHomologicalComplex (presentationPresheafNatIso J Λ U M M₀ η) shape).app I

/-- Every degree of the native complex map retains the original chart section function. -/
theorem presentationComplexIso_hom_f_app_apply {ι : Type*} (shape : ComplexShape ι)
    (I : HomologicalComplex (ModuleSheaf.{c, h, max c h, max c h} J Λ) shape)
    (i : ι) (V : (Over U)ᵒᵖ)
    (s : (SheafOfModules.InternalHom.sheaf (commutativeSheaf J Λ) M (I.X i)).val.obj
      (op V.unop.left)) :
    ((presentationComplexIso J Λ U M M₀ η shape I).hom.f i).app V s =
      presentationSectionAddEquiv J Λ V.unop.left M M₀
        (ModuleCat.Sheaf.overPresentationRestrict J
          ((moduleSheafEquivalence J Λ).inverse.obj M) M₀ V.unop.hom η) (I.X i) s := rfl

end ModuleCat.Sheaf.ConstantRing
