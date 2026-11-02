/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.InternalHomConstant
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantPresentation

/-!
# Original internal Hom through a locally bijective constant presentation

Recover the actual slice chart from its original constant-presheaf map and
use the one slice-frame Hom comparison. Its forward formula is the original
presentation followed by the same slice-linear transformation. This version
permits restriction of the original presentation without introducing another
constant-sheaf or internal-Hom model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe c h r

namespace ModuleCat.Sheaf.ConstantRing

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  (Λ : Type r) [CommRing Λ] (U : C)
  [HasWeakSheafify J RingCat.{r}] [HasWeakSheafify (J.over U) RingCat.{r}]
  [J.WEqualsLocallyBijective RingCat.{r}] [(J.over U).WEqualsLocallyBijective RingCat.{r}]
  [J.HasSheafCompose (CategoryTheory.forget RingCat.{r})]
  [(J.over U).HasSheafCompose (CategoryTheory.forget RingCat.{r})]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasWeakSheafify J AddCommGrpCat.{max c h}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{max c h}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c h}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c h}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{max c h} Λ) AddCommGrpCat.{max c h})]
  [(J.over U).HasSheafCompose (forget₂ (ModuleCat.{max c h} Λ) AddCommGrpCat.{max c h})]

attribute [local instance] ModuleCat.Sheaf.hasSheafify

variable (M : ModuleSheaf.{c, h, r, max c h} J Λ) (M₀ : ModuleCat.{max c h} Λ)
  (η : (Functor.const (Over U)ᵒᵖ).obj M₀ ⟶
    ((J.overPullback (ModuleCat.{max c h} Λ) U).obj
      ((moduleSheafEquivalence J Λ).inverse.obj M)).obj)
  [CategoryTheory.Presheaf.IsLocallySurjective (J.over U) η]
  [CategoryTheory.Presheaf.IsLocallyInjective (J.over U) η]

/-- The whole Hom comparison uses the original presentation in the existing slice-frame map. -/
def presentationHomNatIso :
    SheafOfModules.overFunctor (constantRing J Λ) U ⋙
        preadditiveCoyoneda.obj (op (M.over U)) ≅
      (moduleSheafEquivalence J Λ).inverse ⋙
        (sheafSections J (ModuleCat.{max c h} Λ)).obj (op U) ⋙
          preadditiveCoyoneda.obj (op M₀) :=
  sliceFrameHomNatIso J Λ U M M₀
    (ModuleCat.Sheaf.constantPresentationIso (J.over U) M₀ _ η)

/-- Original internal-Hom sections through the one whole presentation comparison. -/
def presentationSectionAddEquiv (N : ModuleSheaf.{c, h, r, max c h} J Λ) :
    (SheafOfModules.InternalHom.sheaf (commutativeSheaf J Λ) M N).val.obj (op U) ≃+
      (M₀ ⟶ ((moduleSheafEquivalence J Λ).inverse.obj N).obj.obj (op U)) :=
  (SheafOfModules.InternalHom.sectionHomAddEquiv (commutativeSheaf J Λ) M N U).trans
    ((presentationHomNatIso J Λ U M M₀ η).app N).addCommGroupIsoToAddEquiv

-- Retain the original constant-ring parent through the commutative section view.
set_option backward.isDefEq.respectTransparency false in
/-- The forward map keeps the original presentation at the terminal slice object. -/
theorem presentationSectionAddEquiv_apply (N : ModuleSheaf.{c, h, r, max c h} J Λ)
    (s : (SheafOfModules.InternalHom.sheaf (commutativeSheaf J Λ) M N).val.obj (op U)) :
    presentationSectionAddEquiv J Λ U M M₀ η N s =
      η.app (op (Over.mk (𝟙 U))) ≫
        (sectionValuedHomAddEquiv J Λ U M N s).hom.app (op (Over.mk (𝟙 U))) := by
  change sliceFrameSectionAddEquiv J Λ U M N M₀
    (ModuleCat.Sheaf.constantPresentationIso (J.over U) M₀ _ η) s = _
  rw [sliceFrameSectionAddEquiv_apply]
  have hη := congrArg (fun t => t.app (op (Over.mk (𝟙 U))))
    (ModuleCat.Sheaf.constantPresentationIso_unit (J.over U) M₀ _ η)
  dsimp only [NatTrans.comp_app] at hη
  rw [← Category.assoc, hη]

/-- The original slice-linear function is evaluated on the original chart-unit value. -/
theorem presentationSectionAddEquiv_apply_apply
    (N : ModuleSheaf.{c, h, r, max c h} J Λ)
    (s : (SheafOfModules.InternalHom.sheaf (commutativeSheaf J Λ) M N).val.obj (op U))
    (x : M₀) :
    presentationSectionAddEquiv J Λ U M M₀ η N s x =
      s.val.app (op (Over.mk (𝟙 U))) (η.app (op (Over.mk (𝟙 U))) x) := by
  rw [presentationSectionAddEquiv_apply]
  rfl

/-- The original target coefficient map is preserved by the presentation comparison. -/
theorem presentationSectionAddEquiv_postcompose
    {N N' : ModuleSheaf.{c, h, r, max c h} J Λ} (b : N ⟶ N')
    (s : (SheafOfModules.InternalHom.sheaf (commutativeSheaf J Λ) M N).val.obj (op U)) :
    presentationSectionAddEquiv J Λ U M M₀ η N'
        ((SheafOfModules.InternalHom.map (commutativeSheaf J Λ) (𝟙 M) b).val.app (op U) s) =
      presentationSectionAddEquiv J Λ U M M₀ η N s ≫
        ((moduleSheafEquivalence J Λ).inverse.map b).hom.app (op U) := by
  rw [presentationSectionAddEquiv_apply, presentationSectionAddEquiv_apply,
    sectionValuedHomAddEquiv_postcompose]
  change η.app (op (Over.mk (𝟙 U))) ≫
      ((sectionValuedHomAddEquiv J Λ U M N s).hom.app (op (Over.mk (𝟙 U))) ≫
        ((moduleSheafEquivalence J Λ).inverse.map b).hom.app (op U)) = _
  exact (Category.assoc _ _ _).symm

variable {V : C}
  [HasWeakSheafify (J.over V) RingCat.{r}]
  [(J.over V).WEqualsLocallyBijective RingCat.{r}]
  [(J.over V).HasSheafCompose (CategoryTheory.forget RingCat.{r})]
  [HasWeakSheafify (J.over V) AddCommGrpCat.{max c h}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c h}]
  [(J.over V).HasSheafCompose (forget₂ (ModuleCat.{max c h} Λ) AddCommGrpCat.{max c h})]

-- Use the same original ring parent in both section values.
set_option backward.isDefEq.respectTransparency false in
/-- Actual restriction of sections agrees with restriction of the original chart presentation. -/
theorem presentationSectionAddEquiv_restrict (f : V ⟶ U)
    (N : ModuleSheaf.{c, h, r, max c h} J Λ)
    (s : (SheafOfModules.InternalHom.sheaf (commutativeSheaf J Λ) M N).val.obj (op U)) :
    presentationSectionAddEquiv J Λ V M M₀
        (ModuleCat.Sheaf.overPresentationRestrict J
          ((moduleSheafEquivalence J Λ).inverse.obj M) M₀ f η) N
        ((SheafOfModules.InternalHom.sheaf (commutativeSheaf J Λ) M N).val.map f.op s) =
      presentationSectionAddEquiv J Λ U M M₀ η N s ≫
        ((moduleSheafEquivalence J Λ).inverse.obj N).obj.map f.op := by
  ext x
  change presentationSectionAddEquiv J Λ V M M₀
      (ModuleCat.Sheaf.overPresentationRestrict J
        ((moduleSheafEquivalence J Λ).inverse.obj M) M₀ f η) N
      ((SheafOfModules.InternalHom.sheaf (commutativeSheaf J Λ) M N).val.map f.op s) x =
    ((moduleSheafEquivalence J Λ).inverse.obj N).obj.map f.op
      (presentationSectionAddEquiv J Λ U M M₀ η N s x)
  rw [presentationSectionAddEquiv_apply_apply, presentationSectionAddEquiv_apply_apply,
    ModuleCat.Sheaf.overPresentationRestrict_terminal]
  change s.val.app (op (Over.mk ((𝟙 V) ≫ f))) (η.app (op (Over.mk f)) x) =
    N.val.map f.op (s.val.app (op (Over.mk (𝟙 U))) (η.app (op (Over.mk (𝟙 U))) x))
  rw [Category.id_comp]
  let a : Over.mk f ⟶ Over.mk (𝟙 U) := Over.homMk f (by simp)
  have hη := NatTrans.naturality_apply η a.op x
  change η.app (op (Over.mk f)) x =
    M.val.map f.op (η.app (op (Over.mk (𝟙 U))) x) at hη
  have hs := NatTrans.naturality_apply s.val a.op (η.app (op (Over.mk (𝟙 U))) x)
  change s.val.app (op (Over.mk f)) (M.val.map f.op (η.app (op (Over.mk (𝟙 U))) x)) =
    N.val.map f.op (s.val.app (op (Over.mk (𝟙 U))) (η.app (op (Over.mk (𝟙 U))) x)) at hs
  exact (congrArg (fun z => s.val.app (op (Over.mk f)) z) hη).trans hs

end ModuleCat.Sheaf.ConstantRing
