/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantCoefficients
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantLocalHom
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# Constant charts from an original locally bijective presentation

Sheafifying the actual constant-presheaf map gives its original isomorphism
onto the specified target sheaf. Its unit equation and naturality keep the
original map. This permits restriction of a chart's original unit before
recovering its constant-sheaf isomorphism; no second constant-sheaf model is
chosen.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe c h r m

namespace ModuleCat.Sheaf

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  {Λ : Type r} [Ring Λ]

attribute [local instance] hasSheafify

variable (M : ModuleCat.{max c h} Λ) (F : Sheaf J (ModuleCat.{max c h} Λ))
  (η : (Functor.const Cᵒᵖ).obj M ⟶ F.obj)
  [CategoryTheory.Presheaf.IsLocallySurjective J η]
  [CategoryTheory.Presheaf.IsLocallyInjective J η]

/-- Sheafifying the original locally bijective constant presentation gives its actual chart. -/
def constantPresentationIso : (constantSheaf J (ModuleCat.{max c h} Λ)).obj M ≅ F := by
  let : PreservesFilteredColimits (forget (ModuleCat.{max c h} Λ)) :=
    forget_preservesFilteredColimits Λ
  let : J.PreservesSheafification (forget (ModuleCat.{max c h} Λ)) :=
    GrothendieckTopology.instPreservesSheafification J (forget (ModuleCat.{max c h} Λ))
  have hmap : IsIso ((presheafToSheaf J (ModuleCat.{max c h} Λ)).map η) :=
    (J.W_iff η).mp (J.W_of_isLocallyBijective η)
  have hε : IsIso ((sheafificationAdjunction J (ModuleCat.{max c h} Λ)).counit.app F) :=
    inferInstance
  let a : (constantSheaf J (ModuleCat.{max c h} Λ)).obj M ⟶ F :=
    ((sheafificationAdjunction J (ModuleCat.{max c h} Λ)).homEquiv _ F).symm η
  have ha : IsIso a := by
    dsimp only [a]
    rw [Adjunction.homEquiv_counit]
    exact IsIso.comp_isIso' hmap hε
  exact @asIso _ _ _ _ a ha

/-- The chart map is the native sheafification-adjunction lift of the original presentation. -/
theorem constantPresentationIso_hom :
    (constantPresentationIso J M F η).hom =
      ((sheafificationAdjunction J (ModuleCat.{max c h} Λ)).homEquiv _ F).symm η := rfl

/-- The original constant-unit factorization determines the chart. -/
theorem constantPresentationIso_unit :
    constantUnit J M ≫ (constantPresentationIso J M F η).hom.hom = η :=
  toSheafify_sheafifyLift J η F.property

variable {M F η}

/-- The same unit factorization retains an already specified original constant chart. -/
theorem constantPresentationIso_eq_of_unit
    (e : (constantSheaf J (ModuleCat.{max c h} Λ)).obj M ≅ F)
    (he : constantUnit J M ≫ e.hom.hom = η) :
    constantPresentationIso J M F η = e := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  apply sheafify_hom_ext J _ _ F.property
  exact (constantPresentationIso_unit J M F η).trans he.symm


set_option backward.isDefEq.respectTransparency false in
/-- The construction retains the original coefficient square on whole sheaf morphisms. -/
theorem constantPresentationIso_naturality
    {M' : ModuleCat.{max c h} Λ} {F' : Sheaf J (ModuleCat.{max c h} Λ)}
    (θ : (Functor.const Cᵒᵖ).obj M' ⟶ F'.obj)
    [CategoryTheory.Presheaf.IsLocallySurjective J θ]
    [CategoryTheory.Presheaf.IsLocallyInjective J θ]
    (a : M ⟶ M') (b : F ⟶ F')
    (h : (Functor.const Cᵒᵖ).map a ≫ θ = η ≫ b.hom) :
    (constantSheaf J (ModuleCat.{max c h} Λ)).map a ≫
        (constantPresentationIso J M' F' θ).hom =
      (constantPresentationIso J M F η).hom ≫ b := by
  apply ObjectProperty.hom_ext
  apply sheafify_hom_ext J _ _ F'.property
  change constantUnit J M ≫ sheafifyMap J ((Functor.const Cᵒᵖ).map a) ≫
      (constantPresentationIso J M' F' θ).hom.hom =
    constantUnit J M ≫ (constantPresentationIso J M F η).hom.hom ≫ b.hom
  rw [← toSheafify_naturality_assoc, constantPresentationIso_unit,
    ← Category.assoc, constantPresentationIso_unit]
  exact h

end ModuleCat.Sheaf

namespace ModuleCat.Sheaf

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  {Λ : Type r} [Ring Λ] (F : Sheaf J (ModuleCat.{m} Λ)) (M : ModuleCat.{m} Λ)

/-- Restrict the original constant presentation by the actual map of slice categories. -/
def overPresentationRestrict {U V : C} (f : V ⟶ U)
    (η : (Functor.const (Over U)ᵒᵖ).obj M ⟶ (Over.forget U).op ⋙ F.obj) :
    (Functor.const (Over V)ᵒᵖ).obj M ⟶ (Over.forget V).op ⋙ F.obj :=
  Functor.whiskerLeft (Over.map f).op η

/-- The original restriction is the identity for an identity base arrow. -/
@[simp]
theorem overPresentationRestrict_id {U : C}
    (η : (Functor.const (Over U)ᵒᵖ).obj M ⟶ (Over.forget U).op ⋙ F.obj) :
    overPresentationRestrict J F M (𝟙 U) η = η := by
  apply NatTrans.ext
  funext W
  change η.app (op (Over.mk (W.unop.hom ≫ 𝟙 U))) = η.app W
  rw [Category.comp_id]
  rfl

/-- Original chart restrictions compose in the original order. -/
theorem overPresentationRestrict_comp {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (η : (Functor.const (Over U)ᵒᵖ).obj M ⟶ (Over.forget U).op ⋙ F.obj) :
    overPresentationRestrict J F M g (overPresentationRestrict J F M f η) =
      overPresentationRestrict J F M (g ≫ f) η := by
  apply NatTrans.ext
  funext T
  change η.app (op (Over.mk ((T.unop.hom ≫ g) ≫ f))) =
    η.app (op (Over.mk (T.unop.hom ≫ (g ≫ f))))
  rw [Category.assoc]

/-- The restricted terminal component is the original component at the specified slice object. -/
theorem overPresentationRestrict_terminal {U V : C} (f : V ⟶ U)
    (η : (Functor.const (Over U)ᵒᵖ).obj M ⟶ (Over.forget U).op ⋙ F.obj) :
    (overPresentationRestrict J F M f η).app (op (Over.mk (𝟙 V))) = η.app (op (Over.mk f)) := by
  change η.app (op (Over.mk ((𝟙 V) ≫ f))) = _
  rw [Category.id_comp]

/-- Actual slice restriction preserves local surjectivity of the original presentation. -/
instance overPresentationRestrict_isLocallySurjective {U V : C} (f : V ⟶ U)
    (η : (Functor.const (Over U)ᵒᵖ).obj M ⟶
      ((J.overPullback (ModuleCat.{m} Λ) U).obj F).obj)
    [CategoryTheory.Presheaf.IsLocallySurjective (J.over U) η] :
    CategoryTheory.Presheaf.IsLocallySurjective (J.over V)
      (G := ((J.overPullback (ModuleCat.{m} Λ) V).obj F).obj)
      (overPresentationRestrict J F M f η) :=
  CategoryTheory.Presheaf.isLocallySurjective_whisker
    (J.over V) (J.over U) (Over.map f) η

/-- Actual slice restriction preserves local injectivity of the original presentation. -/
instance overPresentationRestrict_isLocallyInjective {U V : C} (f : V ⟶ U)
    (η : (Functor.const (Over U)ᵒᵖ).obj M ⟶
      ((J.overPullback (ModuleCat.{m} Λ) U).obj F).obj)
    [CategoryTheory.Presheaf.IsLocallyInjective (J.over U) η] :
    CategoryTheory.Presheaf.IsLocallyInjective (J.over V)
      (F₂ := ((J.overPullback (ModuleCat.{m} Λ) V).obj F).obj)
      (overPresentationRestrict J F M f η) :=
  CategoryTheory.Presheaf.isLocallyInjective_whisker
    (J.over V) (J.over U) (Over.map f) η

end ModuleCat.Sheaf
