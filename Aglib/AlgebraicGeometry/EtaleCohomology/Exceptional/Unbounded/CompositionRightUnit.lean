/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionLeftUnit
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionAssociativity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionArrowComparison
public import Aglib.CategoryTheory.Functor.CompositionIdentityNormalization
public import Aglib.CategoryTheory.Functor.RightUnitOfAssociativity

/-! # The original right unit from actual associativity and the original left unit -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wF wI wFI
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
  [CompactSpace Y] [QuasiSeparatedSpace Y] [IsSeparated f] [LocallyOfFiniteType f]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [fModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wF} (ModuleSheaf C.Xbar Λ)]
  [idModels : ∀ C : Hom.DenseCompactification (𝟙 Y),
    HasDerivedCategory.{wI} (ModuleSheaf C.Xbar Λ)]
  [fiModels : ∀ C : Hom.DenseCompactification (f ≫ 𝟙 Y),
    HasDerivedCategory.{wFI} (ModuleSheaf C.Xbar Λ)]
  (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The right unit is forced by the proved original associativity, its original
arrow-comparison squares, and the proved left identity unit. -/
theorem moduleExceptionalDirectImageUnboundedCompIso_comp_id :
    moduleExceptionalDirectImageUnboundedCompIso (firstModels := fModels)
        (secondModels := idModels) (compositeModels := fiModels) f (𝟙 Y) Λ N hN hΛ ≪≫
      moduleExceptionalDirectImageUnboundedCongr Λ hX hY (Category.comp_id f)
        fiModels fModels N hN hΛ =
    Functor.isoWhiskerLeft ((@moduleExceptionalDirectImageUnbounded _ _ _ _ f _ _ _ Λ _ _ _
      (fModels (moduleExceptionalCompactification f))))
        (moduleExceptionalDirectImageUnboundedIdIso
          (middleModels := idModels) Y Λ N hN hΛ) ≪≫
      Functor.rightUnitor
        ((@moduleExceptionalDirectImageUnbounded _ _ _ _ f _ _ _ Λ _ _ _ (fModels
          (moduleExceptionalCompactification f)))) := by
  let eL : (f ≫ 𝟙 Y) ≫ 𝟙 Y = f :=
    (Category.comp_id (f ≫ 𝟙 Y)).trans (Category.comp_id f)
  let eR : f ≫ (𝟙 Y ≫ 𝟙 Y) = f :=
    (congrArg (fun k => f ≫ k) (Category.id_comp (𝟙 Y))).trans (Category.comp_id f)
  let iiModels : ∀ C : Hom.DenseCompactification (𝟙 Y ≫ 𝟙 Y),
      HasDerivedCategory.{wI} (ModuleSheaf C.Xbar Λ) := fun C =>
    idModels (Hom.DenseCompactification.ofArrowEq (Category.id_comp (𝟙 Y)) C)
  let leftModels : ∀ C : Hom.DenseCompactification ((f ≫ 𝟙 Y) ≫ 𝟙 Y),
      HasDerivedCategory.{wF} (ModuleSheaf C.Xbar Λ) := fun C =>
    fModels (Hom.DenseCompactification.ofArrowEq eL C)
  let rightModels : ∀ C : Hom.DenseCompactification (f ≫ (𝟙 Y ≫ 𝟙 Y)),
      HasDerivedCategory.{wF} (ModuleSheaf C.Xbar Λ) := fun C =>
    fModels (Hom.DenseCompactification.ofArrowEq eR C)
  let F := (@moduleExceptionalDirectImageUnbounded _ _ _ _ f _ _ _ Λ _ _ _ (fModels
    (moduleExceptionalCompactification f)))
  let Q := (@moduleExceptionalDirectImageUnbounded _ _ _ _ (𝟙 Y) _ _ _ Λ _ _ _ (idModels
    (moduleExceptionalCompactification (𝟙 Y))))
  let a := moduleExceptionalDirectImageUnboundedCompIso (firstModels := fModels)
    (secondModels := idModels) (compositeModels := fiModels) f (𝟙 Y) Λ N hN hΛ
  let b := moduleExceptionalDirectImageUnboundedCompIso (firstModels := fiModels)
    (secondModels := idModels) (compositeModels := leftModels) (f ≫ 𝟙 Y) (𝟙 Y) Λ N hN hΛ
  let c := moduleExceptionalDirectImageUnboundedCompIso (firstModels := idModels)
    (secondModels := idModels) (compositeModels := iiModels) (𝟙 Y) (𝟙 Y) Λ N hN hΛ
  let d := moduleExceptionalDirectImageUnboundedCompIso (firstModels := fModels)
    (secondModels := iiModels) (compositeModels := rightModels) f (𝟙 Y ≫ 𝟙 Y) Λ N hN hΛ
  let e := moduleExceptionalDirectImageUnboundedCongr Λ hX hY (Category.assoc f (𝟙 Y) (𝟙 Y))
    leftModels rightModels N hN hΛ
  let u := moduleExceptionalDirectImageUnboundedCongr Λ hX hY (Category.comp_id f)
    fiModels fModels N hN hΛ
  let v := moduleExceptionalDirectImageUnboundedCongr Λ hY hY (Category.id_comp (𝟙 Y))
    iiModels idModels N hN hΛ
  let l := moduleExceptionalDirectImageUnboundedCongr Λ hX hY eL leftModels fModels N hN hΛ
  let t := moduleExceptionalDirectImageUnboundedCongr Λ hX hY eR rightModels fModels N hN hΛ
  have hb : b ≪≫ l = Functor.isoWhiskerRight u Q ≪≫ a ≪≫ u := by
    let ef := congrArg (fun k => k ≫ 𝟙 Y) (Category.comp_id f)
    let s := moduleExceptionalDirectImageUnboundedCongr Λ hX hY ef
      leftModels fiModels N hN hΛ
    have hs : Functor.isoWhiskerRight u Q ≪≫ a = b ≪≫ s := by
      simpa only [moduleExceptionalDirectImageUnboundedCongr_refl_self,
        compositionPairIso_refl_right] using
        (moduleExceptionalDirectImageUnboundedCompIso_congr Λ fiModels fModels
          idModels idModels leftModels fiModels N hN hΛ (Category.comp_id f) rfl ef)
    have hc : s ≪≫ u = l :=
      moduleExceptionalDirectImageUnboundedCongr_trans Λ hX hY ef (Category.comp_id f)
        leftModels fiModels fModels N hN hΛ
    calc
      b ≪≫ l = b ≪≫ (s ≪≫ u) := congrArg (fun z => b ≪≫ z) hc.symm
      _ = (b ≪≫ s) ≪≫ u := (Iso.trans_assoc _ _ _).symm
      _ = (Functor.isoWhiskerRight u Q ≪≫ a) ≪≫ u :=
        congrArg (fun z => z ≪≫ u) hs.symm
      _ = _ := Iso.trans_assoc _ _ _
  have hd : d ≪≫ t = Functor.isoWhiskerLeft F v ≪≫ a ≪≫ u := by
    let ef := congrArg (fun k => f ≫ k) (Category.id_comp (𝟙 Y))
    let s := moduleExceptionalDirectImageUnboundedCongr Λ hX hY ef
      rightModels fiModels N hN hΛ
    have hs : Functor.isoWhiskerLeft F v ≪≫ a = d ≪≫ s := by
      simpa only [moduleExceptionalDirectImageUnboundedCongr_refl_self,
        compositionPairIso_refl_left] using
        (moduleExceptionalDirectImageUnboundedCompIso_congr Λ fModels fModels
          iiModels idModels rightModels fiModels N hN hΛ rfl (Category.id_comp (𝟙 Y)) ef)
    have hc : s ≪≫ u = t :=
      moduleExceptionalDirectImageUnboundedCongr_trans Λ hX hY ef (Category.comp_id f)
        rightModels fiModels fModels N hN hΛ
    calc
      d ≪≫ t = d ≪≫ (s ≪≫ u) := congrArg (fun z => d ≪≫ z) hc.symm
      _ = (d ≪≫ s) ≪≫ u := (Iso.trans_assoc _ _ _).symm
      _ = (Functor.isoWhiskerLeft F v ≪≫ a) ≪≫ u :=
        congrArg (fun z => z ≪≫ u) hs.symm
      _ = _ := Iso.trans_assoc _ _ _
  have he : e ≪≫ t = l :=
    moduleExceptionalDirectImageUnboundedCongr_trans Λ hX hY
      (Category.assoc f (𝟙 Y) (𝟙 Y)) eR leftModels rightModels fModels N hN hΛ
  have ha : Functor.isoWhiskerRight a Q ≪≫ b ≪≫ e =
      Functor.associator F Q Q ≪≫ Functor.isoWhiskerLeft F c ≪≫ d :=
    moduleExceptionalDirectImageUnboundedCompIso_assoc (fModels := fModels)
      (gModels := idModels) (hModels := idModels) (fgModels := fiModels)
      (ghModels := iiModels) (leftModels := leftModels) (rightModels := rightModels)
      f (𝟙 Y) (𝟙 Y) Λ N hN hΛ
  exact rightUnit_of_associativity_leftUnit F Q
    (moduleExceptionalDirectImageUnboundedIdIso (middleModels := idModels) Y Λ N hN hΛ)
    (a ≪≫ u) (c ≪≫ v)
    (compositionAssociativity_normalize_identity a b c d e u v l t hb hd he ha)
    (moduleExceptionalDirectImageUnboundedCompIso_id_comp (firstModels := idModels)
      (targetModels := idModels) (compositeModels := iiModels) (𝟙 Y) Λ N hN hΛ)

end AlgebraicGeometry.Scheme.EtaleCohomology
