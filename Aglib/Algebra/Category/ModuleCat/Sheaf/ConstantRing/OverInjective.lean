/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Over
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Pullback
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Injectives
public import Mathlib.Algebra.Category.ModuleCat.AB

/-!
# Injectives under the original constant-ring slice restriction

The actual module-valued slice restriction preserves injectives because its
original coproduct lower shriek is exact. The original constant-ring coefficient
equivalences transport this result to the existing ringed direct image. The
proved original constant-ring-over isomorphism then identifies this with native
ringed over-restriction. All comparisons retain their original maps; restriction
of arbitrary ringed sheaves is not asserted to preserve injectives.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v r w

namespace ModuleCat.Sheaf.ConstantRing

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
  (Λ : Type r) [Ring Λ]
  [HasWeakSheafify J RingCat.{r}] [HasWeakSheafify (J.over U) RingCat.{r}]
  [J.WEqualsLocallyBijective RingCat.{r}] [(J.over U).WEqualsLocallyBijective RingCat.{r}]
  [(J.over U).HasSheafCompose (CategoryTheory.forget RingCat.{r})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [(J.over U).HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [HasCoproducts.{v} (ModuleCat.{w} Λ)] [AB4OfSize.{v} (ModuleCat.{w} Λ)]
  [HasSheafify J (ModuleCat.{w} Λ)]

/-- Existing ringed direct image along the actual slice forgetful functor preserves injectives. -/
instance moduleDirectImage_over_preservesInjectiveObjects :
    (moduleDirectImage.{max u v, v, u, v, r, w}
      (Over.forget U) (J.over U) J Λ).PreservesInjectiveObjects where
  injective_obj {M} hM := by
    let := hM
    let : (moduleValuedDirectImage.{max u v, v, u, v, r, w}
        (Over.forget U) (J.over U) J Λ).PreservesInjectiveObjects :=
      CategoryTheory.Sheaf.SliceCohomology.overPullback_preservesInjectiveObjects
        J (ModuleCat.{w} Λ) U
    have h : Injective (((moduleSheafEquivalence J Λ).inverse ⋙
        moduleValuedDirectImage (Over.forget U) (J.over U) J Λ ⋙
          (moduleSheafEquivalence (J.over U) Λ).functor).obj M) := inferInstance
    exact Injective.of_iso ((moduleDirectImageTransportIso (Over.forget U) (J.over U) J Λ).app
      M).symm h

/-- Native over-restriction for the original constant ring preserves injectives. -/
instance overFunctor_preservesInjectiveObjects :
    (SheafOfModules.overFunctor.{w} (constantRing J Λ) U).PreservesInjectiveObjects where
  injective_obj {M} hM := by
    let := hM
    let e := overRingIso J U Λ
    let E₀ : Over U ≌ Over U := CategoryTheory.Equivalence.refl
    let : E₀.functor.IsContinuous (J.over U) (J.over U) := by
      change (𝟭 (Over U)).IsContinuous (J.over U) (J.over U)
      infer_instance
    let : E₀.inverse.IsContinuous (J.over U) (J.over U) := by
      change (𝟭 (Over U)).IsContinuous (J.over U) (J.over U)
      infer_instance
    let E : SheafOfModules.{w} ((constantRing J Λ).over U) ≌
        SheafOfModules.{w} (constantRing (J.over U) Λ) :=
      SheafOfModules.pushforwardPushforwardEquivalence
      E₀ e.hom e.inv
      (by
        ext V x
        change ((constantRing J Λ).over U).obj.map (𝟙 V) x =
          e.hom.hom.app V (e.inv.hom.app V x)
        rw [CategoryTheory.Functor.map_id]
        exact (congrArg (fun f : (constantRing J Λ).over U ⟶ (constantRing J Λ).over U =>
          f.hom.app V x) e.inv_hom_id).symm)
      (by
        ext V x
        change (constantRing (J.over U) Λ).obj.map (𝟙 V)
          (e.inv.hom.app V (e.hom.hom.app V x)) = x
        rw [CategoryTheory.Functor.map_id]
        exact congrArg (fun f : constantRing (J.over U) Λ ⟶ constantRing (J.over U) Λ =>
          f.hom.app V x) e.hom_inv_id)
    have hi : Injective ((moduleDirectImage.{max u v, v, u, v, r, w}
        (Over.forget U) (J.over U) J Λ).obj M) := inferInstance
    have he : E.functor = SheafOfModules.restrictScalars.{w} e.hom := rfl
    apply (E.map_injective_iff _).mp
    rw [he]
    exact hi

end ModuleCat.Sheaf.ConstantRing
