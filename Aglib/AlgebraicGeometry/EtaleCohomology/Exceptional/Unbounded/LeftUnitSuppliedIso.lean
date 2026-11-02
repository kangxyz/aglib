/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.LeftUnitSupplied
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.LeftUnitTotalComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.UnitModelRefinement

/-! # The actual supplied unbounded left-unit isomorphism triangle -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

attribute [local instance] hasSheafifyLarge
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard
universe u wX wY wA wB wD
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [firstModels : ∀ E : Hom.DenseCompactification (𝟙 X),
    HasDerivedCategory.{wA} (ModuleSheaf E.Xbar Λ)]
  [targetModels : ∀ E : Hom.DenseCompactification f,
    HasDerivedCategory.{wD} (ModuleSheaf E.Xbar Λ)]
  [compositeModels : ∀ E : Hom.DenseCompactification ((𝟙 X) ≫ f),
    HasDerivedCategory.{wB} (ModuleSheaf E.Xbar Λ)]
  (C : Hom.DenseCompactification f)
  (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The category structure for the specified derived-category model. -/
local instance leftUnitSuppliedIsoTotalCategory : Category.{wB}
    (@DerivedCategory (ModuleSheaf C.Xbar Λ) inferInstance inferInstance
      (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite)) :=
  @instCategoryDerivedCategory (ModuleSheaf C.Xbar Λ) inferInstance inferInstance
    (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite)
/-- The category structure for the specified derived-category model. -/
local instance leftUnitSuppliedIsoTargetCategory : Category.{wD}
    (@DerivedCategory (ModuleSheaf C.Xbar Λ) inferInstance inferInstance (targetModels C)) :=
  @instCategoryDerivedCategory (ModuleSheaf C.Xbar Λ) inferInstance inferInstance (targetModels C)

/-- The original first-refinement transition. -/
abbrev moduleUnboundedLeftUnitFirstIso :=
  moduleUnboundedCompactificationSingleTransitionIso (hX := hX) (hS := hX) Λ
    (Hom.CompactifiedComposition.leftUnitFirstRefinement C)
    (firstModels (Hom.CompactifiedComposition.leftUnit C).first) hX N hN hΛ

/-- The original total-refinement transition retains both independent middle models. -/
abbrev moduleUnboundedLeftUnitTotalIso :=
  moduleUnboundedCompactificationSingleTransitionIso (hX := hX) (hS := hY) Λ
    (Hom.CompactifiedComposition.leftUnitTotalRefinement C)
    (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite) (targetModels C) N hN hΛ

/-- The proved original map triangle is retained on the same native isomorphisms. -/
theorem moduleUnboundedLeftUnitSuppliedIso :
    Functor.isoWhiskerRight (moduleUnboundedLeftUnitFirstIso f Λ C N hN hΛ)
        (moduleUnboundedCompactificationFunctor f Λ C) ≪≫
      moduleUnboundedCompactifiedCompositionIso (𝟙 X) f Λ
        (Hom.CompactifiedComposition.leftUnit C) N hN hΛ =
    Functor.isoWhiskerRight
        (moduleUnboundedSingleIdentityValueIso (hX := hX) (hM := hX) X Λ)
        (moduleUnboundedCompactificationFunctor f Λ C) ≪≫
      Functor.leftUnitor (moduleUnboundedCompactificationFunctor f Λ C) ≪≫
      moduleUnboundedLeftUnitTotalIso f Λ C N hN hΛ := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have hs := congrArg (fun t => t.app K)
    (moduleUnboundedLeftUnitSuppliedEquation f Λ C N hN hΛ)
  have ht := @moduleUnboundedLeftUnitTotalMixedTransition X Y f _ C Λ _ hX hY
    (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite) (targetModels C)
  have ht' : CategoryTheory.imageComparison
      (L₁ := @moduleUnboundedDerivedLowerShriek X C.Xbar C.j _ Λ _ hX
        (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite))
      (L₂ := @moduleUnboundedDerivedLowerShriek X C.Xbar C.j _ Λ _ hX (targetModels C))
      (R₁ := @moduleUnboundedDerivedDirectImage Λ _ Y C.Xbar ((𝟙 C.Xbar) ≫ C.p) hY
        (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite))
      (R₂ := @moduleUnboundedDerivedDirectImage Λ _ Y C.Xbar C.p hY (targetModels C))
      (F := @moduleUnboundedDerivedDirectImage Λ _ C.Xbar C.Xbar (𝟙 C.Xbar)
        (targetModels C) (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite))
      (Functor.whiskerLeft (𝟭 (DerivedCategory (ModuleSheaf X Λ)))
        (moduleUnboundedLeftUnitTotalDelta f Λ C))
      (moduleUnboundedLeftUnitImageContraction f Λ C) = _ := ht.symm
  rw [ht'] at hs
  let F := moduleUnboundedCompactificationFunctor f Λ C
  let a := moduleUnboundedLeftUnitFirstIso f Λ C N hN hΛ
  let b := moduleUnboundedCompactifiedCompositionIso (𝟙 X) f Λ
    (Hom.CompactifiedComposition.leftUnit C) N hN hΛ
  let c := moduleUnboundedSingleIdentityValueIso (hX := hX) (hM := hX) X Λ
  let d := moduleUnboundedLeftUnitTotalIso f Λ C N hN hΛ
  change F.map (a.hom.app K) ≫ b.hom.app K =
    F.map (c.hom.app K) ≫ (𝟙 _ ≫ d.hom.app K)
  change F.map (a.hom.app K) ≫ b.hom.app K =
    F.map (c.hom.app K ≫ 𝟙 _) ≫ d.hom.app K at hs
  have hc := congrArg (fun z => F.map z ≫ d.hom.app K) (Category.comp_id (c.hom.app K))
  have hd := congrArg (fun z => F.map (c.hom.app K) ≫ z) (Category.id_comp (d.hom.app K))
  exact (hs.trans hc).trans hd.symm


end AlgebraicGeometry.Scheme.EtaleCohomology
