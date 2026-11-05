/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.UniformSmoothH1Detection
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ClosedCoefficientRefinement
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.RefinedRestrictionZero

/-! # One actual closed residual for all later target refinements

The genuine closed injective and its coefficient arrow are chosen once.
The original residual class is then used at every refinement. Its restriction
zero returns to the original target-refined class because the original open
zero persists and the closed coefficient square commutes canonically.
This is the actual induction return construction, not a claim that the
smaller-rank class already has a vanishing neighborhood.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u
attribute [local instance] hasSheafifyLarge hasSheafifyModules
  HasExt.standard HasDerivedCategory.standard

/-- Choose one genuine residual coefficient, independent of every later
refinement, and return its actual restriction-zero to the unchanged original
class. Only the already produced original open-zero is used in the return. -/
theorem exists_uniform_closed_residual_refinement_return
    {X U Z : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (i : Z ⟶ X) [IsClosedImmersion i]
    (hcomp : Set.range j = (Set.range i)ᶜ)
    (n : ℕ) (hn : 0 < n)
    (I : ModuleSheaf X (ULift.{u + 1} (ZMod n))) [Injective I] :
    ∃ J : ModuleSheaf Z (ULift.{u + 1} (ZMod n)), Injective J ∧
      ∃ a : (moduleInverseImage i (ULift.{u + 1} (ZMod n))).obj I ⟶ J, Mono a ∧
        ∀ {T V W T₂ V₂ W₂ : Scheme.{u}}
          (b : T ⟶ X) (j' : V ⟶ T) (i' : W ⟶ T) (bZ : W ⟶ Z)
          (hi : IsPullback bZ i' i b)
          (t : T₂ ⟶ T) (v : V₂ ⟶ V) (t' : W₂ ⟶ W)
          (j₂ : V₂ ⟶ T₂) (i₂ : W₂ ⟶ T₂) (bU₂ : V₂ ⟶ U)
          (_hj₂ : IsPullback bU₂ j₂ j (t ≫ b))
          (_hi₂ : IsPullback (t' ≫ bZ) i₂ i (t ≫ b))
          (_ho : v ≫ j' = j₂ ≫ t) (_hz : i₂ ≫ t = t' ≫ i')
          (_ : Smooth (t ≫ b))
          (c : Sheaf.H.{u + 2} ((inverseImage b).obj
            ((SheafOfModules.toSheaf (constantRing X
              (ULift.{u + 1} (ZMod n)))).obj I)) 1),
          cohomologyPullback.{u, u + 2, u + 2} j' _ 1 c = 0 →
          cohomologyPullback.{u, u + 2, u + 2} t' _ 1
            (Sheaf.H.map (moduleClosedPullbackCoefficientMap i i' b bZ hi.w.symm
              (ULift.{u + 1} (ZMod n)) I J a) 1
              (cohomologyPullback.{u, u + 2, u + 2} i' _ 1 c)) = 0 →
          cohomologyPullback.{u, u + 2, u + 2} t _ 1 c = 0 := by
  obtain ⟨J, hJ, a, ha, hdetect⟩ :=
    exists_uniform_smooth_moduleInjective_H1_detector.{u, u + 2, u + 2, u + 2, u + 2, u + 2, u + 2}
      j i hcomp n hn I
  refine ⟨J, hJ, a, ha, ?_⟩
  intro T V W T₂ V₂ W₂ b j' i' bZ hi t v t' j₂ i₂ bU₂ hj₂ hi₂ ho hz hs c hopen hclosed
  let F := (SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).obj I
  let c₂ := Sheaf.H.map ((inverseImageComp b t).inv.app F) 1
    (cohomologyPullback.{u, u + 2, u + 2} t _ 1 c)
  have hopen₂ : cohomologyPullback j₂ _ 1 c₂ = 0 :=
    restriction_zero_after_refinement_composite_coefficient b j' t j₂ v ho F 1 c hopen
  have hclosed₂ : Sheaf.H.map
      (moduleClosedPullbackCoefficientMap i i₂ (t ≫ b) (t' ≫ bZ) hi₂.w.symm
        (ULift.{u + 1} (ZMod n)) I J a) 1
      (cohomologyPullback i₂ _ 1 c₂) = 0 :=
    (moduleClosedPullbackCoefficientClass_refinement_eq_zero_iff
      i i' i₂ b bZ t t' hi.w.symm hz hi₂.w.symm
      (ULift.{u + 1} (ZMod n)) I J a 1 c).mpr hclosed
  have hc₂ : c₂ = 0 :=
    hdetect (t ≫ b) j₂ bU₂ hj₂ hs i₂ (t' ≫ bZ) hi₂ c₂ hopen₂ hclosed₂
  apply Sheaf.H.map_injective_of_isIso ((inverseImageComp b t).inv.app F) 1
  exact hc₂.trans (map_zero _).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
