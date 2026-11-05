/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ModuleInjectiveRefinementDetection
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ClosedCoefficientRefinement

/-! # A single finite coefficient replacement returns every target-refined zero

The genuine upstairs injective and its actual coefficient adjunct are chosen
once, before target refinements and classes. Canonical coefficient coherence
and the original finite retract return the unchanged class in every degree.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite
open Coefficients
universe u
attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- Return a zero on any Cartesian refinement through one fixed genuine
finite coefficient replacement, using the original comparison maps. -/
theorem exists_uniform_finite_coefficient_refinement_return
    {B D : Scheme.{u}} (g : D ⟶ B) [IsFinite g] [Surjective g]
    (Λ : Type (u + 1)) [Ring Λ] (I : ModuleSheaf B Λ) [Injective I] :
    ∃ J : ModuleSheaf D Λ, Injective J ∧
      ∃ α : (moduleInverseImage g Λ).obj I ⟶ J,
        ∀ {Y Z Y₂ Z₂ : Scheme.{u}}
          (v : Z ⟶ Y) (b : Y ⟶ B) (d : Z ⟶ D) (H : IsPullback d v g b)
          (t : Y₂ ⟶ Y) (t' : Z₂ ⟶ Z) (v₂ : Z₂ ⟶ Y₂)
          (_Ht : IsPullback t' v₂ v t)
          (q : ℕ) (c : Sheaf.H.{u + 2} ((inverseImage b).obj
            ((SheafOfModules.toSheaf (constantRing B Λ)).obj I)) q),
          cohomologyPullback.{u, u + 2, u + 2} t' _ q
            (Sheaf.H.map (moduleClosedPullbackCoefficientMap g v b d H.w.symm
              Λ I J α) q (cohomologyPullback.{u, u + 2, u + 2} v _ q c)) = 0 →
          cohomologyPullback.{u, u + 2, u + 2} t _ q c = 0 := by
  obtain ⟨J, hJ, α, hdetect⟩ :=
    exists_moduleInjective_finite_refinement_detector.{u, u + 2, u + 2} g Λ I
  refine ⟨J, hJ, α, ?_⟩
  intro Y Z Y₂ Z₂ v b d H t t' v₂ Ht q c hc
  let F := (SheafOfModules.toSheaf (constantRing B Λ)).obj I
  let c₂ := Sheaf.H.map ((inverseImageComp b t).inv.app F) q
    (cohomologyPullback.{u, u + 2, u + 2} t _ q c)
  have H₂ : IsPullback (t' ≫ d) v₂ g (t ≫ b) := Ht.paste_horiz H
  have hz : Sheaf.H.map
      (moduleClosedPullbackCoefficientMap g v₂ (t ≫ b) (t' ≫ d) H₂.w.symm
        Λ I J α) q (cohomologyPullback.{u, u + 2, u + 2} v₂ _ q c₂) = 0 :=
    (moduleClosedPullbackCoefficientClass_refinement_eq_zero_iff
      g v v₂ b d t t' H.w.symm Ht.w.symm H₂.w.symm Λ I J α q c).mpr hc
  have hzero : c₂ = 0 := hdetect v₂ (t ≫ b) (t' ≫ d) H₂ q c₂ hz
  apply Sheaf.H.map_injective_of_isIso ((inverseImageComp b t).inv.app F) q
  exact hzero.trans (map_zero _).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
