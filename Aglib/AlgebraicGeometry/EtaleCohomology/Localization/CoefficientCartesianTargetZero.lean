/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.EtaleCoefficientComponentClass
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.OriginalClassZeroTransport
public import Aglib.CategoryTheory.Limits.Shapes.PullbackPastingIso

/-! # Returning the original coefficient class through a Cartesian target change

The actual module coefficient comparison is followed through the original
Cartesian target square. A zero produced on the changed family returns to
the whole original family over the composite target map, without choosing
another coefficient or class.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u eY

attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- Return an actual changed-coefficient zero along the same Cartesian target
square. No injective replacement and no extra vanishing assertion is used. -/
theorem moduleCoefficientComponentClass_target_zero
    {B D Y Z X O V : Scheme.{u}}
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    (i : D ⟶ B) (v : Z ⟶ Y) (b : Y ⟶ B) (d : Z ⟶ D)
    (h : v ≫ b = d ≫ i)
    (j : O ⟶ X) (a : Y ⟶ X) (a' : Z ⟶ O)
    (H : IsPullback a' v j a) (t : V ⟶ O)
    (Λ : Type (u + 1)) [Ring Λ] (J : ModuleSheaf B Λ)
    (q : ℕ) (c : Sheaf.H.{eY} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing B Λ)).obj J)) q)
    (hc : cohomologyPullback.{u, u + 2, u + 2} (pullback.snd t a') _ q
      (moduleCoefficientComponentClass.{u, eY, u + 2} i v b d h Λ J q c) = 0) :
    cohomologyPullback.{u, eY, u + 2} (pullback.snd (t ≫ j) a) _ q c = 0 := by
  have hcomp := (moduleCoefficientComponentClass_restriction_zero_iff
    i v b d h (pullback.snd t a') Λ J q c).mp hc
  let E : pullback t a' ≅ pullback (t ≫ j) a :=
    H.familyPullbackIso t ≪≫ pullbackSymmetry a (t ≫ j)
  have he : E.hom ≫ pullback.snd (t ≫ j) a = pullback.snd t a' ≫ v := by
    change ((H.familyPullbackIso t).hom ≫ (pullbackSymmetry a (t ≫ j)).hom) ≫
      pullback.snd (t ≫ j) a = _
    rw [Category.assoc, pullbackSymmetry_hom_comp_snd, H.familyPullbackIso_hom_fst t]
  have hi : E.inv ≫ (pullback.snd t a' ≫ v) = pullback.snd (t ≫ j) a := by
    rw [← he, Iso.inv_hom_id_assoc]
  exact TwoFieldEffacement.original_class_zero_of_map_law E.inv
    (pullback.snd t a' ≫ v) (pullback.snd (t ≫ j) a) hi _ q c hcomp

end AlgebraicGeometry.Scheme.EtaleCohomology
