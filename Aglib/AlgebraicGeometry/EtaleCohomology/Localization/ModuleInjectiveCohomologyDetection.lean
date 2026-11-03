/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ModuleInjectiveRetract
public import Aglib.CategoryTheory.Sites.SheafCohomology.SplitPairDetection

/-! # Original pulled-back injective classes detected on open and closed coefficients

The constructed module retraction yields the original pair of coefficient
maps after every scheme inverse image. Their zero images detect the same
class. This is the support-induction detection step, not an assertion of
base change or acyclicity on either piece.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u e

attribute [local instance] hasSheafifyLarge

/-- For a genuine injective module coefficient, its original open unit and
the constructed closed adjunct detect every pulled-back cohomology class.
The target Ext universe remains independent and arbitrary. -/
theorem exists_moduleInjective_open_closed_cohomology_detection
    {U Z X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hcomp : Set.range j = (Set.range i)ᶜ)
    (Λ : Type (u + 1)) [Ring Λ] (I : ModuleSheaf X Λ) [Injective I] :
    ∃ J : ModuleSheaf Z Λ, Injective J ∧
      ∃ a : (moduleInverseImage i Λ).obj I ⟶ J, Mono a ∧
        ∀ {T : Scheme.{u}} (b : T ⟶ X)
          [HasExt.{e} (AbelianSheaf.{u, u + 1} T)] (q : ℕ)
          (x : Sheaf.H.{e} ((inverseImage b).obj
            ((SheafOfModules.toSheaf (constantRing X Λ)).obj I)) q),
          Sheaf.H.map ((inverseImage b).map
            ((SheafOfModules.toSheaf (constantRing X Λ)).map
              ((moduleInverseImageAdjunction j Λ).unit.app I))) q x = 0 →
          Sheaf.H.map ((inverseImage b).map
            ((SheafOfModules.toSheaf (constantRing X Λ)).map
              ((moduleInverseImageAdjunction i Λ).homEquiv I J a))) q x = 0 →
          x = 0 := by
  obtain ⟨J, hJ, a, ha, r, hr⟩ :=
    exists_moduleInjective_open_closed_retract j i hcomp Λ I
  refine ⟨J, hJ, a, ha, ?_⟩
  intro T b _ q x hopen hclosed
  let Q := SheafOfModules.toSheaf (constantRing X Λ) ⋙ inverseImage b
  let f : I ⟶ (moduleDirectImage j Λ).obj ((moduleInverseImage j Λ).obj I) :=
    (moduleInverseImageAdjunction j Λ).unit.app I
  let g : I ⟶ (moduleDirectImage i Λ).obj J :=
    (moduleInverseImageAdjunction i Λ).homEquiv I J a
  have hs : f ≫ (biprod.inl ≫ r) + g ≫ (biprod.inr ≫ r) = 𝟙 I := by
    rw [← Category.assoc, ← Category.assoc, ← Preadditive.add_comp, ← biprod.lift_eq]
    exact hr
  have hsQ : Q.map f ≫ Q.map (biprod.inl ≫ r) +
      Q.map g ≫ Q.map (biprod.inr ≫ r) = 𝟙 (Q.obj I) := by
    rw [← Q.map_comp, ← Q.map_comp, ← Q.map_add, hs, Q.map_id]
  exact Sheaf.H.eq_zero_of_split_pair (Q.map f) (Q.map g)
    (Q.map (biprod.inl ≫ r)) (Q.map (biprod.inr ≫ r)) hsQ q x hopen hclosed

end AlgebraicGeometry.Scheme.EtaleCohomology
