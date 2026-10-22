/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Agreement on protected pullback intersections

An actual comparison over a base chart transports a prescribed open-restriction
agreement. The argument uses only the two native restriction pullback squares.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Transport an open-restriction agreement along an actual comparison over a
pullback chart. No flatness, separatedness, or modification hypothesis is needed. -/
theorem agreement_on_pullback_restriction {X Z Y B P : Scheme.{u}}
    (q : Z ⟶ X) (t : Y ⟶ X) (γ : B ⟶ Z)
    (l : pullback t q ⟶ B) (hl : l ≫ γ = pullback.snd t q)
    (U : X.Opens) (g : U.toScheme ⟶ P) (F : B ⟶ P)
    (h : (γ ⁻¹ᵁ (q ⁻¹ᵁ U)).ι ≫ F = (γ ∣_ (q ⁻¹ᵁ U)) ≫ (q ∣_ U) ≫ g) :
    pullback.fst (pullback.fst t q) (t ⁻¹ᵁ U).ι ≫ l ≫ F =
      pullback.snd (pullback.fst t q) (t ⁻¹ᵁ U).ι ≫ (t ∣_ U) ≫ g := by
  let α := pullback.fst (pullback.fst t q) (t ⁻¹ᵁ U).ι
  let β := pullback.snd (pullback.fst t q) (t ⁻¹ᵁ U).ι
  let r := β ≫ (t ∣_ U)
  let v := α ≫ pullback.snd t q
  have hv : r ≫ U.ι = v ≫ q := by
    calc
      r ≫ U.ι = β ≫ (t ⁻¹ᵁ U).ι ≫ t := by
        simp only [r, Category.assoc, morphismRestrict_ι]
      _ = α ≫ pullback.fst t q ≫ t := by
        rw [← Category.assoc, ← pullback.condition, Category.assoc]
      _ = v ≫ q := by
        simp only [v, Category.assoc, pullback.condition]
  let b := (isPullback_morphismRestrict q U).lift r v hv
  have hb₁ : b ≫ (q ∣_ U) = r :=
    (isPullback_morphismRestrict q U).lift_fst r v hv
  have hb₂ : b ≫ (q ⁻¹ᵁ U).ι = v :=
    (isPullback_morphismRestrict q U).lift_snd r v hv
  have hc : b ≫ (q ⁻¹ᵁ U).ι = (α ≫ l) ≫ γ := by
    rw [hb₂, Category.assoc, hl]
  let c := (isPullback_morphismRestrict γ (q ⁻¹ᵁ U)).lift
    b (α ≫ l) hc
  have hc₁ : c ≫ (γ ∣_ (q ⁻¹ᵁ U)) = b :=
    (isPullback_morphismRestrict γ (q ⁻¹ᵁ U)).lift_fst _ _ hc
  have hc₂ : c ≫ (γ ⁻¹ᵁ (q ⁻¹ᵁ U)).ι = α ≫ l :=
    (isPullback_morphismRestrict γ (q ⁻¹ᵁ U)).lift_snd _ _ hc
  change α ≫ l ≫ F = β ≫ (t ∣_ U) ≫ g
  calc
    α ≫ l ≫ F =
        (c ≫ (γ ⁻¹ᵁ (q ⁻¹ᵁ U)).ι) ≫ F := by rw [hc₂, Category.assoc]
    _ = c ≫ (γ ∣_ (q ⁻¹ᵁ U)) ≫ (q ∣_ U) ≫ g := by
      rw [Category.assoc, h]
    _ = β ≫ (t ∣_ U) ≫ g := by
      rw [← Category.assoc c, hc₁, ← Category.assoc b, hb₁]
      rfl

end AlgebraicGeometry.Scheme.Hom
