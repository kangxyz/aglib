/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Square

/-! # Scalar-extension squares of original restriction maps

Construct the complete tensor square from its original maps and unit-tensor
formulas before specializing its module objects. No replacement tensor map is
chosen: both supplied mates and all three comparison isomorphisms are retained.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u w

namespace ModuleCat

/-- The complete original tensor restriction square, including its law. -/
def tensorRestrictionSquare {R : Type u} {S : Type u} [CommRing R] [CommRing S]
    (σ : R →+* S) (A A' : ModuleCat.{max u w} R) (B B' D : ModuleCat.{max u w} S)
    (q : (extendScalars σ).obj A ⟶ B) (δ : (extendScalars σ).obj A' ⟶ D)
    (eX : A ≅ A') (eY : B ≅ B') (eε : B' ≅ D)
    (g : A → B) (r : A' → D)
    (hq : ∀ x, q ((1 : S) ⊗ₜ[R,σ] x) = g x)
    (hδ : ∀ x, δ ((1 : S) ⊗ₜ[R,σ] x) = r x)
    (hgeo : ∀ x, eε.hom (eY.hom (g x)) = r (eX.hom x)) :
    Square (ModuleCat.{max u w} S) where
  X₁ := (extendScalars σ).obj A
  X₂ := B
  X₃ := (extendScalars σ).obj A'
  X₄ := D
  f₁₂ := q
  f₂₄ := eY.hom ≫ eε.hom
  f₁₃ := (extendScalars σ).map eX.hom
  f₃₄ := δ
  fac := by
    apply ExtendScalars.hom_ext
    intro x
    change eε.hom (eY.hom (q ((1 : S) ⊗ₜ[R,σ] x))) =
      δ ((extendScalars σ).map eX.hom ((1 : S) ⊗ₜ[R,σ] x))
    calc
      _ = eε.hom (eY.hom (g x)) :=
        congrArg (fun z => eε.hom (eY.hom z)) (hq x)
      _ = r (eX.hom x) := hgeo x
      _ = δ ((1 : S) ⊗ₜ[R,σ] eX.hom x) := (hδ (eX.hom x)).symm
      _ = _ := congrArg δ (ExtendScalars.map_tmul σ eX.hom 1 x).symm

end ModuleCat

namespace CategoryTheory.Square

/-- Invertibility of the original top edge from the other three edges. -/
theorem isIso_top_of_other_edges {C : Type*} [Category* C] (s : Square C)
    [IsIso s.f₁₃] [IsIso s.f₂₄] [IsIso s.f₃₄] : IsIso s.f₁₂ := by
  have : IsIso (s.f₁₂ ≫ s.f₂₄) := by
    rw [s.fac]
    infer_instance
  exact IsIso.of_isIso_comp_right s.f₁₂ s.f₂₄

end CategoryTheory.Square
