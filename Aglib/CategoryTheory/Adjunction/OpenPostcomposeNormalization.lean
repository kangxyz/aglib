/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.Adjunction.TripleCompositionInverse
public import Aglib.CategoryTheory.NatTrans.TargetComparisonEquation

/-! # Original open-composition normalization through an invertible canonical second map -/
@[expose] public noncomputable section
namespace CategoryTheory
variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  {J S : A ⥤ C} {J₁ S₁ : A ⥤ B} {J₂ S₂ : B ⥤ C}

/-- Contract the actual original second comparison and the specified open compositor. -/
def openPostcomposeNormalizationIso (c : J ≅ J₁ ⋙ J₂) (e : J₂ ≅ S₂) :
    J₁ ⋙ S₂ ≅ J :=
  Functor.isoWhiskerLeft J₁ e.symm ≪≫ c.symm

/-- The contraction preserves the same original canonical map, by its composition square. -/
theorem openPostcomposeNormalization_toTarget
    (b : J ⟶ S) (b₁ : J₁ ⟶ S₁) (e : J₂ ≅ S₂)
    (c : J ≅ J₁ ⋙ J₂) (r : S ≅ S₁ ⋙ S₂)
    (h : c.hom ≫ Functor.whiskerRight b₁ J₂ ≫ Functor.whiskerLeft S₁ e.hom = b ≫ r.hom) :
    TargetComparisonEquation (openPostcomposeNormalizationIso c e).hom b
      (Functor.whiskerRight b₁ S₂ ≫ r.inv) := by
  have hc := openCompositionToTarget_of_square b b₁ e.hom c r h
  ext K
  change (e.inv.app (J₁.obj K) ≫ c.inv.app K) ≫ b.app K =
    S₂.map (b₁.app K) ≫ r.inv.app K
  have hcK := hc K
  change c.inv.app K ≫ b.app K =
    J₂.map (b₁.app K) ≫ e.hom.app (S₁.obj K) ≫ r.inv.app K at hcK
  rw [Category.assoc, hcK]
  rw [← Category.assoc, ← Category.assoc, ← e.inv.naturality (b₁.app K)]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
end CategoryTheory
