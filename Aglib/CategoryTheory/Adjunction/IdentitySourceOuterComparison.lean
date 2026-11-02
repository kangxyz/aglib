/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! # Original identity-source refinement and the outer-adjoint comparison -/

@[expose] public noncomputable section
namespace CategoryTheory
variable {A B : Type*} [Category* A] [Category* B]
  {J R : A ⥤ B} {I H : A ⥤ A}

/-- Contracting an original identity-source mate gives the specified canonical comparison. -/
theorem identitySourceOuterComparison
    (σ : I ⋙ J ⟶ H ⋙ R) (δ : J ⟶ H ⋙ R) (b : J ⟶ R) (bI : H ⟶ I)
    (γ : I ⋙ R ⟶ I ⋙ R) (d : I ≅ 𝟭 A) (e : H ≅ 𝟭 A)
    (hδ : ∀ K, δ.app K = J.map (d.inv.app K) ≫ σ.app K)
    (hb : bI = e.hom ≫ d.inv) (hγ : γ = 𝟙 (I ⋙ R))
    (h : ∀ K, σ.app K ≫ R.map (bI.app K) ≫ γ.app K = b.app (I.obj K)) :
    δ ≫ Functor.whiskerRight e.hom R ≫ (Functor.leftUnitor R).hom = b := by
  subst γ
  subst bI
  ext K
  have hh := h K
  change σ.app K ≫ R.map (e.hom.app K ≫ d.inv.app K) ≫ 𝟙 _ = b.app (I.obj K) at hh
  rw [Category.comp_id, R.map_comp] at hh
  change δ.app K ≫ R.map (e.hom.app K) ≫ 𝟙 _ = b.app K
  rw [Category.comp_id]
  apply (cancel_mono (R.map (d.inv.app K))).mp
  rw [hδ]
  calc
    _ = J.map (d.inv.app K) ≫
        (σ.app K ≫ (R.map (e.hom.app K) ≫ R.map (d.inv.app K))) := by
      simp only [Category.assoc]
    _ = J.map (d.inv.app K) ≫ b.app (I.obj K) := by rw [hh]
    _ = _ := b.naturality (d.inv.app K)

end CategoryTheory
