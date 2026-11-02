/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! # An original identity-source square descends the canonical outer-adjoint map -/

@[expose] public section
namespace CategoryTheory
variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  {Jc Rc : A ⥤ B} {Jd Rd : A ⥤ C} {R : B ⥤ C} {I : A ⥤ A}

/-- Original mixed-mate compatibility and original identity normalization give refinement
naturality for the specified outer-adjoint comparisons. -/
theorem refinementOuterComparison
    (σ : I ⋙ Jd ⟶ Jc ⋙ R) (δ : Jd ⟶ Jc ⋙ R) (bc : Jc ⟶ Rc) (bd : Jd ⟶ Rd)
    (d : I ≅ 𝟭 A) (c : Rc ⋙ R ≅ I ⋙ Rd) (e : Rc ⋙ R ≅ Rd)
    (hδ : ∀ K, δ.app K = Jd.map (d.inv.app K) ≫ σ.app K)
    (hc : c ≪≫ Functor.isoWhiskerRight d Rd ≪≫ Functor.leftUnitor Rd = e)
    (hσ : ∀ K, σ.app K ≫ R.map (bc.app K) ≫ c.hom.app K = bd.app (I.obj K)) :
    δ ≫ Functor.whiskerRight bc R ≫ e.hom = bd := by
  ext K
  have hcK := congrArg (fun z => z.hom.app K) hc
  change c.hom.app K ≫ Rd.map (d.hom.app K) ≫ 𝟙 _ = e.hom.app K at hcK
  rw [Category.comp_id] at hcK
  change δ.app K ≫ R.map (bc.app K) ≫ e.hom.app K = bd.app K
  rw [hδ, ← hcK]
  calc
    _ = Jd.map (d.inv.app K) ≫
        (σ.app K ≫ R.map (bc.app K) ≫ c.hom.app K) ≫ Rd.map (d.hom.app K) := by
      simp only [Category.assoc]
    _ = (Jd.map (d.inv.app K) ≫ bd.app (I.obj K)) ≫ Rd.map (d.hom.app K) := by
      rw [hσ]
      simp only [Category.assoc]
    _ = (bd.app K ≫ Rd.map (d.inv.app K)) ≫ Rd.map (d.hom.app K) := by
      rw [bd.naturality]
      rfl
    _ = _ := by
      rw [Category.assoc, ← Rd.map_comp, Iso.inv_hom_id_app]
      change bd.app K ≫ Rd.map (𝟙 K) = bd.app K
      rw [Rd.map_id]
      exact Category.comp_id (bd.app K)

end CategoryTheory
