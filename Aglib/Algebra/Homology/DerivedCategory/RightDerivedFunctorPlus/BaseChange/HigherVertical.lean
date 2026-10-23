/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange

/-! # Transporting the actual vertical composition law through homology -/

@[expose] public section
namespace CategoryTheory
variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

/-- Transport a proved composition square through a functor and its actual endpoint isomorphism. -/
theorem mapped_vertical_transport (H : D ⥤ E) {R R' : C ⥤ D} (c : R ≅ R')
    {X Y : C} (p : X ⟶ Y) {Z Z' : D} (d : Z ⟶ Z')
    (v : Z' ⟶ R'.obj X) (u : Z ⟶ R.obj X)
    (h : d ≫ v = u ≫ c.hom.app X)
    {P Q : E} (s : P ⟶ H.obj Z) (e : Q ≅ H.obj (R.obj Y))
    (b : P ⟶ Q) (hb : b = s ≫ H.map u ≫ H.map (R.map p) ≫ e.inv) :
    s ≫ H.map d ≫ H.map v ≫ H.map (R'.map p) =
      b ≫ e.hom ≫ H.map (c.hom.app Y) := by
  rw [hb]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← H.map_comp_assoc, h, H.map_comp, Category.assoc]
  have hn := congrArg H.map (c.hom.naturality p)
  simp only [H.map_comp] at hn
  rw [← hn]

end CategoryTheory
