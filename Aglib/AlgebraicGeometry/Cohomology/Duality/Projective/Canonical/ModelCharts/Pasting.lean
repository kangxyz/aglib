/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Iso

/-!
# Pasting the actual ordinary chart arrows

The native source prefactor, fixed-model canonical square, original
resolution lift and target-differential restriction compose to equality
of the original whole chart arrows.
-/

@[expose] public section

open CategoryTheory

universe u v w z
namespace AlgebraicGeometry.Scheme.Modules

/-- Paste the four original ordinary squares and cancel the same target isomorphism. -/
theorem canonicalChartArrow_paste {C : Type u} {D : Type v}
    [Category.{w} C] [Category.{z} D] (F : C ⥤ D)
    {M H Q N : C} {M' H' H'' Q' N' : D}
    (s : M ≅ H) (s' : M' ≅ H') (u : N ≅ Q) (u' : N' ≅ Q')
    (f : H ⟶ Q) (f' : H' ⟶ Q') (f'' : H'' ⟶ Q')
    (rM : F.obj M ⟶ M') (rN : F.obj N ⟶ N')
    (T : F.obj H ⟶ H'') (h : H' ⟶ H'') (a : F.obj Q ⟶ Q')
    (hs : rM ≫ s'.hom ≫ h = F.map s.hom ≫ T)
    (hf : F.map f ≫ a = T ≫ f'')
    (hh : h ≫ f'' = f') (hu : F.map u.hom ≫ a = rN ≫ u'.hom) :
    F.map (s.hom ≫ f ≫ u.inv) ≫ rN = rM ≫ s'.hom ≫ f' ≫ u'.inv := by
  have hU : F.map u.inv ≫ rN = a ≫ u'.inv := by
    apply (cancel_epi (F.map u.hom)).mp
    rw [← F.map_comp_assoc, u.hom_inv_id, F.map_id, Category.id_comp,
      ← Category.assoc, hu, Category.assoc, u'.hom_inv_id, Category.comp_id]
  calc
    _ = F.map s.hom ≫ F.map f ≫ a ≫ u'.inv := by
      rw [F.map_comp, F.map_comp]
      simpa only [Category.assoc] using congrArg
        (fun t => F.map s.hom ≫ F.map f ≫ t) hU
    _ = F.map s.hom ≫ T ≫ f'' ≫ u'.inv := by
      simpa only [Category.assoc] using congrArg
        (fun t => F.map s.hom ≫ t ≫ u'.inv) hf
    _ = rM ≫ s'.hom ≫ h ≫ f'' ≫ u'.inv := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ f'' ≫ u'.inv) hs.symm
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun t => rM ≫ s'.hom ≫ t ≫ u'.inv) hh

end AlgebraicGeometry.Scheme.Modules
