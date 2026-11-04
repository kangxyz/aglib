/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.ShiftedHom.RightComposition

/-! The original shifted contraction and opposite-degree cancellation. -/

open CategoryTheory

@[expose] public noncomputable section

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D]
  {M : Type*} [AddMonoid M] [HasShift C M] [HasShift D M]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [R.CommShift M]

/-- Contraction computes the value of the original right adjunct against the original trace. -/
theorem shiftedHomEquiv_contraction_value {I : C} {U K : D}
    {a b c d e f : M} (u : L.obj I ⟶ U)
    (x : ShiftedHom U K a) (r : ShiftedHom K K b)
    (y : ShiftedHom U K c) (h : b + a = c) (hy : y = x.comp r h)
    (τ : ShiftedHom (R.obj K) I d) (h₁ : d + b = e) (h₂ : d + b + a = f)
    (v : ShiftedHom I I f)
    (hv : (adj.shiftedHomEquiv c I K (u ≫ y)).comp τ (by rw [← h, ← add_assoc, h₂]) = v) :
    (adj.shiftedHomEquiv a I K (u ≫ x)).comp ((r.map R).comp τ h₁)
        (by rw [← h₁, h₂]) = v := by
  have hz : u ≫ y = ShiftedHom.comp (u ≫ x : ShiftedHom (L.obj I) K a) r h := by
    rw [hy]
    let w := r⟦a⟧' ≫ (shiftFunctorAdd' D b a c h).inv.app K
    exact (Category.assoc u x w).symm
  rw [hz, adj.shiftedHomEquiv_postcomp] at hv
  exact (ShiftedHom.comp_assoc _ _ _ h h₁ h₂).symm.trans hv

end CategoryTheory.Adjunction

namespace CategoryTheory.ShiftedHom

variable {D : Type*} [Category* D] [HasShift D ℤ]

/-- Opposite-degree composition is the original cancellation followed by the zero comparison. -/
theorem comp_neg_eq_mk₀ {I K J : D} (q : ℤ)
    (x : ShiftedHom I K q) (t : ShiftedHom K J (-q)) :
    x.comp t (neg_add_cancel q) = mk₀ 0 rfl
      (x ≫ t⟦q⟧' ≫ (shiftFunctorCompIsoId D (-q) q (neg_add_cancel q)).hom.app J) := by
  simp only [ShiftedHom.comp, ShiftedHom.mk₀, shiftFunctorCompIsoId, shiftFunctorZero',
    eqToIso_refl, Iso.refl_trans, Iso.trans_hom, NatTrans.comp_app, Category.assoc,
    Iso.symm_hom, Functor.id_obj, Iso.hom_inv_id_app, Category.comp_id]

end CategoryTheory.ShiftedHom
