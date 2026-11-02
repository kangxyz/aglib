/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-! # Invertibility at the vertex of the original limiting cones -/

@[expose] public noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory.Limits

namespace CategoryTheory.NatTrans

variable {J : Type u₁} [Category.{v₁} J]
  {C : Type u₂} [Category.{v₂} C] {D : Type u₃} [Category.{v₃} D]

/-- If the two images of the supplied cone are limiting, invertibility on the
original diagram implies invertibility at its vertex. -/
theorem isIso_app_cone {K : J ⥤ C} (c : Cone K)
    {F G : C ⥤ D} (α : F ⟶ G)
    (hF : IsLimit (F.mapCone c)) (hG : IsLimit (G.mapCone c))
    [∀ j, IsIso (α.app (K.obj j))] : IsIso (α.app c.pt) := by
  let : ∀ j, IsIso ((Functor.whiskerLeft K α).app j) :=
    fun j => inferInstanceAs (IsIso (α.app (K.obj j)))
  let : IsIso (Functor.whiskerLeft K α) :=
    NatIso.isIso_of_isIso_app (Functor.whiskerLeft K α)
  let e := hF.conePointsIsoOfNatIso hG (asIso (Functor.whiskerLeft K α))
  have he : α.app c.pt = e.hom := by
    apply hG.hom_ext
    intro j
    dsimp only [e]
    rw [IsLimit.conePointsIsoOfNatIso_hom_comp]
    exact (α.naturality (c.π.app j)).symm
  rw [he]
  infer_instance

end CategoryTheory.NatTrans
