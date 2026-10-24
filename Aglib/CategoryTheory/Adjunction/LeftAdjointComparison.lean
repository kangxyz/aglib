/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.Mates

/-! # The hom orientation of the original left-adjoint uniqueness comparison -/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]
  {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}

/-- The original right-adjoint transport has the expected reversed conjugate. -/
theorem conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : R₁ ≅ R₂) :
    conjugateEquiv b a ((a.ofNatIsoRight e).leftAdjointUniq b).hom = e.inv := by
  have h := conjugateEquiv_leftAdjointUniq_ofNatIsoRight_inv b a e.symm
  have he : (b.leftAdjointUniq (a.ofNatIsoRight e)).inv =
      ((a.ofNatIsoRight e).leftAdjointUniq b).hom := by
    ext X
    exact Adjunction.leftAdjointUniq_inv_app b (a.ofNatIsoRight e) X
  simpa only [Iso.symm_symm_eq, Iso.symm_hom, he] using h

end CategoryTheory
