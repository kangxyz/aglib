/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.EqToHom

/-!
# The canonical equality-map formula for transport of an isomorphism endpoint.

Source: `lean/R5Lab/Aglib/CategoryTheory/Iso/Composite.lean`
at frozen R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `edd41e732aa120b7f39967d2796d2dfd651a09a757476ad221bd8af64358036f`.
Native objects and canonical maps are reused; provenance does not select declaration namespaces.
-/

@[expose] public section

open CategoryTheory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Iso
universe u
/-- Transport of an isomorphism endpoint has the canonical equality-map formula. -/
theorem mpr_hom {C : Type*} [Category C] {A B B' : C}
    (h : B = B') (e : A ≅ B') :
    (Eq.mpr (congrArg (fun Z => A ≅ Z) h) e).hom = e.hom ≫ eqToHom h.symm := by
  subst B'
  simp

end CategoryTheory.Iso
