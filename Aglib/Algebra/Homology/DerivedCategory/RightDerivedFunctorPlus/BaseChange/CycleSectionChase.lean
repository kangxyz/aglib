/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.EpiMono

/-! # Actual cycle-section cancellation

The full section chase uses only the original cycle inclusions, projections,
comparison isomorphisms and commuting equations. All groups and maps remain
opaque here, before any geometric or resolution specialization.
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory

/-- Compatible actual cycle representatives determine the original map on
higher sections. No injectivity of an edge map is assumed. -/
theorem cycle_section_chase
    {Z Z' T T' Q Q' M M' A A' : AddCommGrpCat.{u}}
    (i : Z ⟶ T) (i' : Z' ⟶ T') [Mono i'] (p : Z ⟶ Q) (p' : Z' ⟶ Q')
    (r : M ≅ Q) (r' : M' ≅ Q') (k : Z ⟶ Z') (v : T ⟶ T')
    (b : M ⟶ M') (d : T ⟶ A) (e : T' ≅ A') (a : A ⟶ A')
    (hi : k ≫ i' = i ≫ v) (ht : v ≫ e.hom = d ≫ a)
    (hp : p ≫ r.inv ≫ b ≫ r'.hom = k ≫ p')
    (x : M) (y : M') (z : Z) (z' : Z')
    (hx : r.hom x = p z) (hy : r'.hom y = p' z')
    (hz : e.hom (i' z') = a (d (i z))) : b x = y := by
  have hzz : k z = z' := by
    apply (AddCommGrpCat.mono_iff_injective i').mp inferInstance
    apply (ConcreteCategory.bijective_of_isIso e.hom).injective
    have h₁ := ConcreteCategory.congr_hom hi z
    have h₂ := ConcreteCategory.congr_hom ht (i z)
    exact ((congrArg e.hom h₁).trans h₂).trans hz.symm
  have hx' : r.inv (p z) = x := by
    rw [← hx]
    exact ConcreteCategory.congr_hom r.hom_inv_id x
  have h := ConcreteCategory.congr_hom hp z
  change r'.hom (b (r.inv (p z))) = p' (k z) at h
  rw [hx', hzz] at h
  exact (ConcreteCategory.bijective_of_isIso r'.hom).injective (h.trans hy.symm)

end CategoryTheory
