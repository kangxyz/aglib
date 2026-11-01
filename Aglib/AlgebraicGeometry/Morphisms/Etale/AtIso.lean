/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Etale.At

/-! # Pointwise etaleness under an original source isomorphism -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- Pull back the actual etale open neighborhood along a source isomorphism. -/
theorem etaleAt.of_source_iso {Z Z' X : Scheme.{u}} {f : Z ⟶ X}
    {g : Z' ⟶ X} (e : Z' ≅ Z) (he : e.hom ≫ f = g) (z : Z')
    (h : f.etaleAt (e.hom z)) : g.etaleAt z := by
  obtain ⟨U, hz, hU⟩ := h
  let : Etale (U.ι ≫ f) := hU
  refine ⟨e.hom ⁻¹ᵁ U, hz, ?_⟩
  have hfac : (e.hom ⁻¹ᵁ U).ι ≫ g =
      (e.hom.preimageIso U).hom ≫ (U.ι ≫ f) := by
    rw [← he, ← Category.assoc, ← preimageIso_hom_ι]
    simp only [Category.assoc]
  rw [hfac]
  infer_instance

/-- An over-base automorphism carries an etale point to an etale point. -/
theorem etaleAt.map_over_iso {Z X : Scheme.{u}} {f : Z ⟶ X}
    (e : Z ≅ Z) (he : e.hom ≫ f = f) {z : Z} (h : f.etaleAt z) :
    f.etaleAt (e.hom z) := by
  have hi : e.inv ≫ f = f := by
    calc
      e.inv ≫ f = e.inv ≫ (e.hom ≫ f) := congrArg (e.inv ≫ ·) he.symm
      _ = f := by simp
  apply etaleAt.of_source_iso e.symm hi (e.hom z)
  change f.etaleAt ((e.hom ≫ e.inv) z)
  rw [Iso.hom_inv_id]
  exact h

end AlgebraicGeometry.Scheme.Hom
