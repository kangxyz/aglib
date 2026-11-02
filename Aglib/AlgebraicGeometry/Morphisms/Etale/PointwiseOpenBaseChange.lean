/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Etale.FiniteStalkNeighborhood

/-! # Actual open witnesses under open base change -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- An etale witness on an open source gives the same witness in its open image. -/
theorem etaleAt.of_comp_openImmersion {W Z X : Scheme.{u}}
    (i : W ⟶ Z) [IsOpenImmersion i] (f : Z ⟶ X) (w : W)
    (h : (i ≫ f).etaleAt w) : f.etaleAt (i w) := by
  obtain ⟨U, hw, hU⟩ := h
  let : Etale (U.ι ≫ (i ≫ f)) := hU
  refine ⟨i ''ᵁ U, ⟨w, hw, rfl⟩, ?_⟩
  have he : (i ''ᵁ U).ι ≫ f = (i.isoImage U).inv ≫ (U.ι ≫ (i ≫ f)) := by
    simpa only [Category.assoc] using
      (congrArg (· ≫ f) (i.isoImage_inv_ι U)).symm
  rw [he]
  infer_instance

/-- A specified point of an open-base-change square detects the original
etale neighborhood, in both directions and without presentation hypotheses. -/
theorem etaleAt_iff_of_open_square {P Z V X : Scheme.{u}}
    (i : P ⟶ Z) (f' : P ⟶ V) (f : Z ⟶ X) (b : V ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion b] (H : i ≫ f = f' ≫ b) (p : P) :
    f'.etaleAt p ↔ f.etaleAt (i p) := by
  constructor
  · rintro ⟨U, hp, hU⟩
    let : Etale (U.ι ≫ f') := hU
    apply etaleAt.of_comp_openImmersion i f p
    refine ⟨U, hp, ?_⟩
    rw [H, ← Category.assoc]
    infer_instance
  · intro h
    obtain ⟨U, hp, hU⟩ := etaleAt.comp_openImmersion f i p h
    refine ⟨U, hp, ?_⟩
    have : Etale ((U.ι ≫ f') ≫ b) := by
      simpa only [Category.assoc, ← H] using hU
    exact Etale.of_comp (U.ι ≫ f') b

end AlgebraicGeometry.Scheme.Hom
