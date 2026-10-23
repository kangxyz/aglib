/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Properties

/-! # Original field-valued points factor through actual affine open charts -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u

/-- Retain the literal field point when choosing an affine chart of its target. -/
theorem exists_affineOpenCover_point_factorization {S : Scheme.{u}}
    {Ω : Type u} [Field Ω] (η : Spec (.of Ω) ⟶ S) :
    ∃ (i : S.affineOpenCover.I₀) (φ : S.affineOpenCover.X i →+* Ω),
      Spec.map (CommRingCat.ofHom φ) ≫ S.affineOpenCover.f i = η := by
  let i := S.affineOpenCover.idx (η default)
  have hη : Set.range η ⊆ Set.range (S.affineOpenCover.f i) := by
    rintro _ ⟨x, rfl⟩
    simpa only [Subsingleton.elim x (default : Spec (.of Ω))] using
      S.affineOpenCover.covers (η default)
  let a := IsOpenImmersion.lift (S.affineOpenCover.f i) η hη
  refine ⟨i, (Spec.preimage a).hom, ?_⟩
  exact (congrArg (fun q => q ≫ S.affineOpenCover.f i)
    (Spec.map_preimage a)).trans
      (IsOpenImmersion.lift_fac (S.affineOpenCover.f i) η hη)

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
