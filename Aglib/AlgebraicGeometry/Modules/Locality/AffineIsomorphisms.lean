/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness

/-! # Isomorphism detection on original affine restrictions

The original affine open cover is constructed once for an arbitrary module
morphism. Concrete consumers supply only their restriction theorem.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- A module-sheaf map is invertible if all its original affine restrictions are. -/
theorem isIso_of_affineRestrictions {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (hf : ∀ (R : CommRingCat.{u}) (j : Spec R ⟶ X) [IsOpenImmersion j],
      IsIso ((restrictFunctor j).map f)) : IsIso f := by
  let 𝒰 := X.affineOpenCover
  apply isIso_of_restrict_openCover (fun i => Spec (𝒰.X i)) 𝒰.f
    (fun x => ⟨𝒰.idx x, 𝒰.covers x⟩)
  intro i
  exact hf (𝒰.X i) (𝒰.f i)

end AlgebraicGeometry.Scheme.Modules
