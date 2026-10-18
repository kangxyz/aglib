/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CoverSequence
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# A finite affine-open cover for coefficient dévissage

The cover is the native finite subcover of the installed affine cover.
-/

@[expose] public section
noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- A Noetherian scheme has a finite actual affine-open cover with quasi-compact inclusions. -/
theorem exists_finiteAffineOpenCover_relativeSerre (Y : Scheme.{u}) [IsNoetherian Y] :
    ∃ (J : Type u) (_ : Finite J) (U : J → Y.Opens),
      iSup U = ⊤ ∧ (∀ j, IsAffineOpen (U j)) ∧ (∀ j, QuasiCompact (U j).ι) := by
  let V := Y.affineCover.finiteSubcover
  refine ⟨V.I₀, inferInstance, (fun j => (V.f j).opensRange), V.iSup_opensRange, ?_, ?_⟩
  · intro j
    let : IsAffine (V.X j) := by
      change IsAffine (Y.affineCover.X (Y.affineCover.idx j.val))
      infer_instance
    exact isAffineOpen_opensRange (V.f j)
  · intro j
    infer_instance

end AlgebraicGeometry.Scheme.Cohomology
