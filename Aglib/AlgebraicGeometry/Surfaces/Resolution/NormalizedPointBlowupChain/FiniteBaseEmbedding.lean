/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.Surfaces.Resolution.NormalizedPointBlowupChain.ProjectiveEmbedding
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Point

/-!
# Original normalized-chain embeddings over a finite affine-base map

The original finite base map supplies a genuine projective embedding of the
chain base through native projective zero-space. The accepted proper-chain
embedding theorem then embeds the SAME terminal with its original base map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Blowup

/-- A proper normalized-point chain over an original finite affine-base map has
an actual finite standard projective embedding with the unchanged structural
triangle. No Noetherianity or regularity of the coefficient ring is assumed. -/
theorem NormalizedPointBlowupChain.exists_projective_embedding_of_isFinite_base
    {R : Type u} [CommRing R]
    {X T : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {f : T ⟶ X} (c : NormalizedPointBlowupChain f) [IsProper f]
    (β : X ⟶ Spec (.of R)) [IsFinite β] :
    ∃ (n : ℕ) (i : T ⟶ ProjectiveSpace R (ULift.{u} (Fin (n + 1)))),
      IsClosedImmersion i ∧
        i ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin (n + 1))) = f ≫ β := by
  let q : X ⟶ ProjectiveSpace R PUnit.{u + 1} :=
    β ≫ (ProjectiveSpace.pointIsoSpec R).inv
  let : IsFinite q := inferInstance
  obtain ⟨m, j, hj, hjbase⟩ :=
    ProjectiveSpace.FiniteEmbedding.exists_closedImmersion_of_isFinite q
  let : IsClosedImmersion j := hj
  obtain ⟨n, i, hi, hibase⟩ := c.exists_projective_embedding j
  refine ⟨n, i, hi, ?_⟩
  calc
    i ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin (n + 1))) =
        f ≫ j ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin (m + 1))) := hibase
    _ = f ≫ q ≫ ProjectiveSpace.toSpec R PUnit.{u + 1} := by rw [hjbase]
    _ = f ≫ β := by
      change f ≫ (β ≫ (ProjectiveSpace.pointIsoSpec R).inv) ≫
        (ProjectiveSpace.pointIsoSpec R).hom = _
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.Scheme.Blowup
