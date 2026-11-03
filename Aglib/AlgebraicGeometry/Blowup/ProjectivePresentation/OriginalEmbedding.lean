/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.ProjectivePresentation.Embedding

/-!
# Projective embeddings of the original blowup scheme

Identity base change in the existing projective presentation embeds the SAME
ordinary blowup after its canonical pullback projection is inverted. The
original blowdown and structure triangle are retained. This is the one body
shared by normalized-chain embeddings and the next-point geometry consumer.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation

/-- The actual original blowup inherits a finite-coordinate closed embedding
from its locally Noetherian base, over the unchanged commutative ring.
No integrality, properness or Noetherianity of that ring is required. -/
theorem exists_original_projective_embedding
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {I : X.IdealSheafData} (B : BlowupDatum I)
    {R ι : Type u} [CommRing R] [Finite ι]
    (j : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion j] :
    ∃ (J : Type u) (_ : Finite J) (k : B.Y ⟶ ProjectiveSpace R J),
      IsClosedImmersion k ∧
        k ≫ ProjectiveSpace.toSpec R J =
          B.map ≫ j ≫ ProjectiveSpace.toSpec R ι := by
  obtain ⟨J, hJ, jB, hjB, hjBbase⟩ :=
    ProjectivePresentation.exists_projective_embedding B (𝟙 X) j
  let : Finite J := hJ
  let : IsClosedImmersion jB := hjB
  let q : pullback B.map (𝟙 X) ⟶ B.Y := pullback.fst B.map (𝟙 X)
  let : IsIso q := inferInstance
  let kB : B.Y ⟶ ProjectiveSpace R J := inv q ≫ jB
  let : IsClosedImmersion kB := by
    dsimp only [kB]
    infer_instance
  have hcondition : q ≫ B.map = pullback.snd B.map (𝟙 X) := by
    simpa only [Category.comp_id] using
      (pullback.condition (f := B.map) (g := 𝟙 X))
  have hsecond : inv q ≫ pullback.snd B.map (𝟙 X) = B.map := by
    rw [← hcondition, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have hBbase : kB ≫ ProjectiveSpace.toSpec R J =
      B.map ≫ j ≫ ProjectiveSpace.toSpec R ι := by
    change (inv q ≫ jB) ≫ ProjectiveSpace.toSpec R J = _
    rw [Category.assoc, hjBbase, ← Category.assoc (inv q), hsecond]
  exact ⟨J, hJ, kB, inferInstance, hBbase⟩

end AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation
