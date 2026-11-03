/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.LocalModification.ChainProperness
public import Aglib.AlgebraicGeometry.Blowup.ProjectivePresentation.OriginalEmbedding
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FiniteEmbedding
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Segre.ClosedComposition

/-!
# Projective embeddings of the original proper normalized-point chain

The actual proper total chain makes each literal normalization finite.
The existing blowup embedding and finite-map embedding then propagate the
original finite projective presentation along the same chain. The terminal
scheme and its original structural triangle are unchanged.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Blowup

private theorem exists_projective_embedding_aux
    {R : Type u} [CommRing R] {X T : Scheme.{u}} {f : T ⟶ X}
    (c : NormalizedPointBlowupChain f) :
    IsIntegral X → IsLocallyNoetherian X → IsProper f →
      ∀ {ι : Type u} [Finite ι] (j : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion j],
        ∃ (n : ℕ) (k : T ⟶ ProjectiveSpace R (ULift.{u} (Fin (n + 1)))),
          IsClosedImmersion k ∧
            k ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin (n + 1))) =
              f ≫ j ≫ ProjectiveSpace.toSpec R ι := by
  induction c with
  | refl X =>
    intro hX _hNoeth _hproper ι hι j hj
    let : IsIntegral X := hX
    let : Finite ι := hι
    let : IsClosedImmersion j := hj
    let : Nonempty ι := ProjectiveSpace.Segre.nonempty_coordinates_of_nonempty_source R j
    obtain ⟨n, k, hk, hbase⟩ :=
      ProjectiveSpace.FiniteEmbedding.exists_closedImmersion_of_isFinite j
    refine ⟨n, k, hk, ?_⟩
    simpa only [Category.id_comp] using hbase
  | @cons X T hX x hx hne g tail ih =>
    intro _hX hNoeth hproper ι hι j hj
    let : IsIntegral X := hX
    let : IsLocallyNoetherian X := hNoeth
    let : IsProper (g ≫ normalizedPointBlowupMap X x hx hne) := hproper
    let : Finite ι := hι
    let : IsClosedImmersion j := hj
    let B := blowupDatum (X.fromSpecResidueField x).ker
    let : IsIntegral B.Y := pointBlowup_isIntegral X x hx hne
    let : IsProper B.map := B.isProper_of_isLocallyNoetherian
    let N := normalizedPointBlowup X x hx hne
    let hN : IsIntegral N := normalizedPointBlowup_isIntegral X x hx hne
    let : IsIntegral N := hN
    let ν : N ⟶ B.Y := (B.Y.fromSpecStalk (genericPoint B.Y)).fromNormalization
    let : IsFinite ν := firstNormalization_isFinite_of_proper_chain x hx hne g tail
    have hp := firstStep_and_tail_isProper_of_proper_chain x hx hne g tail
    let : IsProper (normalizedPointBlowupMap X x hx hne) := hp.1
    have hNoethN : IsLocallyNoetherian N :=
      LocallyOfFiniteType.isLocallyNoetherian (normalizedPointBlowupMap X x hx hne)
    obtain ⟨J, hJ, kB, hkB, hBbase⟩ :=
      ProjectivePresentation.exists_original_projective_embedding B j
    let : Finite J := hJ
    let : IsClosedImmersion kB := hkB
    let : Nonempty J := ProjectiveSpace.Segre.nonempty_coordinates_of_nonempty_source R kB
    let : IsFinite (ν ≫ kB) := inferInstance
    obtain ⟨m, jN, hjN, hjNbase⟩ :=
      ProjectiveSpace.FiniteEmbedding.exists_closedImmersion_of_isFinite (ν ≫ kB)
    let : IsClosedImmersion jN := hjN
    obtain ⟨n, k, hk, hkbase⟩ := ih hN hNoethN hp.2 jN
    refine ⟨n, k, hk, ?_⟩
    calc
      k ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin (n + 1))) =
          g ≫ jN ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin (m + 1))) := hkbase
      _ = g ≫ ((ν ≫ kB) ≫ ProjectiveSpace.toSpec R J) :=
        congrArg (fun t => g ≫ t) hjNbase
      _ = (g ≫ (ν ≫ B.map)) ≫ j ≫ ProjectiveSpace.toSpec R ι := by
        rw [Category.assoc ν kB _, hBbase]
        simp only [Category.assoc]
      _ = (g ≫ normalizedPointBlowupMap X x hx hne) ≫
          j ≫ ProjectiveSpace.toSpec R ι := rfl

/-- A supplied proper normalized-point chain preserves an actual finite projective
embedding of its original base. The conclusion embeds the SAME terminal scheme
and retains the original structural map; no base Noetherianity is required. -/
theorem NormalizedPointBlowupChain.exists_projective_embedding
    {R : Type u} [CommRing R]
    {X T : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {f : T ⟶ X} (c : NormalizedPointBlowupChain f) [IsProper f]
    {ι : Type u} [Finite ι]
    (j : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion j] :
    ∃ (n : ℕ) (k : T ⟶ ProjectiveSpace R (ULift.{u} (Fin (n + 1)))),
      IsClosedImmersion k ∧
        k ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin (n + 1))) =
          f ≫ j ≫ ProjectiveSpace.toSpec R ι :=
  exists_projective_embedding_aux c inferInstance inferInstance inferInstance j

end AlgebraicGeometry.Scheme.Blowup
