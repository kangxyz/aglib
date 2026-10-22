/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.ProperSource
public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence.FiniteCover

/-!
# Properness from finite local sequence data

A proper source is refined by the actual local admissible sequences and their
maps are glued globally. The inverse protected restriction lifts the prescribed
dense map to this proper source, proving surjectivity and properness of the target.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u v

namespace AlgebraicGeometry.Scheme.Compactification

/-- Finite local sequence data on a proper source give an actual proper
surjective map to the target, hence properness of the target itself. -/
theorem exists_proper_surjective_of_finite_local_sequences
    {X P S : Scheme.{u}} [IsLocallyNoetherian X]
    (C : X.OpenCover.{v}) [Finite C.I₀] [∀ i, QuasiCompact (C.f i)]
    (U : X.Opens) [QuasiCompact U.ι] [IsSchemeTheoreticallyDominant U.ι]
    (pX : X ⟶ S) [IsProper pX] (pP : P ⟶ S)
    [IsSeparated pP] [LocallyOfFiniteType pP]
    (g : U.toScheme ⟶ P) (hg : DenseRange g)
    (B : C.I₀ → Scheme.{u}) (γ : ∀ i, B i ⟶ C.X i)
    (hγ : ∀ i, Blowup.AdmissibleSequence (C.f i ⁻¹ᵁ U) (γ i))
    (F : ∀ i, B i ⟶ P)
    (hbase : ∀ i, F i ≫ pP = γ i ≫ C.f i ≫ pX)
    (hagree : ∀ i, (γ i ⁻¹ᵁ C.f i ⁻¹ᵁ U).ι ≫ F i =
      (γ i ∣_ C.f i ⁻¹ᵁ U) ≫ (C.f i ∣_ U) ≫ g) :
    ∃ (Y : Scheme.{u}) (β : Y ⟶ X) (G : Y ⟶ P) (t : U.toScheme ⟶ Y),
      Blowup.AdmissibleSequence U β ∧ IsProper β ∧ IsProper (β ≫ pX) ∧
      IsProper G ∧ Surjective G ∧ IsProper pP ∧
      G ≫ pP = β ≫ pX ∧ t ≫ β = U.ι ∧ t ≫ G = g := by
  obtain ⟨Y, β, G, hβ, hp, hi, _hd, hbaseG, hU⟩ :=
    Blowup.AdmissibleSequence.exists_map_of_finite_cover C U pX pP g B γ hγ F
      hbase hagree
  let : IsProper β := hp
  let : IsIso (β ∣_ U) := hi
  let t := inv (β ∣_ U) ≫ (β ⁻¹ᵁ U).ι
  have htβ : t ≫ β = U.ι := by
    dsimp only [t]
    rw [Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  have htG : t ≫ G = g := by
    dsimp only [t]
    rw [Category.assoc, hU, IsIso.inv_hom_id_assoc]
  obtain ⟨hG, hs, hP⟩ := proper_of_dense_map_lift (β ≫ pX) pP G hbaseG g hg t htG
  exact ⟨Y, β, G, t, hβ, hp, inferInstance, hG, hs, hP, hbaseG, htβ, htG⟩

end AlgebraicGeometry.Scheme.Compactification
