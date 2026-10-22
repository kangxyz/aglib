/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.SourceResidueTrdeg
public import Aglib.FieldTheory.SeparablyGenerated.EmbeddedField
public import Mathlib.RingTheory.Extension.Generators
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! # The actual residue field of the original source centre

The residue field is formed from the native localization at the actual centre.
Its embedding, essential finite type, separability, and field generators all
come from the original source and target maps.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace ParameterLocalization.SourceCentre

variable {R S B : Type*}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [CommRing B] [IsDomain B] [Algebra R B] [Algebra R S]
  [IsLocalHom (algebraMap R S)]

/-- The actual local source residue field embeds over the original residue field. -/
def residueEmbedding (χ : B →ₐ[R] S) :
    ResidueField (LocalSource χ) →ₐ[ResidueField R] ResidueField S :=
  ResidueField.mapAlgHom' (localPoint χ)

omit [IsDomain B] in
/-- The residue embedding agrees with the original source point on every coefficient. -/
@[simp] theorem residueEmbedding_algebraMap (χ : B →ₐ[R] S) (b : B) :
    residueEmbedding χ (algebraMap B (ResidueField (LocalSource χ)) b) =
      residue S (χ b) := by
  change residueEmbedding χ
    (residue (LocalSource χ) (algebraMap B (LocalSource χ) b)) = _
  rw [residueEmbedding, ResidueField.mapAlgHom'_residue, localPoint_algebraMap]

omit [IsDomain B] in
/-- Essential finite type is asserted over the residue field, not finite type
of the local source over the original coefficient ring. -/
theorem residue_essFiniteType (χ : B →ₐ[R] S) [Algebra.FiniteType R B] :
    Algebra.EssFiniteType (ResidueField R) (ResidueField (LocalSource χ)) := by
  let : Algebra.EssFiniteType R (LocalSource χ) := inferInstance
  let : Algebra.EssFiniteType R (ResidueField (LocalSource χ)) :=
    Algebra.EssFiniteType.comp R (LocalSource χ) _
  exact Algebra.EssFiniteType.of_comp R (ResidueField R) _

omit [IsDomain B] in
/-- Actual residual transcendental separability restricts to the source residue field. -/
theorem residue_isSeparablyGenerated (χ : B →ₐ[R] S) [Algebra.FiniteType R B]
    [Algebra.IsTranscendentalSeparable (ResidueField R) (ResidueField S)] :
    Algebra.IsSeparablyGenerated (ResidueField R) (ResidueField (LocalSource χ)) := by
  let : Algebra.EssFiniteType (ResidueField R) (ResidueField (LocalSource χ)) :=
    residue_essFiniteType χ
  exact Algebra.isSeparablyGenerated_of_algHom (residueEmbedding χ)

omit [IsDomain B] in
/-- The residues of the SAME original algebra generators generate the actual
source-centre residue field as a field. No unrelated choice of field generators occurs. -/
theorem residue_generators_adjoin_eq_top (χ : B →ₐ[R] S) {ι : Type*}
    (P : Algebra.Generators R B ι) :
    IntermediateField.adjoin (ResidueField R)
      (Set.range (fun i => algebraMap B (ResidueField (LocalSource χ)) (P.val i))) = ⊤ := by
  let E := IntermediateField.adjoin (ResidueField R)
    (Set.range (fun i => algebraMap B (ResidueField (LocalSource χ)) (P.val i)))
  have hP : Algebra.adjoin R (Set.range P.val) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.range_eq_top]
    exact P.aeval_val_surjective
  have hmem : ∀ b : B, algebraMap B (ResidueField (LocalSource χ)) b ∈ E := by
    have hle : Algebra.adjoin R (Set.range P.val) ≤
        (E.toSubalgebra.restrictScalars R).comap
          (IsScalarTower.toAlgHom R B (ResidueField (LocalSource χ))) := by
      apply Algebra.adjoin_le
      rintro _ ⟨i, rfl⟩
      exact IntermediateField.subset_adjoin _ _ (Set.mem_range_self i)
    rw [hP] at hle
    intro b
    exact hle (Algebra.mem_top)
  apply top_unique
  intro x _
  obtain ⟨z, rfl⟩ := residue_surjective x
  obtain ⟨⟨a, s⟩, hz⟩ := IsLocalization.surj (centre χ).primeCompl z
  have hs : algebraMap B (ResidueField (LocalSource χ)) (s : B) ≠ 0 := by
    change residue (LocalSource χ) (algebraMap B (LocalSource χ) (s : B)) ≠ 0
    exact (residue_ne_zero_iff_isUnit _).2
      (IsLocalization.map_units (LocalSource χ) s)
  have heq : residue (LocalSource χ) z *
      algebraMap B (ResidueField (LocalSource χ)) (s : B) =
      algebraMap B (ResidueField (LocalSource χ)) a := by
    change residue (LocalSource χ) z *
      residue (LocalSource χ) (algebraMap B (LocalSource χ) (s : B)) =
      residue (LocalSource χ) (algebraMap B (LocalSource χ) a)
    simpa only [map_mul] using congrArg (residue (LocalSource χ)) hz
  rw [(eq_div_iff hs).2 heq]
  exact E.div_mem (hmem a) (hmem s)

end ParameterLocalization.SourceCentre
