/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Analysis.Normed.Field.CompletedAlgebraicClosure
public import Aglib.FieldTheory.AlgebraicClosure.RelativeImage
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.Topology.Algebra.UniformRing

/-!
# Actual isometric automorphisms of the spectral completion

Source: `R5Lab.Aglib.Analysis.Normed.Field.CompletedAlgebraicClosure.Galois`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. The actual objects, maps, norm choices,
universes, and stated hypotheses are retained.
-/

@[expose] public section

noncomputable section
universe u
section CompletedGaloisActionConstruction

/-! # The actual norm-compatible Galois action on the chosen completed algebraic closure

The extension is constructed with `Completion.mapRingEquiv` after proving
spectral-norm invariance of each automorphism of the actual algebraic closure.
No continuity or completion-automorphism extension theorem is an input.
-/
noncomputable section
namespace AlgebraicClosure.SpectralCompletion
variable (F : Type u) [NontriviallyNormedField F] [CompleteSpace F]
  [CharZero F] [IsUltrametricDist F]

omit [CharZero F] in
/-- The original-field algebraic Galois automorphisms preserve the chosen actual
spectral norm. -/
theorem algebraicAutomorphism_isometry (σ : Algebraic F ≃ₐ[F] Algebraic F) :
    Isometry σ := by
  apply (AddMonoidHomClass.isometry_iff_norm σ).mpr
  intro x
  exact (spectralNorm_eq_of_equiv σ x).symm

/-- The constructed continuous extension of the actual algebraic automorphism. -/
def completedAutomorphism (σ : Algebraic F ≃ₐ[F] Algebraic F) :
    Completed F ≃+* Completed F :=
  UniformSpace.Completion.mapRingEquiv σ.toRingEquiv
    (algebraicAutomorphism_isometry F σ).continuous
    (algebraicAutomorphism_isometry F σ.symm).continuous

omit [CharZero F] in
@[simp, nolint unusedArguments] theorem completedAutomorphism_coe [CharZero F] (σ : Algebraic F
  ≃ₐ[F] Algebraic F)
    (x : Algebraic F) :
    completedAutomorphism F σ (algebraMap (Algebraic F) (Completed F) x) =
      algebraMap (Algebraic F) (Completed F) (σ x) := by
  exact UniformSpace.Completion.mapRingHom_coe
    (algebraicAutomorphism_isometry F σ).continuous x

omit [CharZero F] in
/-- Completion preserves the proved isometry. -/
@[nolint unusedArguments]
theorem completedAutomorphism_isometry [CharZero F] (σ : Algebraic F ≃ₐ[F] Algebraic F) :
    Isometry (completedAutomorphism F σ) :=
  UniformSpace.Completion.isometry_mapRingHom (algebraicAutomorphism_isometry F σ)

instance completedAutomorphism_isometric (σ : Algebraic F ≃ₐ[F] Algebraic F) :
    RingHomIsometric (completedAutomorphism F σ).toRingHom where
  norm_map {x} := (completedAutomorphism_isometry F σ).norm_map_of_map_zero (map_zero _) x

/-- It fixes the original-field embedding chosen for the completed algebraic closure. -/
@[simp] theorem completedAutomorphism_embedding (σ : Algebraic F ≃ₐ[F] Algebraic F)
    (x : F) : completedAutomorphism F σ (embedding F x) = embedding F x := by
  change completedAutomorphism F σ
    (algebraMap (Algebraic F) (Completed F) (algebraMap F (Algebraic F) x)) = _
  rw [completedAutomorphism_coe, σ.commutes]
  rfl

/-- In particular it fixes every original-field unit as an actual unit. -/
@[simp] theorem completedAutomorphism_unit (σ : Algebraic F ≃ₐ[F] Algebraic F)
    (q : Fˣ) :
    Units.map (completedAutomorphism F σ).toMonoidHom
      (Units.map (embedding F).toMonoidHom q) = Units.map (embedding F).toMonoidHom q := by
  apply Units.ext
  exact completedAutomorphism_embedding F σ q

/-- The extensions obey the original Galois composition law. -/
def completedGaloisAction : (Algebraic F ≃ₐ[F] Algebraic F) →* (Completed F ≃+* Completed F) where
  toFun := completedAutomorphism F
  map_one' := by
    apply RingEquiv.toRingHom_injective
    change UniformSpace.Completion.mapRingHom (RingHom.id (Algebraic F)) continuous_id =
      RingHom.id (Completed F)
    exact UniformSpace.Completion.mapRingHom_id
  map_mul' σ τ := by
    apply RingEquiv.toRingHom_injective
    change UniformSpace.Completion.mapRingHom (σ.toRingHom.comp τ.toRingHom)
      ((algebraicAutomorphism_isometry F σ).continuous.comp
        (algebraicAutomorphism_isometry F τ).continuous) =
      (UniformSpace.Completion.mapRingHom σ.toRingHom (algebraicAutomorphism_isometry F
        σ).continuous).comp
        (UniformSpace.Completion.mapRingHom τ.toRingHom (algebraicAutomorphism_isometry F
          τ).continuous)
    exact (UniformSpace.Completion.mapRingHom_comp
      (algebraicAutomorphism_isometry F σ).continuous
      (algebraicAutomorphism_isometry F τ).continuous).symm

omit [CharZero F] in
@[simp, nolint unusedArguments] theorem completedGaloisAction_apply [CharZero F] (σ : Algebraic
  F ≃ₐ[F] Algebraic F) :
    completedGaloisAction F σ = completedAutomorphism F σ := rfl

end AlgebraicClosure.SpectralCompletion

end
end CompletedGaloisActionConstruction


/- Source cluster: CompletedRelativeAction; source SHA256
  b710d9ff708bcd09df6843fe10ba7aee0daf8d1149bcffc97edc6d352c8b0c9e. -/
section CompletedRelativeActionConstruction

/-! # Action of the actual algebraic subfield on the chosen completed closure

The transport equivalence is tied to the original algebraic-closure embedding.
Every automorphism of this literal algebraic subfield therefore has a constructed
norm-compatible extension to the same chosen completed algebraic closure.
-/
noncomputable section
namespace AlgebraicClosure.SpectralCompletion
open IsAlgClosure
variable (F : Type u) [NontriviallyNormedField F] [CompleteSpace F]
  [CharZero F] [IsUltrametricDist F]

omit [CharZero F] in
theorem algebraMap_completed_eq_embedding : algebraMap F (Completed F) = embedding F := by
  ext x
  rfl

/-- Construct an ambient automorphism from every automorphism of the actual
algebraic elements, using the specified embedded algebraic closure. -/
def relativeCompletedAutomorphism
    (σ : (algebraicClosure F (Completed F)) ≃ₐ[F] (algebraicClosure F (Completed F))) :
    Completed F ≃+* Completed F :=
  completedAutomorphism F (algebraicAutomorphismLift F (Algebraic F) (Completed F) σ)

instance relativeCompletedAutomorphism_isometric
    (σ : (algebraicClosure F (Completed F)) ≃ₐ[F] (algebraicClosure F (Completed F))) :
    RingHomIsometric (relativeCompletedAutomorphism F σ).toRingHom :=
  completedAutomorphism_isometric F _

/-- Exact extension on the literal algebraic subfield. -/
@[simp] theorem relativeCompletedAutomorphism_algebraic
    (σ : (algebraicClosure F (Completed F)) ≃ₐ[F] (algebraicClosure F (Completed F)))
    (x : algebraicClosure F (Completed F)) :
    relativeCompletedAutomorphism F σ (x : Completed F) = (σ x : Completed F) := by
  let e := algebraicImageEquiv F (Algebraic F) (Completed F)
  have hx : algebraMap (Algebraic F) (Completed F) (e.symm x) = (x : Completed F) :=
    congrArg Subtype.val (e.apply_symm_apply x)
  rw [← hx]
  change completedAutomorphism F _ _ = _
  rw [completedAutomorphism_coe]
  exact algebraicAutomorphismLift_compatible F (Algebraic F) (Completed F) σ x

@[simp] theorem relativeCompletedAutomorphism_embedding
    (σ : (algebraicClosure F (Completed F)) ≃ₐ[F] (algebraicClosure F (Completed F)))
    (x : F) : relativeCompletedAutomorphism F σ (embedding F x) = embedding F x :=
  completedAutomorphism_embedding F _ x

theorem relativeCompletedAutomorphism_comp_embedding
    (σ : (algebraicClosure F (Completed F)) ≃ₐ[F] (algebraicClosure F (Completed F))) :
    (relativeCompletedAutomorphism F σ).toRingHom.comp (embedding F) = embedding F := by
  ext x
  exact relativeCompletedAutomorphism_embedding F σ x

end AlgebraicClosure.SpectralCompletion

end
end CompletedRelativeActionConstruction


/- Source cluster: CoordinateGaloisEquivariance; source SHA256
  86f2caaff406d940ea75f3267fe0fa5a771b0d12f79a57aba63de40ef029ea61. -/
