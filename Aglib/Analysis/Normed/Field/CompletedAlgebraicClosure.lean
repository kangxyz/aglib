/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Analysis.Normed.Field.Nontrivial
public import Aglib.Analysis.Normed.Field.CompletedAlgebraicClosure.Witness
public import Mathlib.Analysis.Normed.Field.Dense
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Field.Ultra
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-!
# The spectral-norm completion of the actual algebraic closure

Source: `R5Lab.Aglib.Analysis.Normed.Field.CompletedAlgebraicClosure`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. The actual objects, maps, norm choices,
universes, and stated hypotheses are retained.
-/

@[expose] public section

noncomputable section
universe u
namespace AlgebraicClosure.SpectralCompletion
variable (F : Type u) [NontriviallyNormedField F] [CompleteSpace F]
  [CharZero F] [IsUltrametricDist F]

/-- The algebraic closure of `F` on which the spectral norm is installed. -/
abbrev Algebraic := AlgebraicClosure F
instance algebraicNormedField : NormedField (Algebraic F) :=
  spectralNorm.normedField F (Algebraic F)
instance algebraicNormedAlgebra : NormedAlgebra F (Algebraic F) :=
  spectralNorm.normedAlgebra F (Algebraic F)
instance algebraicNontrivial : NontriviallyNormedField (Algebraic F) :=
  spectralNorm.nontriviallyNormedField F (Algebraic F)
instance algebraicUltrametric : IsUltrametricDist (Algebraic F) :=
  IsUltrametricDist.of_normedAlgebra F
/-- The existing algebraic closure has its native characteristic-zero instance. -/
abbrev algebraicCharZero : CharZero (Algebraic F) := inferInstance

/-- The completion of the algebraic closure of `F` with its spectral norm. -/
abbrev Completed := UniformSpace.Completion (Algebraic F)
instance completedCharZero : CharZero (Completed F) :=
  (RingHom.charZero_iff (algebraMap (Algebraic F) (Completed F)).injective).mp inferInstance
instance completedUltrametric : IsUltrametricDist (Completed F) :=
  IsUltrametricDist.of_normedAlgebra (Algebraic F)
instance completedNontrivial : NontriviallyNormedField (Completed F) where
  toNormedField := inferInstance
  non_trivial := by
    obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := Algebraic F)
    exact ⟨algebraMap (Algebraic F) (Completed F) x, by simpa using hx⟩
instance completedAlgClosed : IsAlgClosed (Completed F) :=
  IsAlgClosed.of_denseRange UniformSpace.Completion.denseRange_coe

/-- The canonical ring embedding of `F` into the spectral-norm completion of its algebraic
closure. -/
def embedding : F →+* Completed F :=
  (algebraMap (Algebraic F) (Completed F)).comp (algebraMap F (Algebraic F))
instance embeddingIsometric : RingHomIsometric (embedding F) where
  norm_map {x} := by simp [embedding]

omit [CharZero F] in
@[nolint unusedArguments]
theorem dense_algebraic [CharZero F] : DenseRange (algebraMap (Algebraic F) (Completed F)) :=
  UniformSpace.Completion.denseRange_coe

omit [CharZero F] in
@[nolint unusedArguments]
theorem extends_embedding [CharZero F] :
    (algebraMap (Algebraic F) (Completed F)).comp (algebraMap F (Algebraic F)) =
      embedding F := rfl
/-- Construct the analytic comparison field from the original complete valued field
and its actual small unit. All field, norm, completeness and algebraic-closure
properties below are proved instances, not additional analytic premises. -/
theorem exists_completed_closure {F : Type u} [NormedField F] [CompleteSpace F]
    [CharZero F] [IsUltrametricDist F] (q : Fˣ) (hq : ‖(q : F)‖ < 1) :
    ∃ (K : Type u) (nf : NormedField K),
      letI := nf
      CompleteSpace K ∧ CharZero K ∧ IsUltrametricDist K ∧ IsAlgClosed K ∧
      ∃ f : F →+* K, RingHomIsometric f ∧
        ∃ i : AlgebraicClosure F →+* K,
          i.comp (algebraMap F (AlgebraicClosure F)) = f ∧ DenseRange i := by
  let : NontriviallyNormedField F := NormedField.nontrivialOfSmallUnit q hq
  refine ⟨Completed F, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, embedding F, inferInstance, algebraMap (Algebraic F) (Completed F),
    rfl, dense_algebraic F⟩
end AlgebraicClosure.SpectralCompletion
