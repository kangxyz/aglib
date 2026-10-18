/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.Mumford.Bound
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.Coordinate

/-!
# Hyperplane sections in the raising form

Mumford's induction (`Mumford/Bound.lean`) uses hyperplane sections in the form
`μ : O(-1) ⊗ - ⟶ 𝟭` (`HasHyperplaneSections`). Multiplication by a section `s` of `O(1)` is
more naturally the raising map `ν_s : M ≅ O(0) ⊗ M → O(1 + 0) ⊗ M`, the form of the chart
criterion `ProjectiveSpace.mono_twistingTensorMultiply_of_isSMulRegular`.
`HasHyperplaneSectionsUp` asks for a common monomorphic `ν : 𝟭 ⟶ O(1 + 0) ⊗ -`, and
`HasHyperplaneSections.of_up` converts it: `μ_M = ν_{O(-1) ⊗ M}` followed by
`O(1 + 0) ⊗ (O(-1) ⊗ M) ≅ M`. `hasHyperplaneSectionsUp_of_isSMulRegular` reduces the raising
form to regular frame coefficients on the chart subopens.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (k : Type u) [Field k] (ι : Type u)

/-- **Hyperplane sections in the raising form**: every pair of coherent modules has a common
monomorphic `ν : 𝟭 ⟶ O(1 + 0) ⊗ -`. -/
def HasHyperplaneSectionsUp : Prop :=
  ∀ G Q : (ProjectiveSpace k ι).Modules, affineLocallyFiniteType (ProjectiveSpace k ι) G →
    affineLocallyFiniteType (ProjectiveSpace k ι) Q →
      ∃ ν : 𝟭 (ProjectiveSpace k ι).Modules ⟶
          moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (((1 : ℕ) : ℤ) + 0)),
        Mono (ν.app G) ∧ Mono (ν.app Q)

/-- The degree equation `1 + 0 + -1 = 0`. -/
theorem raiseLowerDeg : ((1 : ℕ) : ℤ) + 0 + -1 = 0 := by norm_num

/-- `O(1 + 0) ⊗ (O(-1) ⊗ -) ≅ 𝟭`. -/
def raiseLowerIso :
    moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (-1)) ⋙
        moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (((1 : ℕ) : ℤ) + 0)) ≅
      𝟭 (ProjectiveSpace k ι).Modules :=
  twistingTensorCompIso k ι (((1 : ℕ) : ℤ) + 0) (-1) ≪≫
    eqToIso (by rw [raiseLowerDeg]) ≪≫ twistingTensorZeroIso k ι

variable {k ι}

/-- The raising form of hyperplane sections gives the lowering form used by Mumford's
induction. -/
theorem HasHyperplaneSections.of_up [Finite ι] (h : HasHyperplaneSectionsUp k ι) :
    HasHyperplaneSections k ι := by
  intro G Q hG hQ
  obtain ⟨ν, hνG, hνQ⟩ := h _ _ (twistingTensor_affineLocallyFiniteType k ι (-1) G hG)
    (twistingTensor_affineLocallyFiniteType k ι (-1) Q hQ)
  let T := moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (-1))
  refine ⟨(Functor.rightUnitor T).inv ≫ Functor.whiskerLeft T ν ≫ (raiseLowerIso k ι).hom,
    ?_, ?_⟩
  · change Mono ((Functor.rightUnitor T).inv.app G ≫ ν.app (T.obj G) ≫
      (raiseLowerIso k ι).hom.app G)
    infer_instance
  · change Mono ((Functor.rightUnitor T).inv.app Q ≫ ν.app (T.obj Q) ≫
      (raiseLowerIso k ι).hom.app Q)
    infer_instance

/-- **Hyperplane sections from regular frame coefficients**: if every pair of coherent modules
admits a global section `s` of `O(1)` whose frame coefficients `s / Xᵢ` are nonzerodivisors on
the sections of both modules over every subopen of every chart, hyperplane sections exist. -/
theorem hasHyperplaneSectionsUp_of_isSMulRegular
    (h : ∀ G Q : (ProjectiveSpace k ι).Modules, affineLocallyFiniteType (ProjectiveSpace k ι) G →
      affineLocallyFiniteType (ProjectiveSpace k ι) Q →
        ∃ s : (twistingSheaf k ι ((1 : ℕ) : ℤ)).val.obj (op ⊤),
          ∀ (i : ι) (V : (ProjectiveSpace k ι).Opens) (hV : V ≤ coordinateOpen k ι i),
            IsSMulRegular Γ(G, V) (frameCoefficient k ι s i hV) ∧
              IsSMulRegular Γ(Q, V) (frameCoefficient k ι s i hV)) :
    HasHyperplaneSectionsUp k ι := by
  intro G Q hG hQ
  obtain ⟨s, hs⟩ := h G Q hG hQ
  refine ⟨(twistingTensorZeroIso k ι).inv ≫ twistingTensorMultiply k ι ((1 : ℕ) : ℤ) 0 s, ?_, ?_⟩
  · exact mono_twistingTensorMultiply_of_isSMulRegular k ι s G fun i V hV => (hs i V hV).1
  · exact mono_twistingTensorMultiply_of_isSMulRegular k ι s Q fun i V hV => (hs i V hV).2

end AlgebraicGeometry.Scheme.Cohomology
