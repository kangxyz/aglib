/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.ResidueMinpoly
public import Aglib.KTheory.MilnorK.Norm.Polynomial.DVRCoprimeBaseChange
public import Aglib.RingTheory.DVRCharpolyBranchCount

/-!
# Actual ramification-weighted residue norm base change

The fiber count is proved by the characteristic polynomial of the full generic
tensor decomposition. Literal ramification squares convert it to the vertical
weights. No residue norm identity or branch-count equality is assumed.
-/

@[expose] public noncomputable section

namespace MilnorK

open Polynomial IsLocalRing
open scoped TensorProduct

universe u

variable (R F S E T L : Type u)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Field E]
  [Algebra R F] [IsFractionRing R F] [Algebra R S] [Algebra F E]
  [Algebra R E] [Algebra S E] [IsScalarTower R F E] [IsScalarTower R S E]
  [IsIntegralClosure S R E] [FiniteDimensional F E]
  [Module.IsTorsionFree R S] [Module.Finite R S] [IsLocalHom (algebraMap R S)]
  [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field L]
  [Algebra R T] [IsLocalHom (algebraMap R T)] [Algebra T L]
  [IsFractionRing T L] [Algebra F L] [Algebra R L]
  [IsScalarTower R T L] [IsScalarTower R F L]
  {ι : Type u} [Fintype ι] (D U : ι → Type u)
  [∀ i, Field (D i)] [∀ i, CommRing (U i)] [∀ i, IsDomain (U i)]
  [∀ i, IsDiscreteValuationRing (U i)]
  [∀ i, Algebra L (D i)] [∀ i, Algebra T (U i)]
  [∀ i, Algebra T (D i)] [∀ i, Algebra (U i) (D i)]
  [∀ i, IsScalarTower T L (D i)] [∀ i, IsScalarTower T (U i) (D i)]
  [∀ i, IsIntegralClosure (U i) T (D i)] [∀ i, FiniteDimensional L (D i)]
  [∀ i, IsFractionRing (U i) (D i)]
  [∀ i, Module.IsTorsionFree T (U i)] [∀ i, Module.Finite T (U i)]
  [∀ i, IsLocalHom (algebraMap T (U i))]
  [∀ i, Algebra S (U i)] [∀ i, Algebra R (U i)]
  [∀ i, IsScalarTower R S (U i)] [∀ i, IsScalarTower R T (U i)]
  [∀ i, IsLocalHom (algebraMap S (U i))] [∀ i, IsLocalHom (algebraMap R (U i))]
  [CharZero (ResidueField R)] [CharZero (ResidueField T)]

/-- The actual residue norms satisfy weighted base change through the full
finite generic tensor decomposition, with every ramification factor retained. -/
theorem residue_norm_weighted_baseChange
    (ε : (L ⊗[F] E) ≃ₐ[L] (∀ i, D i)) (θ : S)
    (hθ : ∀ i, algebraMap (U i) (D i) (algebraMap S (U i) θ) =
      ε (1 ⊗ₜ[F] (algebraMap S E θ)) i)
    {π : R} {ϖ : S} {τ : T}
    (hπ : Irreducible π) (hϖ : Irreducible ϖ) (hτ : Irreducible τ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (v : Tˣ) (a : ℕ) (ha : algebraMap R T π = (v : T) * τ ^ a)
    (B : PowerBasis (ResidueField R) (ResidueField S)) (hB : B.gen = IsLocalRing.residue S θ)
    (ρ : ∀ i, U i) (hρ : ∀ i, Irreducible (ρ i))
    (w z : ∀ i, (U i)ˣ) (b c : ι → ℕ)
    (hb : ∀ i, algebraMap S (U i) ϖ = (w i : U i) * ρ i ^ b i)
    (hc : ∀ i, algebraMap T (U i) τ = (z i : U i) * ρ i ^ c i)
    (n : ℕ) (x : K (ResidueField S) n) :
    a • map n (algebraMap (ResidueField R) (ResidueField T))
      (finiteExtensionNorm (ResidueField R) (ResidueField S) n x) =
      ∑ i, b i • finiteExtensionNorm (ResidueField T) (ResidueField (U i)) n
        (map n (ResidueField.map (algebraMap S (U i))) x) := by
  classical
  let : ∀ i, IsLocalHom (IsScalarTower.toAlgHom R S (U i)) := fun i =>
    ⟨fun x hx => IsUnit.of_map (algebraMap S (U i)) x hx⟩
  let φ := fun i => ResidueField.mapAlgHom' (IsScalarTower.toAlgHom R S (U i))
  have hφ (i : ι) : φ i B.gen = IsLocalRing.residue (U i) (algebraMap S (U i) θ) := by
    rw [hB]
    rfl
  have hφdegree (i : ι) : Module.finrank
      (IntermediateField.adjoin (ResidueField T)
        {IsLocalRing.residue (U i) (algebraMap S (U i) θ)}) (ResidueField (U i)) =
      Module.finrank (IntermediateField.adjoin (ResidueField T) {φ i B.gen})
        (ResidueField (U i)) :=
    congrArg (fun α : ResidueField (U i) => Module.finrank
      (IntermediateField.adjoin (ResidueField T) {α}) (ResidueField (U i))) (hφ i).symm
  have hepos : 0 < e := by
    by_contra h
    have hz : e = 0 := Nat.eq_zero_of_not_pos h
    apply hπ.not_isUnit
    apply IsUnit.of_map (algebraMap R S) π
    rw [he, hz, pow_zero, mul_one]
    exact u.isUnit
  have hsquare (i : ι) : e * b i = a * c i := by
    apply PolynomialNorm.ramification_square_of_uniformizer_equations (U := U i) (D := D i)
      (algebraMap R S) (algebraMap R T) (algebraMap S (U i)) (algebraMap T (U i))
      _ (hρ i) u v (w i) (z i) e a (b i) (c i) he ha (hb i) (hc i)
    ext r
    exact (IsScalarTower.algebraMap_apply R S (U i) r).symm.trans
      (IsScalarTower.algebraMap_apply R T (U i) r)
  apply finiteExtensionNorm_restrict_eq_weighted_residue_sum
    (fun i => ResidueField (U i)) B φ b a _ n x
  intro q
  have hhorizontal := Algebra.sum_residue_branch_degrees_eq_ramification
    R F S E T L D U ε θ (fun i => algebraMap S (U i) θ) hθ
    hπ hϖ u e he B hB hτ ρ hρ z c hc
  rw [← hB] at hhorizontal
  specialize hhorizontal q
  simp only [← hφ, hφdegree] at hhorizontal
  have hv := ramification_fiber_weight_conversion e a hepos
    (fun i => if minpoly (ResidueField T) (φ i B.gen) = q.val.val then b i else 0)
    (fun i => if minpoly (ResidueField T) (φ i B.gen) = q.val.val then c i else 0)
    (fun i => Module.finrank
      (IntermediateField.adjoin (ResidueField T) {φ i B.gen}) (ResidueField (U i)))
    (fun i => by split_ifs <;> simp_all only [mul_zero])
    (by simpa only [ite_mul, zero_mul] using hhorizontal)
  simpa only [ite_mul, zero_mul] using hv

end MilnorK
