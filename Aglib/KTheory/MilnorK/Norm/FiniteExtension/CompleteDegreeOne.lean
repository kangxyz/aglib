/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.DVRResidueEquiv

/-!
# The actual degree-one norm-residue square

This is the degree-one base case for complete-DVR tower induction. The proof
is stronger than that application: completeness is not needed in degree one.
An equivalence of the actual fields restricts to their actual integral closures,
and uniqueness of integral closures supplies the specified extension DVR.
-/

@[expose] public noncomputable section

namespace MilnorK

open IsLocalRing

/-- The actual presentation-independent norm of a field over itself is identity. -/
theorem finiteExtensionNorm_self_apply (F : Type*) [Field F] [CharZero F]
    (n : ℕ) (x : K F n) : finiteExtensionNorm F F n x = x := by
  have h := finiteExtensionNorm_map_constants F F n x
  change finiteExtensionNorm F F n (map n (RingHom.id F) x) =
    (Module.finrank F F : ℤ) • x at h
  simpa only [map_id, LinearMap.id_apply, Module.finrank_self, Nat.cast_one, one_smul] using h

/-- The degree-one complete-DVR base case on any specified actual integral
closure. In degree one the conclusion does not require completeness. -/
theorem residue_finiteExtensionNorm_complete_degree_one
    (R F E S : Type*)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero (ResidueField R)]
    [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
    [Field E] [Algebra F E] [FiniteDimensional F E]
    [Algebra R E] [IsScalarTower R F E]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [Module.Finite R S] [IsLocalHom (algebraMap R S)]
    [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
    [IsIntegralClosure S R E]
    (hd : Module.finrank F E = 1) (n : ℕ) (x : K E (n + 1)) :
    DVR.residue R F n (finiteExtensionNorm F E (n + 1) x) =
      finiteExtensionNorm (ResidueField R) (ResidueField S) n (DVR.residue S E n x) := by
  let ε : F ≃ₐ[F] E := AlgEquiv.ofBijective (Algebra.ofId F E)
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hd)
  let j₀ : R ≃ₐ[R] integralClosure R F := IsIntegralClosure.equiv R R F _
  let j₁ : integralClosure R F ≃ₐ[R] integralClosure R E :=
    CompleteDVRResidueEquiv.closureEquiv R F ε
  let j₂ : integralClosure R E ≃ₐ[R] S := IsIntegralClosure.equiv R _ E S
  let j : R ≃ₐ[R] S := (j₀.trans j₁).trans j₂
  have hj (r : R) : ε (algebraMap R F r) = algebraMap S E (j r) := by
    dsimp only [j, AlgEquiv.trans_apply, j₂]
    rw [IsIntegralClosure.algebraMap_equiv]
    change ε (algebraMap R F r) = ε (algebraMap (integralClosure R F) F (j₀ r))
    rw [IsIntegralClosure.algebraMap_equiv]
  apply residue_finiteExtensionNorm_of_equiv j ε hj n (fun y => ?_) x
  rw [finiteExtensionNorm_self_apply]
  let : Algebra (ResidueField R) (ResidueField R) :=
    IsLocalRing.ResidueField.instAlgebra (R := R) (S := R)
  have hid : algebraMap (ResidueField R) (ResidueField R) = RingHom.id _ := by
    ext a
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective a
    rfl
  have hbij : Function.Bijective (algebraMap (ResidueField R) (ResidueField R)) := by
    rw [hid]
    exact Function.bijective_id
  have hdegree := Module.finrank_of_bijective_algebraMap hbij
  have h := finiteExtensionNorm_map_constants (ResidueField R) (ResidueField R) n
    (DVR.residue R F n y)
  rw [hid, map_id, LinearMap.id_apply, hdegree, Nat.cast_one, one_smul] at h
  exact h.symm

end MilnorK
