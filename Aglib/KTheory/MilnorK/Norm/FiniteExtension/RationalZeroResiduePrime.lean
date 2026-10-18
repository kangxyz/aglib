/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.RationalTower
public import Aglib.KTheory.MilnorK.Norm.Polynomial.RationalPrime
public import Aglib.KTheory.MilnorK.Norm.Polynomial.RationalLinear
public import Aglib.KTheory.MilnorK.Residue.Polynomial.CoefficientEquiv

/-!
# The original rational zero-place norm square for normal prime extensions

The finite `X` residue is identified with the original coefficient field.
Literal coefficient equivalences transport this concrete map, and therefore
transport the proved root-presentation square to arbitrary actual finite
normal-prime extensions. The degree-one square is also proved directly.
-/

@[expose] public noncomputable section

namespace MilnorK

open Polynomial Polynomial.LocalResidue PolynomialResidue PolynomialNorm
open scoped RatFunc

attribute [local instance] Polynomial.algebra

universe u

local instance zeroPlaceIrreducible {A : Type*} [Field A] :
    Fact (Irreducible (X : A[X])) := ⟨irreducible_X⟩

/-- The actual finite `X` residue, normalized by its original coefficient-field
identification. -/
def rationalZeroResidue (k : Type*) [Field k] (n : ℕ) :
    K (RatFunc k) (n + 1) →ₗ[ℤ] K k n :=
  (map n (InfinityResidue.rootXEquiv k).toRingHom).comp (residueAt (X : k[X]) n)

/-- Coefficient naturality of the actual normalized finite residue. -/
theorem rationalZeroResidue_restrict {A B : Type*} [Field A] [Field B]
    (φ : A →+* B) (n : ℕ) (x : K (RatFunc A) (n + 1)) :
    rationalZeroResidue B n (map (n + 1) (fractionMap φ) x) =
      map n φ (rationalZeroResidue A n x) :=
  residueAt_X_restrict_normalized φ n x

local instance zeroRationalFinite {k E : Type u} [Field k] [Field E]
    [Algebra k E] [FiniteDimensional k E] : FiniteDimensional (RatFunc k) (RatFunc E) :=
  FiniteDimensional.of_finrank_pos (by
    rw [RatFunc.finrank_ratFunc_ratFunc]
    exact Module.finrank_pos)

local instance zeroRootFinite {k : Type u} [Field k] (p : MonicIrreducible k) :
    FiniteDimensional k (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot

/-- An actual coefficient-algebra equivalence transports an explicitly supplied
zero-place norm square. No norm compatibility is an input to the transport. -/
theorem rationalZeroResidue_norm_of_algEquiv
    {k A B : Type u} [Field k] [CharZero k] [Field A] [Field B]
    [Algebra k A] [Algebra k B] [FiniteDimensional k A] [FiniteDimensional k B]
    (φ : A ≃ₐ[k] B) (n : ℕ)
    (hsource : ∀ y : K (RatFunc A) (n + 1),
      rationalZeroResidue k n (finiteExtensionNorm (RatFunc k) (RatFunc A) (n + 1) y) =
        finiteExtensionNorm k A n (rationalZeroResidue A n y))
    (x : K (RatFunc B) (n + 1)) :
    rationalZeroResidue k n (finiteExtensionNorm (RatFunc k) (RatFunc B) (n + 1) x) =
      finiteExtensionNorm k B n (rationalZeroResidue B n x) := by
  let ε := fractionMapAlgEquiv φ
  have hex : ∃ y : K (RatFunc A) (n + 1), map (n + 1) ε.toRingHom y = x := by
    refine ⟨map (n + 1) ε.symm.toRingHom x, ?_⟩
    rw [← LinearMap.comp_apply, ← map_comp]
    have hi : ε.toRingHom.comp ε.symm.toRingHom = RingHom.id (RatFunc B) := by
      ext a
      exact ε.apply_symm_apply a
    rw [hi, map_id, LinearMap.id_apply]
  obtain ⟨y, rfl⟩ := hex
  rw [finiteExtensionNorm_map_algEquiv ε, hsource]
  change _ = finiteExtensionNorm k B n
    (rationalZeroResidue B n (map (n + 1) (fractionMap φ.toRingHom) y))
  rw [rationalZeroResidue_restrict, finiteExtensionNorm_map_algEquiv φ]

/-- The actual normalized zero-place square for every finite normal-prime
coefficient extension, not just a chosen polynomial root presentation. -/
theorem rationalZeroResidue_finiteExtensionNorm_prime
    {k : Type u} [Field k] [CharZero k] (L : Type u) [Field L]
    [Algebra k L] [FiniteDimensional k L] [Normal k L]
    (hp : (Module.finrank k L).Prime) (n : ℕ) (x : K (RatFunc L) (n + 1)) :
    rationalZeroResidue k n (finiteExtensionNorm (RatFunc k) (RatFunc L) (n + 1) x) =
      finiteExtensionNorm k L n (rationalZeroResidue L n x) := by
  let p := finiteNormPolynomial k L
  let ε := finiteNormPresentation k L
  let : Normal k (AdjoinRoot p.val) := Normal.of_algEquiv ε.symm
  have hdegree : p.val.natDegree = Module.finrank k L := by
    have h := ε.toLinearEquiv.finrank_eq
    rw [(AdjoinRoot.powerBasis p.property.2.ne_zero).finrank, AdjoinRoot.powerBasis_dim] at h
    exact h
  apply rationalZeroResidue_norm_of_algEquiv ε n _ x
  intro y
  unfold rationalZeroResidue
  simp only [LinearMap.comp_apply]
  rw [← rationalFunctionNorm_eq_finiteExtensionNorm p,
    finiteExtensionNorm_adjoinRoot p]
  exact residueAt_X_rationalFunctionNorm_prime p (hdegree ▸ hp) n y

/-- The actual normalized zero-place square for every degree-one coefficient
extension. Its proof transports the proved literal degree-one rational norm square. -/
theorem rationalZeroResidue_finiteExtensionNorm_degree_one
    {k : Type u} [Field k] [CharZero k] (L : Type u) [Field L]
    [Algebra k L] [FiniteDimensional k L]
    (hd : Module.finrank k L = 1) (n : ℕ) (x : K (RatFunc L) (n + 1)) :
    rationalZeroResidue k n (finiteExtensionNorm (RatFunc k) (RatFunc L) (n + 1) x) =
      finiteExtensionNorm k L n (rationalZeroResidue L n x) := by
  let p := finiteNormPolynomial k L
  let ε := finiteNormPresentation k L
  have hdegree : p.val.natDegree = 1 := by
    have h := ε.toLinearEquiv.finrank_eq
    rw [(AdjoinRoot.powerBasis p.property.2.ne_zero).finrank, AdjoinRoot.powerBasis_dim] at h
    exact h.trans hd
  apply rationalZeroResidue_norm_of_algEquiv ε n _ x
  intro y
  unfold rationalZeroResidue
  simp only [LinearMap.comp_apply]
  rw [← rationalFunctionNorm_eq_finiteExtensionNorm p,
    finiteExtensionNorm_adjoinRoot p]
  exact residueAt_X_rationalFunctionNorm_linear_normalized p hdegree n y

end MilnorK
