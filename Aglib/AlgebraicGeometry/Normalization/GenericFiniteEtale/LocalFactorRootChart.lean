/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.LocalFactor
public import Aglib.RingTheory.IntegralClosure.Inertia.StrictHenselianNormalForm

/-! # A root chart on the same pointed DVR normalization factor

An original regular action with globally invertible bounded order gives a root
chart on the specified maximal localization itself. The generic field and its
Galois structure are derived from the original inclusion. The final transfer is
the canonical integral-closure equivalence, preserving the original base map.
This is a strictly Henselian DVR theorem, not a higher-dimensional tame chart.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Algebra.Kummer
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.FiniteEtale.LocalFactor

universe u v

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  (A : Type u) [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [Algebra.Etale K A]
  (q : Ideal (integralClosure R A)) [q.IsMaximal]

local notation "S₀" => Localization.AtPrime q
local notation "L₀" => K ⊗[R] S₀

local instance : Module.Finite K A := Algebra.FormallyUnramified.finite_of_free K A
/-- The field structure on the generic local factor supplied by `genericField`. -/
local instance : Field L₀ := integralClosure.LocalFactor.genericField R K A q
local instance : Module.Finite K L₀ := integralClosure.LocalFactor.generic_finite R K A q
local instance : Algebra.Etale K L₀ := integralClosure.LocalFactor.generic_etale R K A q
/-- The right tensor-factor algebra structure on the generic local factor. -/
local instance : Algebra S₀ L₀ := Algebra.TensorProduct.rightAlgebra

variable (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
  {G : Type v} [Group G]
  (ρ : G →* Aut ((finiteEtaleSpecFunctor K).obj (op (CommAlgCat.FiniteEtale.of K A))))
  (z : Fiber (Spec.algebraMap K Ω) (genericCover R K A q))
  (hρ : Function.Bijective (fun a =>
    (fiberToFinite (Spec.algebraMap K Ω)).map (ρ a).hom
      ((fiberToFinite (Spec.algebraMap K Ω)).map (genericInclusion R K A q) z)))

include hρ in
/-- The original chosen normalization factor has a uniformizer-root chart.
The exponent divides the original acting-group bound, and the original base
uniformizer and rank equations hold on that same localization. -/
theorem exists_rootChart_of_regularAction
    (n d : ℕ) (hn : IsUnit (n : R)) (hcard : Nat.card G ∣ n ^ d)
    (π : R) (hπ : Irreducible π) :
    ∃ (e : ℕ) (E : RootAlgebra e π ≃ₐ[R] S₀),
      0 < e ∧ e ∣ n ^ d ∧ IsUnit (e : R) ∧
      Irreducible (E (AdjoinRoot.root (rootPolynomial e π))) ∧
      E (AdjoinRoot.root (rootPolynomial e π)) ^ e = algebraMap R S₀ π ∧
      Module.finrank R S₀ = e := by
  obtain ⟨hGalois, hdeck⟩ := genericField_isGalois_and_card_dvd R K A q Ω ρ z hρ
  let : _root_.IsGalois K L₀ := hGalois
  let : IsIntegralClosure S₀ R L₀ :=
    integralClosure.LocalFactor.generic_isIntegralClosure R K A q
  obtain ⟨e, E, he, hdvd, hunit, hirr, hpow, hrank⟩ :=
    integralClosure.Inertia.FiniteEtale.exists_rootChart_of_strictHenselian_of_card_dvd_pow
      R K L₀ n d hn (hdeck.trans hcard) π hπ
  let ε : integralClosure R L₀ ≃ₐ[R] S₀ :=
    IsIntegralClosure.equiv R (integralClosure R L₀) L₀ S₀
  refine ⟨e, E.trans ε, he, hdvd, hunit, ?_, ?_, ?_⟩
  · exact (MulEquiv.irreducible_iff ε.toMulEquiv).mpr hirr
  · change ε (E (AdjoinRoot.root (rootPolynomial e π))) ^ e = algebraMap R S₀ π
    exact (map_pow ε _ e).symm.trans
      ((congrArg ε hpow).trans (ε.commutes π))
  · exact ε.toLinearEquiv.finrank_eq.symm.trans hrank

end AlgebraicGeometry.Scheme.FiniteEtale.LocalFactor
