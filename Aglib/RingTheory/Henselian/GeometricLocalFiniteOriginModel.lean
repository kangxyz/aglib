/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.ResidueParameterBasis
public import Aglib.RingTheory.Henselian.ResidueParameterAnnihilator
public import Aglib.RingTheory.Henselian.MonicFiniteOriginModel
public import Aglib.RingTheory.Localization.FractionBase
public import Mathlib.RingTheory.Extension.Generators

/-!
# An actual finite origin model for an arbitrary geometric local henselization

Actual finite algebra generators descend to the prime quotient. A transcendence
basis among their residue values is lifted to those generators; localizing at
nonzero parameter polynomials gives the actual rational-function coefficient
field action. The coefficient triangle transports algebraicity to the localized
prime quotient and supplies genuine monic residue equations. The monic finite
reduction then constructs a common-universe finite local model over an actual
polynomial-origin henselization. Both localization equivalences and both
henselization equivalences are the proved native constructions.
-/

@[expose] public section

noncomputable section

universe u v

namespace GeometricLocalHenselization

variable (k : Type u) [Field k] (B : Type v) [CommRing B] [Algebra k B]

/-- The reduction model is constructed, not supplied as an approximation premise.
The field and actual tensor-local model live in the same common universe. -/
theorem exists_finite_origin_model [Algebra.FiniteType k B] (q : Ideal B) [q.IsPrime] :
    ∃ (F : Type (max u v)) (_ : Field F) (n : ℕ) (A : Type (max u v)) (_ : CommRing A)
      (_ : Algebra (Henselization (PolynomialLocalRing F n)) A)
      (_ : Module.Finite (Henselization (PolynomialLocalRing F n)) A) (_ : IsLocalRing A),
      Nonempty (Henselization (Localization.AtPrime q) ≃+* A) := by
  classical
  obtain ⟨n, ⟨G⟩⟩ := Algebra.FiniteType.iff_exists_generators.mp
    (inferInstance : Algebra.FiniteType k B)
  let z : Fin n → B := G.val
  have hz : Algebra.adjoin k (Set.range z) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact (AlgHom.range_eq_top _).2 G.aeval_val_surjective
  obtain ⟨s, _, t, ht, hb⟩ := ResidueParameterBasis.exists_residue_basis z q hz
  let parameters : s → B := fun a => z (t a)
  have hparameters : IsTranscendenceBasis k
      (fun a => Ideal.Quotient.mk q (parameters a)) := by
    simpa only [parameters, ht] using hb
  let P := MvPolynomial s k
  let := (ResidueParameterBasis.parameterMap (k := k) parameters).toRingHom.toAlgebra
  let : IsScalarTower k P B :=
    IsScalarTower.of_algHom (ResidueParameterBasis.parameterMap (k := k) parameters)
  have hq : q.comap (algebraMap P B) = ⊥ :=
    ResidueParameterBasis.parameterMap_comap_eq_bot q parameters hparameters.1
  let F := FractionRing P
  let B' := FractionBaseLocalization.BaseLocalized P B
  let q' := FractionBaseLocalization.selectedPrime P B q
  let : q'.IsPrime := FractionBaseLocalization.selectedPrime_isPrime P B q hq
  let z' : Fin n → B' := fun i => algebraMap B B' (z i)
  have hz' : Algebra.adjoin F (Set.range z') = ⊤ :=
    FractionBaseLocalization.adjoin_range_eq_top P B k z hz
  let g : B ⧸ q →+* B' ⧸ q' := FractionBaseLocalization.quotientMap P B q
  have heval : algebraMap P (B ⧸ q) =
      (MvPolynomial.aeval (fun a => Ideal.Quotient.mk q (parameters a))).toRingHom := by
    apply RingHom.ext
    intro f
    change Ideal.Quotient.mk q (MvPolynomial.aeval parameters f) = _
    exact MvPolynomial.comp_aeval_apply parameters (Ideal.Quotient.mkₐ k q) f
  have hfg : (algebraMap F (B' ⧸ q')).comp (algebraMap P F) =
      g.comp (MvPolynomial.aeval (fun a => Ideal.Quotient.mk q (parameters a))).toRingHom := by
    rw [← heval]
    exact FractionBaseLocalization.quotientMap_comp_algebraMap P B q
  have hi (i : Fin n) : IsIntegral F (Ideal.Quotient.mk q' (z' i)) := by
    change IsIntegral F (g (Ideal.Quotient.mk q (z i)))
    exact ResidueParameterAnnihilator.isIntegral_image hparameters (algebraMap P F) g
      (IsFractionRing.injective P F) hfg (Ideal.Quotient.mk q (z i))
  let Q := ResidueMonicEquations.equations (F := F) z' q'
  obtain ⟨hm, hd, hQ⟩ := ResidueMonicEquations.equations_spec z' q' hi
  obtain ⟨A, hA, aA, fA, lA, ⟨e⟩⟩ :=
    MonicFiniteReduction.exists_finite_origin_model z' Q q' hz' hm hd hQ
  let := hA
  let := aA
  let := fA
  let := lA
  refine ⟨F, inferInstance, n, A, hA, aA, fA, lA, ?_⟩
  exact ⟨(Henselization.equivOfRingEquiv
    (FractionBaseLocalization.localEquiv P B q hq).toRingEquiv).symm.trans e⟩

end GeometricLocalHenselization
