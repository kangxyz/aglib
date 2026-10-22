/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.LocalMonicFiniteOriginModel
public import Aglib.RingTheory.Henselian.LocalResidueMonicEquations
public import Aglib.RingTheory.Henselian.LocalResidueParameterBasis
public import Aglib.RingTheory.Henselian.FiniteBaseLocalizationResidue
public import Aglib.RingTheory.Henselian.ResidueParameterAnnihilator
public import Mathlib.RingTheory.Extension.Generators

/-!
# Actual finite models in the closed fibre of a DVR

The coefficient ring is the native parameter localization. The source is first
localized along its coefficient prime complement. The actual residue-field
identification supplies algebraicity, and coefficientwise monic lifts give a
finite polynomial action and the selected finite local henselization model.
-/

@[expose] public noncomputable section
universe u v w
namespace DVRGeometricLocalHenselization
open IsLocalRing

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (B : Type v) [CommRing B] [Algebra R B]
variable (q : Ideal B) [q.IsPrime]
variable (hq : q.comap (algebraMap R B) = maximalIdeal R)
variable (π : R) [Fact (Irreducible π)]

/-- The finite model after choosing actual residue parameters. This theorem
constructs both the localized source action and the monic equations. The actual
transcendence-basis property requires no separate `Finite σ` premise. -/
theorem exists_finite_model_of_residue_basis {n : ℕ} (z : Fin n → B)
    (hz : Algebra.adjoin R (Set.range z) = ⊤)
    {σ : Type w} (t : σ → B)
    (ht : let := LocalResidueParameterBasis.residueAlgebra q hq
      IsTranscendenceBasis (ResidueField R) (fun i => Ideal.Quotient.mk q (t i))) :
    ∃ (A : Type (max u v w)) (_ : CommRing A)
      (_ : Algebra (Henselization (PolynomialLocalRing
        (ParameterLocalization.Ring R σ π) n)) A)
      (_ : Module.Finite (Henselization (PolynomialLocalRing
        (ParameterLocalization.Ring R σ π) n)) A) (_ : IsLocalRing A),
      Nonempty (Henselization (Localization.AtPrime q) ≃+* A) := by
  classical
  let := LocalResidueParameterBasis.residueAlgebra q hq
  let P := MvPolynomial σ R
  let p := ParameterLocalization.parameterIdeal R σ π
  let R' := ParameterLocalization.Ring R σ π
  let : Algebra P B := (MvPolynomial.aeval t).toRingHom.toAlgebra
  let : IsScalarTower R P B := IsScalarTower.of_algHom (MvPolynomial.aeval t)
  have hqp : q.comap (algebraMap P B) = p :=
    LocalResidueParameterBasis.parameterMap_comap q hq t π ht.1
  let B' := FiniteBaseLocalization.BaseLocalized (B := B) p
  let q' := FiniteBaseLocalization.selectedPrime p q
  let : q'.IsPrime := FiniteBaseLocalization.selectedPrime_isPrime p q hqp
  have hq' : q'.comap (algebraMap R' B') = maximalIdeal R' :=
    FiniteBaseLocalization.selectedPrime_comap_base p q hqp
  let := LocalResidueParameterBasis.residueAlgebra q' hq'
  let k' := ResidueField R'
  let P₀ := MvPolynomial σ (ResidueField R)
  let K := FractionRing P₀
  let e : k' ≃+* K := ParameterLocalization.residueFieldRingEquiv R σ π
  let f : P₀ →+* k' := e.symm.toRingHom.comp (algebraMap P₀ K)
  let g : B ⧸ q →+* B' ⧸ q' := FiniteBaseLocalization.quotientMap p q
  have hf : Function.Injective f := e.symm.injective.comp (IsFractionRing.injective P₀ K)
  have hreduction : (Ideal.Quotient.mk q).comp (MvPolynomial.aeval t).toRingHom =
      (MvPolynomial.aeval (fun i => Ideal.Quotient.mk q (t i))).toRingHom.comp
        (MvPolynomial.map (residue R)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change Ideal.Quotient.mk q (MvPolynomial.aeval t (MvPolynomial.C r)) =
        MvPolynomial.aeval (fun i => Ideal.Quotient.mk q (t i))
          (MvPolynomial.map (residue R) (MvPolynomial.C r))
      rw [MvPolynomial.map_C, MvPolynomial.aeval_C, MvPolynomial.aeval_C]
      rfl
    · intro i
      simp
  have hfg : (algebraMap k' (B' ⧸ q')).comp f =
      g.comp (MvPolynomial.aeval (fun i => Ideal.Quotient.mk q (t i))).toRingHom := by
    apply RingHom.ext
    intro a
    obtain ⟨a, rfl⟩ := MvPolynomial.map_surjective (residue R) residue_surjective a
    have he : f (MvPolynomial.map (residue R) a) =
        residue R' (algebraMap P R' a) := by
      apply e.injective
      change e (e.symm (algebraMap P₀ K (MvPolynomial.map (residue R) a))) = _
      rw [RingEquiv.apply_symm_apply]
      exact (ParameterLocalization.residueFieldRingEquiv_polynomial R σ π a).symm
    change algebraMap k' (B' ⧸ q') (f (MvPolynomial.map (residue R) a)) = _
    rw [he]
    have hres := DFunLike.congr_fun (LocalResidueParameterBasis.residue_triangle q' hq')
      (algebraMap P R' a)
    change algebraMap k' (B' ⧸ q') (residue R' (algebraMap P R' a)) =
      algebraMap R' (B' ⧸ q') (algebraMap P R' a) at hres
    rw [hres]
    change algebraMap R' (B' ⧸ q') (algebraMap P R' a) =
      g (MvPolynomial.aeval (fun i => Ideal.Quotient.mk q (t i))
        (MvPolynomial.map (residue R) a))
    rw [show MvPolynomial.aeval (fun i => Ideal.Quotient.mk q (t i))
        (MvPolynomial.map (residue R) a) = Ideal.Quotient.mk q (MvPolynomial.aeval t a)
      from (DFunLike.congr_fun hreduction a).symm]
    exact DFunLike.congr_fun (FiniteBaseLocalization.quotientMap_comp_algebraMap p q) a
  let z' : Fin n → B' := fun i => algebraMap B B' (z i)
  have hz' : Algebra.adjoin R' (Set.range z') = ⊤ :=
    FiniteBaseLocalization.adjoin_range_eq_top p R z hz
  have hi (i : Fin n) : IsIntegral k' (Ideal.Quotient.mk q' (z' i)) := by
    change IsIntegral k' (g (Ideal.Quotient.mk q (z i)))
    exact ResidueParameterAnnihilator.isIntegral_image ht f g hf hfg _
  obtain ⟨Q, hm, hd, _, hQ⟩ := LocalResidueMonicEquations.exists_equations
    q' (residue R') residue_surjective
    (LocalResidueParameterBasis.residue_triangle q' hq') z' hi
  obtain ⟨A, hA, aA, fA, lA, ⟨eA⟩⟩ :=
    LocalMonicFiniteReduction.exists_finite_origin_model z' Q q' hz' hm hd hq' hQ
  refine ⟨A, hA, aA, fA, lA, ?_⟩
  exact ⟨(Henselization.equivOfRingEquiv
    (FiniteBaseLocalization.localEquiv p q hqp).toRingEquiv).symm.trans eA⟩

include hq π in
/-- Every vertical prime of a finite-type DVR algebra admits a constructed
finite local model over an actual parameter DVR's polynomial-origin
henselization. The coefficient inclusion is injective, so characteristic zero
of the original DVR is retained without any condition on its residue field. -/
theorem exists_finite_origin_model_with_uniformizer [Algebra.FiniteType R B] :
    ∃ (S : Type (max u v)) (_ : CommRing S) (_ : IsDomain S)
      (_ : IsDiscreteValuationRing S) (_ : Algebra R S),
      Function.Injective (algebraMap R S) ∧
      ∃ (n : ℕ) (A : Type (max u v)) (_ : CommRing A)
        (_ : Algebra (Henselization (PolynomialLocalRing S n)) A)
        (_ : Module.Finite (Henselization (PolynomialLocalRing S n)) A) (_ : IsLocalRing A),
        Nonempty (Henselization (Localization.AtPrime q) ≃+* A) := by
  classical
  obtain ⟨n, ⟨G⟩⟩ := Algebra.FiniteType.iff_exists_generators.mp
    (inferInstance : Algebra.FiniteType R B)
  let z : Fin n → B := G.val
  have hz : Algebra.adjoin R (Set.range z) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact (AlgHom.range_eq_top _).2 G.aeval_val_surjective
  let := LocalResidueParameterBasis.residueAlgebra q hq
  obtain ⟨s, hs, t, ht, hb⟩ := LocalResidueParameterBasis.exists_residue_basis q hq z hz
  let : Finite s := hs.to_subtype
  let parameters : s → B := fun a => z (t a)
  have hparameters : IsTranscendenceBasis (ResidueField R)
      (fun a => Ideal.Quotient.mk q (parameters a)) := by
    simpa only [parameters, ht] using hb
  let S := ParameterLocalization.Ring R s π
  let : IsDiscreteValuationRing S := ParameterLocalization.isDiscreteValuationRing R s π
  obtain ⟨A, hA, aA, fA, lA, eA⟩ :=
    exists_finite_model_of_residue_basis R B q hq π z hz parameters hparameters
  refine ⟨S, inferInstance, inferInstance, inferInstance, inferInstance,
    ParameterLocalization.algebraMap_injective R s π, n, A, hA, aA, fA, lA, eA⟩

include hq in
/-- The uniformizer is supplied by the DVR itself, not by a final theorem premise. -/
theorem exists_finite_origin_model [Algebra.FiniteType R B] :
    ∃ (S : Type (max u v)) (_ : CommRing S) (_ : IsDomain S)
      (_ : IsDiscreteValuationRing S) (_ : Algebra R S),
      Function.Injective (algebraMap R S) ∧
      ∃ (n : ℕ) (A : Type (max u v)) (_ : CommRing A)
        (_ : Algebra (Henselization (PolynomialLocalRing S n)) A)
        (_ : Module.Finite (Henselization (PolynomialLocalRing S n)) A) (_ : IsLocalRing A),
        Nonempty (Henselization (Localization.AtPrime q) ≃+* A) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let : Fact (Irreducible π) := ⟨hπ⟩
  exact exists_finite_origin_model_with_uniformizer R B q hq π

end DVRGeometricLocalHenselization
