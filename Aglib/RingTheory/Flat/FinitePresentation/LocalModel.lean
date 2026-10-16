/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Flat.LocalCriterion.Residue
public import Aglib.RingTheory.Flat.FinitePresentation.Relations
public import Aglib.RingTheory.Flat.FinitePresentation.Localization
public import Mathlib.RingTheory.Extension.Presentation.Core
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Noetherian models for flat finitely presented algebras over arbitrary local bases

## Extraction basis

Transferred from `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FibrewiseRegularity.lean`
at frozen dirty R5Lab revision `79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`79621aa63046ca16c5f98424d77f16bc8cd45b99a84ddc8bc561fc8f9ccfe923`.
Source line ranges: 1954–1981, 1989–2073, 2081–2275, 2283–2317.
The original rings, modules, canonical maps, universes and hypotheses are retained.
-/

@[expose] public section

noncomputable section
open TensorProduct LinearMap

namespace Algebra.FlatApproximation

variable {R S Rp Sp : Type*} [CommRing R] [CommRing S] [CommRing Rp] [CommRing Sp]
  [Algebra R S] [Algebra R Rp] [Algebra R Sp] [Algebra S Sp] [IsScalarTower R S Sp]
  [Algebra Rp Sp] [IsScalarTower R Rp Sp]
  [IsLocalRing Rp] [IsLocalRing Sp] [IsLocalHom (algebraMap Rp Sp)]
  [IsNoetherianRing Sp] [Module.Flat R S]

/-- A genuine residue-fibre injection for an ideal implies flatness of its
actual quotient after compatible base and target localizations. -/
theorem flat_localized_quotient_of_fibre_injective
    (U : Submonoid R) (V : Submonoid S) [IsLocalization U Rp] [IsLocalization V Sp]
    (I : Ideal S)
    (hf : Function.Injective ((I.subtype.restrictScalars R).lTensor
      (Rp ⧸ IsLocalRing.maximalIdeal Rp))) :
    Module.Flat Rp (Sp ⧸ I.map (algebraMap S Sp)) := by
  have : Module.Flat S Sp := IsLocalization.flat Sp V
  have : Module.Flat R Sp := Module.Flat.trans R S Sp
  have : Module.Flat Rp Sp := (Module.flat_iff_of_isLocalization Rp U Sp).mpr inferInstance
  have hlocalized := localized_ideal_subtype_lTensor_injective (A := R) (T := Sp)
    (K := Rp ⧸ IsLocalRing.maximalIdeal Rp) V I hf
  have hbase := lTensor_injective_over_localization (D := Rp)
    (K := Rp ⧸ IsLocalRing.maximalIdeal Rp) U
    ((I.map (algebraMap S Sp)).subtype.restrictScalars Rp) hlocalized
  exact Module.Flat.flat_quotient_of_residue_subtype_injective_noetherian
    (I.map (algebraMap S Sp)) hbase

end Algebra.FlatApproximation

namespace Algebra.FlatApproximation

/-- Flatness of the quotient at a chosen pair of primes, using the canonical
local map. The abstract rings here keep concrete tensor-localization instances
out of the approximation theorem's statement. -/
def PrimeQuotientFlat {C S : Type*} [CommRing C] [CommRing S] [Algebra C S]
    (p : Ideal C) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (J : Ideal S) : Prop :=
  letI := Localization.AtPrime.algebraOfLiesOver p q
  Module.Flat (Localization.AtPrime p)
    (Localization.AtPrime q ⧸ J.map (algebraMap S (Localization.AtPrime q)))

theorem primeQuotientFlat_of_fibre_injective {C S : Type*}
    [CommRing C] [CommRing S] [Algebra C S] [Module.Flat C S] [IsNoetherianRing S]
    (p : Ideal C) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (J : Ideal S)
    (hf : Function.Injective ((J.subtype.restrictScalars C).lTensor
      (Localization.AtPrime p ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime p)))) :
    PrimeQuotientFlat p q J := by
  let D := Localization.AtPrime p
  let T := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : IsLocalHom (algebraMap D T) := by
    rw [Localization.AtPrime.algebraMap_eq p q]
    exact Localization.isLocalHom_localRingHom _ _ _ _
  exact flat_localized_quotient_of_fibre_injective (R := C) (S := S)
    (Rp := D) (Sp := T) p.primeCompl q.primeCompl J hf

variable {A R B : Type*} [CommRing A] [CommRing R] [CommRing B]
  [Algebra A R] [Algebra A B] [IsLocalRing R]

/-- The point of an intermediate base induced by the fixed local limiting base. -/
def basePrime (C : Subalgebra A R) : Ideal C :=
  (IsLocalRing.maximalIdeal R).comap (algebraMap C R)

instance basePrime_isPrime (C : Subalgebra A R) : (basePrime C).IsPrime :=
  Ideal.IsPrime.comap _

/-- For a finite-type flat Noetherian presentation, flatness of the limiting
quotient descends to a single finite-type stage at every point over the chosen
point of the local base. This is the local flat-model result needed in the
fibrewise-regularity argument; it does not assert a globally flat stage. -/
theorem exists_fg_flat_local_quotients
    [IsLocalRing A] [IsLocalHom (algebraMap A R)] [IsNoetherianRing A]
    [Algebra.FiniteType A B] [Module.Flat A B]
    (I : Ideal B) [Module.Flat R (R ⊗[A] (B ⧸ I))] :
    ∃ (C : Subalgebra A R), C.FG ∧
      ∀ (q : Ideal (C ⊗[A] B)) [q.IsPrime] [q.LiesOver (basePrime C)],
        PrimeQuotientFlat (basePrime C) q
          (I.map (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B)) := by
  classical
  let K := A ⧸ IsLocalRing.maximalIdeal A
  let : Field K := Ideal.Quotient.field (IsLocalRing.maximalIdeal A)
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  let g : R ⊗[A] B →ₗ[R] R ⊗[A] (B ⧸ I) :=
    (Ideal.Quotient.mkₐ A I).toLinearMap.baseChange R
  have hex : Function.Exact ((I.subtype.restrictScalars A).baseChange R) g :=
    _root_.lTensor_exact R (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective
  have hg : Function.Surjective g := LinearMap.baseChange_surjective R I.mkQ_surjective
  obtain ⟨C, hC, hlift⟩ := exists_fg_universal_residue_relation_lifts
    (K := K) Ideal.Quotient.mk_surjective I.subtype g hex hg
  refine ⟨C, hC, ?_⟩
  intro q hq hqp
  let D := Localization.AtPrime (basePrime C)
  have : Algebra.FiniteType A C := ⟨(Subalgebra.fg_top C).mpr hC⟩
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing A C
  have : IsNoetherianRing (C ⊗[A] B) := Algebra.FiniteType.isNoetherianRing C (C ⊗[A] B)
  have hlocal : IsLocalHom (algebraMap A D) := by
    apply ((IsLocalRing.local_hom_TFAE (algebraMap A D)).out 5 1).mp
    rw [IsScalarTower.algebraMap_eq A C D, ← Ideal.comap_comap]
    change ((IsLocalRing.maximalIdeal D).under C).comap (algebraMap A C) = _
    rw [IsLocalization.AtPrime.under_maximalIdeal D (basePrime C)]
    change ((IsLocalRing.maximalIdeal R).comap (algebraMap C R)).comap (algebraMap A C) = _
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq A C R,
      IsLocalRing.maximalIdeal_comap]
  let L := D ⧸ IsLocalRing.maximalIdeal D
  let : Algebra K L := (IsLocalRing.ResidueField.map (algebraMap A D)).toAlgebra
  have : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq (fun a ↦ rfl)
  let : Module.Free K L := Module.Free.of_divisionRing K L
  have : Module.Flat K L := Module.Flat.of_free
  have hf := ideal_map_subtype_fibre_injective_of_relation_lifts (C := C) (K := K) (L := L) I hlift
  exact primeQuotientFlat_of_fibre_injective (basePrime C) q
    (I.map (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B)) hf

end Algebra.FlatApproximation

namespace Algebra.FlatApproximation

universe uR uS
variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]

/-- A localization of a coefficient algebra at the point induced by a local target
maps locally to that target. -/
def localCoefficientMap (A : Type*) [CommRing A] [Algebra A R] [IsLocalRing R] :
    Localization.AtPrime ((IsLocalRing.maximalIdeal R).comap (algebraMap A R)) →+* R :=
  IsLocalization.lift (M := ((IsLocalRing.maximalIdeal R).comap (algebraMap A R)).primeCompl)
    (g := algebraMap A R) (fun x ↦ by
    have hx : algebraMap A R x ∉ IsLocalRing.maximalIdeal R := x.property
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using hx)

@[simp] theorem localCoefficientMap_algebraMap (A : Type*) [CommRing A] [Algebra A R]
    [IsLocalRing R] (a : A) :
    localCoefficientMap (R := R) A (algebraMap A _ a) = algebraMap A R a :=
  IsLocalization.lift_eq _ _

instance localCoefficientMap_isLocal (A : Type*) [CommRing A] [Algebra A R]
    [IsLocalRing R] : IsLocalHom (localCoefficientMap (R := R) A) := by
  constructor
  intro x hx
  let p := (IsLocalRing.maximalIdeal R).comap (algebraMap A R)
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
  apply (IsLocalization.AtPrime.isUnit_mk'_iff _ p r s).mpr
  change algebraMap A R r ∉ IsLocalRing.maximalIdeal R
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  have he : algebraMap A R r = algebraMap A R s *
      localCoefficientMap (R := R) A (IsLocalization.mk' _ r s) :=
    (IsLocalization.lift_mk'_spec (S := Localization.AtPrime p)
      (g := algebraMap A R) _ _ _ _).mp rfl
  rw [he]
  exact (show IsUnit (algebraMap A R s) from by
    have hs : algebraMap A R s ∉ IsLocalRing.maximalIdeal R := s.property
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using hs).mul hx

/-- Any finite presentation over a local ring has a local Noetherian polynomial
model carrying a prescribed element. Flatness of the model is not asserted. -/
theorem exists_local_noetherian_polynomial_model [IsLocalRing R]
    [Algebra.FinitePresentation R S] (a : S) :
    ∃ (A : Type uR) (_ : CommRing A) (_ : Algebra A R) (_ : IsLocalRing A),
      IsNoetherianRing A ∧ IsLocalHom (algebraMap A R) ∧
      ∃ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) A))
        (b : MvPolynomial (Fin n) A)
        (e : R ⊗[A] (MvPolynomial (Fin n) A ⧸ I) ≃ₐ[R] S),
        e ((1 : R) ⊗ₜ[A] Ideal.Quotient.mk I b) = a := by
  classical
  let P := Algebra.Presentation.ofFinitePresentation R S
  obtain ⟨w, hw⟩ := P.algebraMap_surjective a
  let A₀ := Algebra.adjoin P.Core (w.coeffs : Set R)
  have : Algebra.FiniteType P.Core A₀ := Algebra.FiniteType.adjoin_of_finite (Finset.finite_toSet _)
  have : Algebra.FiniteType ℤ A₀ := Algebra.FiniteType.trans (R := ℤ) (S := P.Core) (A := A₀)
    inferInstance inferInstance
  have : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing ℤ A₀
  let p : Ideal A₀ := (IsLocalRing.maximalIdeal R).comap (algebraMap A₀ R)
  let A := Localization.AtPrime p
  let : Algebra A R := (localCoefficientMap (R := R) A₀).toAlgebra
  have : IsScalarTower A₀ A R := IsScalarTower.of_algebraMap_eq (by
    intro r
    exact (localCoefficientMap_algebraMap A₀ r).symm)
  let : Algebra A S := (algebraMap R S).comp (algebraMap A R) |>.toAlgebra
  have : IsScalarTower A R S := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have : P.HasCoeffs A := Algebra.Presentation.HasCoeffs.of_isScalarTower A₀
  have hwA : (w.coeffs : Set R) ⊆ Set.range (algebraMap A R) := by
    intro r hr
    refine ⟨algebraMap A₀ A ⟨r, Algebra.subset_adjoin hr⟩, ?_⟩
    rw [← IsScalarTower.algebraMap_apply A₀ A R]
    rfl
  obtain ⟨b, hb⟩ := MvPolynomial.mem_range_map_iff_coeffs_subset.mpr hwA
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstanceAs (IsLocalHom (localCoefficientMap (R := R) A₀)), _,
    Ideal.span (Set.range (P.relationOfHasCoeffs A)), b,
    P.tensorModelOfHasCoeffsEquiv A, ?_⟩
  rw [Algebra.Presentation.tensorModelOfHasCoeffsEquiv_tmul, map_one, one_mul]
  rw [← MvPolynomial.aeval_map_algebraMap R, hb]
  simpa only [Algebra.Generators.algebraMap_apply] using hw


/-- The local polynomial model of a flat algebra has a flat limiting quotient.
This is precisely the input for finite-stage local flatness. -/
theorem exists_local_noetherian_polynomial_model_of_flat [IsLocalRing R]
    [Algebra.FinitePresentation R S] [Module.Flat R S] (a : S) :
    ∃ (A : Type uR) (_ : CommRing A) (_ : Algebra A R) (_ : IsLocalRing A),
      IsNoetherianRing A ∧ IsLocalHom (algebraMap A R) ∧
      ∃ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) A))
        (b : MvPolynomial (Fin n) A)
        (e : R ⊗[A] (MvPolynomial (Fin n) A ⧸ I) ≃ₐ[R] S),
        Module.Flat R (R ⊗[A] (MvPolynomial (Fin n) A ⧸ I)) ∧
        e ((1 : R) ⊗ₜ[A] Ideal.Quotient.mk I b) = a := by
  obtain ⟨A, hA, hAR, hlocal, hNoeth, hhom, n, I, b, e, he⟩ :=
    exists_local_noetherian_polynomial_model (R := R) a
  exact ⟨A, hA, hAR, hlocal, hNoeth, hhom, n, I, b, e,
    Module.Flat.of_linearEquiv e.toLinearEquiv, he⟩

/-- After localizing any base at a prime, the actual base-changed algebra has
such a local Noetherian polynomial model, still carrying the prescribed element. -/
theorem exists_localized_noetherian_polynomial_model
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    (p : Ideal R) [p.IsPrime] (a : S) :
    ∃ (A : Type uR) (_ : CommRing A) (_ : Algebra A (Localization.AtPrime p))
      (_ : IsLocalRing A),
      IsNoetherianRing A ∧ IsLocalHom (algebraMap A (Localization.AtPrime p)) ∧
      ∃ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) A))
        (b : MvPolynomial (Fin n) A)
        (e : Localization.AtPrime p ⊗[A] (MvPolynomial (Fin n) A ⧸ I) ≃ₐ[Localization.AtPrime p]
          Localization.AtPrime p ⊗[R] S),
        Module.Flat (Localization.AtPrime p)
          (Localization.AtPrime p ⊗[A] (MvPolynomial (Fin n) A ⧸ I)) ∧
        e ((1 : Localization.AtPrime p) ⊗ₜ[A] Ideal.Quotient.mk I b) =
          (1 : Localization.AtPrime p) ⊗ₜ[R] a :=
  exists_local_noetherian_polynomial_model_of_flat ((1 : Localization.AtPrime p) ⊗ₜ[R] a)


/-- An actual prime of the original algebra determines a prime of the algebra
with localized base, lying over the closed point of that base. -/
theorem exists_prime_localizedBaseChange (q : Ideal S) [q.IsPrime] :
    let p := q.under R;
    ∃ (Q : Ideal (Localization.AtPrime p ⊗[R] S)), Q.IsPrime ∧
      Q.LiesOver (IsLocalRing.maximalIdeal (Localization.AtPrime p)) ∧
      Q.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] Localization.AtPrime p ⊗[R] S) = q := by
  let p := q.under R
  let Rp := Localization.AtPrime p
  let T := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : IsLocalHom (algebraMap Rp T) := by
    rw [Localization.AtPrime.algebraMap_eq p q]
    infer_instance
  let g : Rp ⊗[R] S →ₐ[R] T := Algebra.TensorProduct.lift
    (IsScalarTower.toAlgHom R Rp T) (IsScalarTower.toAlgHom R S T) (fun _ _ ↦ Commute.all _ _)
  let Q : Ideal (Rp ⊗[R] S) := (IsLocalRing.maximalIdeal T).comap g
  refine ⟨Q, inferInstance, ?_, ?_⟩
  · constructor
    apply Ideal.ext
    intro x
    change x ∈ IsLocalRing.maximalIdeal Rp ↔
      g (algebraMap Rp (Rp ⊗[R] S) x) ∈ IsLocalRing.maximalIdeal T
    change x ∈ IsLocalRing.maximalIdeal Rp ↔ g (x ⊗ₜ[R] 1) ∈ _
    simp only [g, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    change x ∈ IsLocalRing.maximalIdeal Rp ↔ algebraMap Rp T x ∈ _
    simpa only [Ideal.mem_comap] using
      (SetLike.ext_iff.mp (IsLocalRing.maximalIdeal_comap (algebraMap Rp T)) x).symm
  · apply Ideal.ext
    intro x
    change g (1 ⊗ₜ[R] x) ∈ IsLocalRing.maximalIdeal T ↔ x ∈ q
    simp only [g, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff T q x


section StagePrime
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A R] [Algebra A B]
  [Algebra A S] [IsScalarTower A R S]

/-- The actual map from a finite coefficient stage of a polynomial presentation
to the limiting algebra. -/
def modelStageMap (C : Subalgebra A R) (I : Ideal B)
    (e : R ⊗[A] (B ⧸ I) ≃ₐ[R] S) : C ⊗[A] B →ₐ[A] S :=
  (e.restrictScalars A).toAlgHom.comp
    (Algebra.TensorProduct.map C.val (Ideal.Quotient.mkₐ A I))

@[simp] theorem modelStageMap_tmul (C : Subalgebra A R) (I : Ideal B)
    (e : R ⊗[A] (B ⧸ I) ≃ₐ[R] S) (c : C) (b : B) :
    modelStageMap C I e (c ⊗ₜ[A] b) = e ((c : R) ⊗ₜ[A] Ideal.Quotient.mk I b) := rfl

theorem modelStageMap_algebraMap (C : Subalgebra A R) (I : Ideal B)
    (e : R ⊗[A] (B ⧸ I) ≃ₐ[R] S) (c : C) :
    modelStageMap C I e (algebraMap C (C ⊗[A] B) c) = algebraMap R S (c : R) := by
  change e ((c : R) ⊗ₜ[A] Ideal.Quotient.mk I 1) = _
  rw [map_one]
  exact e.commutes (c : R)

/-- Pulling back a prime through the actual finite-stage map preserves the
chosen base point and includes the extended presentation ideal. -/
theorem modelStageMap_prime (C : Subalgebra A R) (I : Ideal B)
    (e : R ⊗[A] (B ⧸ I) ≃ₐ[R] S) (Q : Ideal S) [Q.IsPrime] :
    (Q.comap (modelStageMap C I e)).IsPrime ∧
      (Q.comap (modelStageMap C I e)).LiesOver ((Q.under R).under C) ∧
      I.map (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B) ≤
        Q.comap (modelStageMap C I e) := by
  refine ⟨inferInstance, ?_, ?_⟩
  · constructor
    ext c
    change algebraMap R S (algebraMap C R c) ∈ Q ↔
      modelStageMap C I e (algebraMap C (C ⊗[A] B) c) ∈ Q
    rw [modelStageMap_algebraMap]
    rfl
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    change e ((1 : R) ⊗ₜ[A] Ideal.Quotient.mk I b) ∈ Q
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hb, tmul_zero, map_zero]
    exact Q.zero_mem

end StagePrime

end Algebra.FlatApproximation

namespace Algebra.FlatApproximation

universe uR uS
variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]

/-- A flat finitely presented algebra over a local base has an actual
Noetherian polynomial model carrying any prescribed element, and one finite
coefficient stage whose local quotient is flat at every point over the base
point. This uses no Noetherian hypothesis on the original base. -/
theorem exists_chosen_flat_local_model [IsLocalRing R]
    [Algebra.FinitePresentation R S] [Module.Flat R S] (a : S) :
    ∃ (A : Type uR) (_ : CommRing A) (_ : Algebra A R) (_ : IsLocalRing A),
      IsNoetherianRing A ∧ IsLocalHom (algebraMap A R) ∧
      ∃ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) A))
        (b : MvPolynomial (Fin n) A)
        (e : R ⊗[A] (MvPolynomial (Fin n) A ⧸ I) ≃ₐ[R] S),
        e ((1 : R) ⊗ₜ[A] Ideal.Quotient.mk I b) = a ∧
        ∃ (C : Subalgebra A R), C.FG ∧
          ∀ (q : Ideal (C ⊗[A] MvPolynomial (Fin n) A)) [q.IsPrime]
            [q.LiesOver (basePrime C)],
            PrimeQuotientFlat (basePrime C) q
              (I.map (Algebra.TensorProduct.includeRight :
                MvPolynomial (Fin n) A →ₐ[A] C ⊗[A] MvPolynomial (Fin n) A)) := by
  obtain ⟨A, hA, hAR, hlocal, hNoeth, hhom, n, I, b, e, hflat, he⟩ :=
    exists_local_noetherian_polynomial_model_of_flat (R := R) a
  let := hA
  let := hAR
  let := hlocal
  let := hNoeth
  let := hhom
  let := hflat
  refine ⟨A, hA, hAR, hlocal, hNoeth, hhom, n, I, b, e, he, ?_⟩
  exact exists_fg_flat_local_quotients I

end Algebra.FlatApproximation
