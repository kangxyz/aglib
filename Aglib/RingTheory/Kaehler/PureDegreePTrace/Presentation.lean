/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kaehler.PureDegreePTrace
public import Mathlib.RingTheory.Derivation.MapCoeffs
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The actual monogenic differential presentation

Coefficient differentiation descends through the original presentation kernel.
Its Kähler lift and the relative root component give the actual differential
decomposition. No freeness of the base differential module is assumed.
-/

@[expose] public noncomputable section

open Polynomial TensorProduct

namespace KaehlerDifferential

variable {Λ R S : Type*} [CommRing Λ] [CommRing R] [CommRing S]
  [Algebra Λ R] [Algebra R S] [Algebra Λ S] [IsScalarTower Λ R S]
  {p : ℕ} {a : R}

local notation "P" => KaehlerDifferential Λ R
local notation "L" => Submodule.span R ({D Λ R a} : Set P)
local notation "Pbar" => P ⧸ L
local notation "E" => S ⊗[R] Pbar

/-- Differentiate the original coefficients into the actual quotient and tensor product. -/
def pureDegreePBaseDerivation : Derivation Λ R E :=
  (TensorProduct.mk R S Pbar 1).compDer ((Submodule.mkQ L).compDer (D Λ R))

/-- The relation coefficient has zero differential in the displayed quotient. -/
theorem pureDegreePBaseDerivation_relation :
    pureDegreePBaseDerivation (Λ := Λ) (S := S) (a := a) a = 0 := by
  have hz : (Submodule.mkQ L) (D Λ R a) = 0 :=
    (Submodule.Quotient.mk_eq_zero L).mpr (Submodule.subset_span (by simp))
  change (TensorProduct.mk R S Pbar 1) ((Submodule.mkQ L) (D Λ R a)) = 0
  rw [hz, map_zero]

/-- Evaluate coefficient-wise differentiation at the root of the original presentation. -/
def pureDegreePCoefficientPolynomial
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) : R[X] →ₗ[Λ] E :=
  ((PolynomialModule.eval h.root).restrictScalars Λ).comp
    (((PolynomialModule.coeffLinearEquiv S Λ (M := E)).symm.toLinearMap.comp
      (PolynomialModule.coeffLinearEquiv R Λ (M := E)).toLinearMap).comp
        (pureDegreePBaseDerivation (Λ := Λ) (S := S) (a := a)).mapCoeffs.toLinearMap)

/-- Changing the polynomial-module carrier preserves every actual coefficient. -/
theorem pureDegreePCoefficientPolynomial_apply
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (q : R[X]) :
    pureDegreePCoefficientPolynomial (Λ := Λ) h q =
      PolynomialModule.eval h.root
        (PolynomialModule.map S (LinearMap.id (R := R) (M := E))
          ((pureDegreePBaseDerivation (Λ := Λ) (S := S) (a := a)).mapCoeffs q)) := by
  rw [PolynomialModule.map, Finsupp.mapRange.linearMap_id, LinearMap.id_comp]
  rfl

/-- The coefficient map on an original monomial has the literal tensor formula. -/
theorem pureDegreePCoefficientPolynomial_monomial
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (i : ℕ) (r : R) :
    pureDegreePCoefficientPolynomial (Λ := Λ) h (monomial i r) =
      h.root ^ i • pureDegreePBaseDerivation (Λ := Λ) (S := S) (a := a) r := by
  rw [pureDegreePCoefficientPolynomial_apply, Derivation.mapCoeffs_monomial,
    PolynomialModule.map_single,
    PolynomialModule.eval_single, LinearMap.id_apply]

/-- The polynomial coefficient map agrees with differentiation on the original base ring. -/
@[simp]
theorem pureDegreePCoefficientPolynomial_C
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (r : R) :
    pureDegreePCoefficientPolynomial (Λ := Λ) h (C r) =
      pureDegreePBaseDerivation (Λ := Λ) (S := S) (a := a) r := by
  simpa only [monomial_zero_left, pow_zero, one_smul]
    using pureDegreePCoefficientPolynomial_monomial (Λ := Λ) h 0 r

/-- The root is constant for coefficient differentiation. -/
@[simp]
theorem pureDegreePCoefficientPolynomial_X_pow
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (n : ℕ) :
    pureDegreePCoefficientPolynomial (Λ := Λ) h (X ^ n) = 0 := by
  simpa only [← C_mul_X_pow_eq_monomial, C_1, one_mul,
    Derivation.map_one_eq_zero, smul_zero]
    using pureDegreePCoefficientPolynomial_monomial (Λ := Λ) h n 1

/-- The coefficient map obeys Leibniz with scalars from the original presentation. -/
theorem pureDegreePCoefficientPolynomial_mul
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (q r : R[X]) :
    pureDegreePCoefficientPolynomial (Λ := Λ) h (q * r) =
      h.map q • pureDegreePCoefficientPolynomial (Λ := Λ) h r +
        h.map r • pureDegreePCoefficientPolynomial (Λ := Λ) h q := by
  simp only [pureDegreePCoefficientPolynomial_apply]
  rw [Derivation.leibniz, map_add, map_add, PolynomialModule.map_smul,
    PolynomialModule.map_smul, PolynomialModule.eval_smul, PolynomialModule.eval_smul]
  simp only [Polynomial.eval_map, ← Polynomial.aeval_def, h.aeval_root_eq_map]

/-- Coefficient differentiation annihilates the actual defining equation. -/
theorem pureDegreePCoefficientPolynomial_relation
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) :
    pureDegreePCoefficientPolynomial (Λ := Λ) h (X ^ p - C a) = 0 := by
  rw [map_sub, pureDegreePCoefficientPolynomial_X_pow,
    pureDegreePCoefficientPolynomial_C, pureDegreePBaseDerivation_relation, sub_self]

/-- The actual kernel is killed, using its original principal presentation. -/
theorem pureDegreePCoefficientPolynomial_ker
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a))
    (q : R[X]) (hq : h.map q = 0) :
    pureDegreePCoefficientPolynomial (Λ := Λ) h q = 0 := by
  obtain ⟨r, rfl⟩ := h.map_eq_zero_iff.mp hq
  rw [pureDegreePCoefficientPolynomial_mul, h.map_self,
    pureDegreePCoefficientPolynomial_relation, zero_smul, smul_zero, add_zero]

/-- Descend coefficient differentiation to the original algebra. The kernel theorem
makes its value independent of the polynomial representative. -/
def pureDegreePCoefficientLinear
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) : S →ₗ[Λ] E where
  toFun s := pureDegreePCoefficientPolynomial (Λ := Λ) h (h.repr s)
  map_add' s t := by
    have hk := pureDegreePCoefficientPolynomial_ker (Λ := Λ) h
      (h.repr (s + t) - (h.repr s + h.repr t)) (by simp)
    exact sub_eq_zero.mp (by simpa only [map_sub, map_add] using hk)
  map_smul' r s := by
    change pureDegreePCoefficientPolynomial (Λ := Λ) h (h.repr (r • s)) =
      r • pureDegreePCoefficientPolynomial (Λ := Λ) h (h.repr s)
    have hz : h.map (h.repr (r • s) - r • h.repr s) = 0 := by
      rw [map_sub, h.map_repr]
      rw [h.map.map_smul_of_tower r (h.repr s), h.map_repr, sub_self]
    have hk := pureDegreePCoefficientPolynomial_ker (Λ := Λ) h
      (h.repr (r • s) - r • h.repr s) hz
    exact sub_eq_zero.mp (by simpa only [map_sub, map_smul] using hk)

/-- The descended map retains the value of every original polynomial. -/
@[simp]
theorem pureDegreePCoefficientLinear_map
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (q : R[X]) :
    pureDegreePCoefficientLinear (Λ := Λ) h (h.map q) =
      pureDegreePCoefficientPolynomial (Λ := Λ) h q := by
  have hk := pureDegreePCoefficientPolynomial_ker (Λ := Λ) h
    (h.repr (h.map q) - q) (by simp)
  change pureDegreePCoefficientPolynomial (Λ := Λ) h (h.repr (h.map q)) = _
  exact sub_eq_zero.mp (by simpa only [map_sub] using hk)

/-- The coefficient component is an actual derivation on the original algebra. -/
def pureDegreePCoefficientDerivation
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) : Derivation Λ S E where
  toLinearMap := pureDegreePCoefficientLinear (Λ := Λ) h
  map_one_eq_zero' := by
    have h1 : h.map (C (1 : R)) = 1 := by rw [C_1, map_one]
    rw [← h1, pureDegreePCoefficientLinear_map,
      pureDegreePCoefficientPolynomial_C, Derivation.map_one_eq_zero]
  leibniz' s t := by
    obtain ⟨q, rfl⟩ := h.map_surjective s
    obtain ⟨r, rfl⟩ := h.map_surjective t
    rw [← map_mul, pureDegreePCoefficientLinear_map,
      pureDegreePCoefficientPolynomial_mul, pureDegreePCoefficientLinear_map,
      pureDegreePCoefficientLinear_map]

/-- The coefficient derivation on the original base coefficients. -/
@[simp]
theorem pureDegreePCoefficientDerivation_algebraMap
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (r : R) :
    pureDegreePCoefficientDerivation (Λ := Λ) h (algebraMap R S r) =
      1 ⊗ₜ[R] (Submodule.mkQ L) (D Λ R r) := by
  change pureDegreePCoefficientLinear (Λ := Λ) h (algebraMap R S r) = _
  rw [h.algebraMap_apply, pureDegreePCoefficientLinear_map,
    pureDegreePCoefficientPolynomial_C]
  rfl

/-- The coefficient derivation kills the original chosen root. -/
@[simp]
theorem pureDegreePCoefficientDerivation_root
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) :
    pureDegreePCoefficientDerivation (Λ := Λ) h h.root = 0 := by
  change pureDegreePCoefficientLinear (Λ := Λ) h h.root = 0
  rw [← h.map_X, pureDegreePCoefficientLinear_map]
  simpa only [pow_one] using pureDegreePCoefficientPolynomial_X_pow (Λ := Λ) h 1

/-- The coefficient component is the universal Kähler lift, with source unchanged. -/
def pureDegreePCoefficientDifferential
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) :
    KaehlerDifferential Λ S →ₗ[S] E :=
  (pureDegreePCoefficientDerivation (Λ := Λ) h).liftKaehlerDifferential

@[simp]
theorem pureDegreePCoefficientDifferential_D
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (s : S) :
    pureDegreePCoefficientDifferential (Λ := Λ) h (D Λ S s) =
      pureDegreePCoefficientDerivation (Λ := Λ) h s :=
  Derivation.liftKaehlerDifferential_comp_D _ _

theorem pureDegreePCoefficientDifferential_map
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (η : P) :
    pureDegreePCoefficientDifferential (Λ := Λ) h (map Λ Λ R S η) =
      1 ⊗ₜ[R] (Submodule.mkQ L) η := by
  have he : ((pureDegreePCoefficientDifferential (Λ := Λ) h).restrictScalars R).comp
      (map Λ Λ R S) = (TensorProduct.mk R S Pbar 1).comp (Submodule.mkQ L) := by
    apply Derivation.liftKaehlerDifferential_unique
    apply Derivation.ext
    intro r
    change pureDegreePCoefficientDifferential (Λ := Λ) h
      (map Λ Λ R S (D Λ R r)) = 1 ⊗ₜ[R] (Submodule.mkQ L) (D Λ R r)
    rw [map_D, pureDegreePCoefficientDifferential_D,
      pureDegreePCoefficientDerivation_algebraMap]
  exact LinearMap.congr_fun he η

theorem pureDegreePCoefficientDifferential_root
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) :
    pureDegreePCoefficientDifferential (Λ := Λ) h (D Λ S h.root) = 0 := by
  rw [pureDegreePCoefficientDifferential_D, pureDegreePCoefficientDerivation_root]

section Characteristic

variable [CharP R p]

/-- The original map on differentials kills `da`, by differentiating the original relation. -/
theorem pureDegreeP_map_relation
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) :
    map Λ Λ R S (D Λ R a) = 0 := by
  have hroot : h.root ^ p = algebraMap R S a := by
    simpa only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] using h.aeval_root_self
  have hpS : (p : S) = 0 := by
    rw [← map_natCast (algebraMap R S), CharP.cast_eq_zero, map_zero]
  rw [map_D, ← hroot, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul S,
    hpS, zero_smul]

/-- The quotient of the original base differential map by its proved relation. -/
def pureDegreePQuotientDifferential
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) : Pbar →ₗ[R] KaehlerDifferential Λ S :=
  Submodule.liftQ L (map Λ Λ R S) (by
    rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
    exact pureDegreeP_map_relation (Λ := Λ) h)

theorem pureDegreePQuotientDifferential_mkQ
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (η : P) :
    pureDegreePQuotientDifferential (Λ := Λ) h ((Submodule.mkQ L) η) = map Λ Λ R S η :=
  Submodule.liftQ_apply _ _ _

/-- Extend the actual quotient differential map to its tensor product. -/
def pureDegreePBaseDifferential
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) : E →ₗ[S] KaehlerDifferential Λ S :=
  (pureDegreePQuotientDifferential (Λ := Λ) h).liftBaseChange S

@[simp]
theorem pureDegreePBaseDifferential_tmul
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (s : S) (η : Pbar) :
    pureDegreePBaseDifferential (Λ := Λ) h (s ⊗ₜ[R] η) =
      s • pureDegreePQuotientDifferential (Λ := Λ) h η :=
  LinearMap.liftBaseChange_tmul _ _ _ _

/-- The root component uses exactly the relative map and equivalence of the one-form prefix. -/
def pureDegreePRootDifferential
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) : KaehlerDifferential Λ S →ₗ[S] S :=
  (pureDegreePDifferentialEquiv h).toLinearMap.comp (map Λ R S S)

@[simp]
theorem pureDegreePRootDifferential_map
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (η : P) :
    pureDegreePRootDifferential (Λ := Λ) h (map Λ Λ R S η) = 0 := by
  have hz : map Λ R S S (map Λ Λ R S η) = 0 := by
    have hm : mapBaseChange Λ R S (1 ⊗ₜ[R] η) ∈ LinearMap.ker (map Λ R S S) := by
      rw [← range_mapBaseChange Λ R S]
      exact ⟨1 ⊗ₜ[R] η, rfl⟩
    simpa only [LinearMap.mem_ker, mapBaseChange_tmul, one_smul] using hm
  change pureDegreePDifferentialEquiv h (map Λ R S S (map Λ Λ R S η)) = 0
  rw [hz, map_zero]

@[simp]
theorem pureDegreePRootDifferential_root
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) :
    pureDegreePRootDifferential (Λ := Λ) h (D Λ S h.root) = 1 := by
  change pureDegreePDifferentialEquiv h (map Λ R S S (D Λ S h.root)) = 1
  rw [map_D]
  change pureDegreePDifferentialEquiv h (D R S h.root) = 1
  rw [pureDegreePDifferentialEquiv_D, pureDegreePDerivation_root]

/-- The two actual coefficient components of the original differential module. -/
def pureDegreePDifferentialSplit
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) :
    KaehlerDifferential Λ S →ₗ[S] E × S :=
  (pureDegreePCoefficientDifferential (Λ := Λ) h).prod
    (pureDegreePRootDifferential (Λ := Λ) h)

/-- Reassemble the quotient base differential and the actual root differential. -/
def pureDegreePDifferentialMerge
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) :
    E × S →ₗ[S] KaehlerDifferential Λ S :=
  (pureDegreePBaseDifferential (Λ := Λ) h).coprod
    (LinearMap.toSpanSingleton S (KaehlerDifferential Λ S) (D Λ S h.root))

theorem pureDegreePCoefficientDifferential_base
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (e : E) :
    pureDegreePCoefficientDifferential (Λ := Λ) h
      (pureDegreePBaseDifferential (Λ := Λ) h e) = e := by
  induction e using TensorProduct.inductionOn with
  | tmul s η =>
    refine Submodule.Quotient.induction_on L η ?_
    intro θ
    have hθ : pureDegreePQuotientDifferential (Λ := Λ) h (Submodule.Quotient.mk θ) =
        map Λ Λ R S θ := Submodule.liftQ_apply _ _ _
    rw [pureDegreePBaseDifferential_tmul, hθ,
      map_smul, pureDegreePCoefficientDifferential_map,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one, Submodule.mkQ_apply]
  | add e e' he he' => simp only [map_add, he, he']

theorem pureDegreePRootDifferential_base
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (e : E) :
    pureDegreePRootDifferential (Λ := Λ) h
      (pureDegreePBaseDifferential (Λ := Λ) h e) = 0 := by
  induction e using TensorProduct.inductionOn with
  | tmul s η =>
    refine Submodule.Quotient.induction_on L η ?_
    intro θ
    have hθ : pureDegreePQuotientDifferential (Λ := Λ) h (Submodule.Quotient.mk θ) =
        map Λ Λ R S θ := Submodule.liftQ_apply _ _ _
    rw [pureDegreePBaseDifferential_tmul, hθ,
      map_smul, pureDegreePRootDifferential_map, smul_zero]
  | add e e' he he' => simp only [map_add, he, he', add_zero]

theorem pureDegreePDifferentialSplit_merge
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (v : E × S) :
    pureDegreePDifferentialSplit (Λ := Λ) h
      (pureDegreePDifferentialMerge (Λ := Λ) h v) = v := by
  apply Prod.ext
  · change pureDegreePCoefficientDifferential (Λ := Λ) h
      (pureDegreePBaseDifferential (Λ := Λ) h v.1 + v.2 • D Λ S h.root) = v.1
    rw [map_add, pureDegreePCoefficientDifferential_base, map_smul,
      pureDegreePCoefficientDifferential_root, smul_zero, add_zero]
  · change pureDegreePRootDifferential (Λ := Λ) h
      (pureDegreePBaseDifferential (Λ := Λ) h v.1 + v.2 • D Λ S h.root) = v.2
    rw [map_add, pureDegreePRootDifferential_base, map_smul,
      pureDegreePRootDifferential_root, zero_add, smul_eq_mul, mul_one]

theorem pureDegreePBaseDifferential_mapTensor
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (v : S ⊗[R] P) :
    pureDegreePBaseDifferential (Λ := Λ) h (TensorProduct.map LinearMap.id (Submodule.mkQ L) v) =
      mapBaseChange Λ R S v := by
  induction v using TensorProduct.inductionOn with
  | tmul s η =>
    rw [TensorProduct.map_tmul, LinearMap.id_apply, pureDegreePBaseDifferential_tmul,
      pureDegreePQuotientDifferential_mkQ (Λ := Λ) h, mapBaseChange_tmul]
  | add v w hv hw => simp only [map_add, hv, hw]

theorem pureDegreePDifferentialMerge_surjective
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) :
    Function.Surjective (pureDegreePDifferentialMerge (Λ := Λ) h) := by
  intro ω
  let s := pureDegreePDifferentialEquiv h (map Λ R S S ω)
  have hs : s • D R S h.root = map Λ R S S ω :=
    (pureDegreePDifferentialEquiv h).symm_apply_apply (map Λ R S S ω)
  have hk : ω - s • D Λ S h.root ∈ LinearMap.ker (map Λ R S S) := by
    change map Λ R S S (ω - s • D Λ S h.root) = 0
    rw [map_sub, map_smul, map_D]
    change map Λ R S S ω - s • D R S h.root = 0
    rw [hs, sub_self]
  rw [← range_mapBaseChange Λ R S] at hk
  obtain ⟨v, hv⟩ := hk
  refine ⟨(TensorProduct.map LinearMap.id (Submodule.mkQ L) v, s), ?_⟩
  change pureDegreePBaseDifferential (Λ := Λ) h
    (TensorProduct.map LinearMap.id (Submodule.mkQ L) v) + s • D Λ S h.root = ω
  rw [pureDegreePBaseDifferential_mapTensor, hv, sub_add_cancel]

/-- The actual Kähler module has the required monogenic decomposition. Both
components and both inverse identities are constructed above. -/
def pureDegreePDifferentialDecomposition
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) :
    KaehlerDifferential Λ S ≃ₗ[S] E × S where
  __ := pureDegreePDifferentialSplit (Λ := Λ) h
  invFun := pureDegreePDifferentialMerge (Λ := Λ) h
  left_inv ω := by
    change pureDegreePDifferentialMerge (Λ := Λ) h
      (pureDegreePDifferentialSplit (Λ := Λ) h ω) = ω
    obtain ⟨v, rfl⟩ := pureDegreePDifferentialMerge_surjective (Λ := Λ) h ω
    rw [pureDegreePDifferentialSplit_merge]
  right_inv v := by
    change pureDegreePDifferentialSplit (Λ := Λ) h
      (pureDegreePDifferentialMerge (Λ := Λ) h v) = v
    exact pureDegreePDifferentialSplit_merge (Λ := Λ) h v

end Characteristic

end KaehlerDifferential
