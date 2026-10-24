/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.IsAdjoinRoot
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.RingTheory.Etale.Kaehler

/-!
# The one-form differential trace for a degree-p presentation

For an actual presentation `S = R[z]/(z^p - a)`, polynomial differentiation
descends to an `R`-derivation of the original algebra `S`. Its Kähler lift
identifies `Ω[S⁄R]` with `S`, with `dz` mapping to one. Restriction from
`Ω[S⁄Λ]`, followed by this map, the coefficient of `z^(p-1)`, and multiplication
by `da`, defines the original `R`-linear one-form trace. The defining formulas
and their uniqueness include arbitrary coefficient rings of characteristic p.

Coordinate independence follows from an explicit polynomial coefficient identity.
The scalar-change equation compares the native Kähler maps, and localization
identifies the trace with the native localized linear map.

The exterior extension and the actual finite normal DVR models are separate
consumers. This file does not identify the map with a proper duality trace.
-/

@[expose] public noncomputable section

open Polynomial TensorProduct

namespace KaehlerDifferential

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {p : ℕ} [CharP R p] {a : R}

private theorem pureDegreeP_relation_derivative :
    derivative ((X : R[X]) ^ p - C a) = 0 := by
  simp [derivative_X_pow, CharP.cast_eq_zero]

/-- The defining ideal of the original presentation is preserved by differentiation. -/
theorem pureDegreeP_map_derivative_eq_zero
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a))
    (q : R[X]) (hq : h.map q = 0) : h.map (derivative q) = 0 := by
  obtain ⟨u, rfl⟩ := h.map_eq_zero_iff.mp hq
  rw [derivative_mul, pureDegreeP_relation_derivative, zero_mul, zero_add,
    map_mul, h.map_self, zero_mul]

/-- Polynomial differentiation descends through the original degree-p presentation. -/
def pureDegreePDerivation
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) : Derivation R S S :=
  Derivation.liftOfSurjective (f := h.map) h.map_surjective
    (d := Polynomial.derivative') (pureDegreeP_map_derivative_eq_zero h)

/-- The descended derivation is computed on the original presentation map. -/
@[simp]
theorem pureDegreePDerivation_map
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (q : R[X]) :
    pureDegreePDerivation h (h.map q) = h.map (derivative q) :=
  Derivation.liftOfSurjective_apply h.map_surjective
    (pureDegreeP_map_derivative_eq_zero h) q

/-- The chosen original root has derivative one. -/
@[simp]
theorem pureDegreePDerivation_root
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) :
    pureDegreePDerivation h h.root = 1 := by
  rw [← h.map_X, pureDegreePDerivation_map]
  simp

private theorem pureDegreeP_D_eq
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (s : S) :
    D R S s = pureDegreePDerivation h s • D R S h.root := by
  obtain ⟨q, rfl⟩ := h.map_surjective s
  rw [pureDegreePDerivation_map]
  simpa only [h.aeval_root_eq_map] using (D R S).map_aeval q h.root

/-- The original relative differential module is free on the differential of the root. -/
def pureDegreePDifferentialEquiv
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) :
    KaehlerDifferential R S ≃ₗ[S] S where
  __ := (pureDegreePDerivation h).liftKaehlerDifferential
  invFun s := s • D R S h.root
  left_inv ω := by
    change (pureDegreePDerivation h).liftKaehlerDifferential ω • D R S h.root = ω
    have hω : ω ∈ Submodule.span S (Set.range (D R S)) := by
      rw [span_range_derivation]
      trivial
    induction hω using Submodule.span_induction with
    | mem ω hω =>
      obtain ⟨s, rfl⟩ := hω
      rw [Derivation.liftKaehlerDifferential_comp_D]
      exact (pureDegreeP_D_eq h s).symm
    | zero => simp
    | add ω η _ _ hω hη => simp only [map_add, add_smul, hω, hη]
    | smul s ω _ hω => simp only [map_smul, smul_eq_mul, mul_smul, hω]
  right_inv s := by
    simp

/-- The relative equivalence carries each original differential to its descended derivative. -/
@[simp]
theorem pureDegreePDifferentialEquiv_D
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (s : S) :
    pureDegreePDifferentialEquiv h (D R S s) = pureDegreePDerivation h s :=
  Derivation.liftKaehlerDifferential_comp_D _ _

/-- The inverse equivalence is multiplication by the original root differential. -/
@[simp]
theorem pureDegreePDifferentialEquiv_symm_apply
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (s : S) :
    (pureDegreePDifferentialEquiv h).symm s = s • D R S h.root := rfl

/-- Extract the coefficient of `z^(p-1)` in the actual monic power basis. -/
def pureDegreePCoeff
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) : S →ₗ[R] R where
  toFun s := h.coeff s (p - 1)
  map_add' s t := congrFun (h.coeff.map_add s t) (p - 1)
  map_smul' r s := congrFun (h.coeff.map_smul r s) (p - 1)

/-- Coefficient extraction on each member of the original power basis. -/
theorem pureDegreePCoeff_root_pow [Fact p.Prime]
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) {i : ℕ} (hi : i < p) :
    pureDegreePCoeff h (h.root ^ i) = if i = p - 1 then 1 else 0 := by
  let : Nontrivial R :=
    CharP.nontrivial_of_char_ne_one (R := R) (Fact.out : p.Prime).ne_one
  have hi' : i < ((X : R[X]) ^ p - C a).natDegree := by
    simpa only [natDegree_X_pow_sub_C] using hi
  simpa only [pureDegreePCoeff, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.single_apply, eq_comm] using congrFun (h.coeff_root_pow hi') (p - 1)

section Tower

variable (Λ : Type*) [CommRing Λ] [Algebra Λ R] [Algebra Λ S]
  [IsScalarTower Λ R S]

/-- The one-form trace is the literal relative differential map, followed by the
root-derivative equivalence, power-basis coefficient, and multiplication by `da`. -/
def pureDegreePTraceOne
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) :
    KaehlerDifferential Λ S →ₗ[R] KaehlerDifferential Λ R :=
  (LinearMap.toSpanSingleton R (KaehlerDifferential Λ R) (D Λ R a)).comp
    ((pureDegreePCoeff h).comp
      (((pureDegreePDifferentialEquiv h).toLinearMap.restrictScalars R).comp
        ((map Λ R S S).restrictScalars R)))

/-- Evaluation exposes the original four maps without introducing a substitute trace. -/
theorem pureDegreePTraceOne_apply
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (ω : KaehlerDifferential Λ S) :
    pureDegreePTraceOne Λ h ω =
      pureDegreePCoeff h (pureDegreePDifferentialEquiv h (map Λ R S S ω)) • D Λ R a :=
  rfl

/-- Every `S`-multiple of a pulled-up form is killed. -/
@[simp]
theorem pureDegreePTraceOne_smul_map
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a))
    (s : S) (η : KaehlerDifferential Λ R) :
    pureDegreePTraceOne Λ h (s • map Λ Λ R S η) = 0 := by
  have hz : map Λ R S S (s • map Λ Λ R S η) = 0 := by
    have hm : mapBaseChange Λ R S (s ⊗ₜ[R] η) ∈ LinearMap.ker (map Λ R S S) := by
      rw [← range_mapBaseChange Λ R S]
      exact ⟨s ⊗ₜ[R] η, rfl⟩
    simpa only [LinearMap.mem_ker, mapBaseChange_tmul] using hm
  rw [pureDegreePTraceOne_apply, hz]
  simp

/-- The prescribed coefficient formula holds on the actual root differentials. -/
theorem pureDegreePTraceOne_root_pow_smul_D [Fact p.Prime]
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) {i : ℕ} (hi : i < p) :
    pureDegreePTraceOne Λ h (h.root ^ i • D Λ S h.root) =
      if i = p - 1 then D Λ R a else 0 := by
  rw [pureDegreePTraceOne_apply]
  simp only [map_smul, map_D, Algebra.algebraMap_self, RingHom.id_apply,
    pureDegreePDifferentialEquiv_D, pureDegreePDerivation_root, smul_eq_mul, mul_one]
  rw [pureDegreePCoeff_root_pow h hi]
  split_ifs <;> simp

/-- Maps on the actual differentials are determined by pulled-up forms and the
root power differentials. This includes rings with torsion in their Kähler modules. -/
theorem pureDegreePTraceOne_ext [Fact p.Prime]
    {M : Type*} [AddCommGroup M] [Module R M]
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a))
    (f g : KaehlerDifferential Λ S →ₗ[R] M)
    (hbase : ∀ (s : S) (η : KaehlerDifferential Λ R),
      f (s • map Λ Λ R S η) = g (s • map Λ Λ R S η))
    (hpow : ∀ i < p,
      f (h.root ^ i • D Λ S h.root) = g (h.root ^ i • D Λ S h.root)) : f = g := by
  let : Nontrivial R :=
    CharP.nontrivial_of_char_ne_one (R := R) (Fact.out : p.Prime).ne_one
  let j : S →ₗ[R] KaehlerDifferential Λ S :=
    (LinearMap.toSpanSingleton S (KaehlerDifferential Λ S) (D Λ S h.root)).restrictScalars R
  have hj : f.comp j = g.comp j := by
    apply h.basis.ext
    intro i
    change f (h.basis i • D Λ S h.root) = g (h.basis i • D Λ S h.root)
    rw [h.basis_apply]
    exact hpow i (by simpa only [natDegree_X_pow_sub_C] using i.isLt)
  have ht : ∀ v : S ⊗[R] KaehlerDifferential Λ R,
      f (mapBaseChange Λ R S v) = g (mapBaseChange Λ R S v) := by
    intro v
    induction v using TensorProduct.inductionOn with
    | tmul s η => simpa only [mapBaseChange_tmul] using hbase s η
    | add v w hv hw => simp only [map_add, hv, hw]
  apply LinearMap.ext
  intro ω
  let u := pureDegreePDifferentialEquiv h (map Λ R S S ω)
  have hu : u • D R S h.root = map Λ R S S ω :=
    (pureDegreePDifferentialEquiv h).symm_apply_apply (map Λ R S S ω)
  have hk : ω - u • D Λ S h.root ∈ LinearMap.ker (map Λ R S S) := by
    change map Λ R S S (ω - u • D Λ S h.root) = 0
    rw [map_sub, map_smul, map_D]
    change map Λ R S S ω - u • D R S h.root = 0
    rw [hu, sub_self]
  rw [← range_mapBaseChange Λ R S] at hk
  obtain ⟨v, hv⟩ := hk
  have hd := ht v
  rw [hv, map_sub, map_sub] at hd
  have hs : f (u • D Λ S h.root) = g (u • D Λ S h.root) :=
    LinearMap.congr_fun hj u
  rw [hs] at hd
  exact sub_left_inj.mp hd

/-- The actual trace is the unique map with the two defining formulas. -/
theorem pureDegreePTraceOne_unique [Fact p.Prime]
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a))
    (f : KaehlerDifferential Λ S →ₗ[R] KaehlerDifferential Λ R)
    (hbase : ∀ (s : S) (η : KaehlerDifferential Λ R), f (s • map Λ Λ R S η) = 0)
    (hpow : ∀ i < p, f (h.root ^ i • D Λ S h.root) =
      if i = p - 1 then D Λ R a else 0) : f = pureDegreePTraceOne Λ h := by
  apply pureDegreePTraceOne_ext Λ h f (pureDegreePTraceOne Λ h)
  · intro s η
    rw [hbase, pureDegreePTraceOne_smul_map]
  · intro i hi
    rw [hpow i hi, pureDegreePTraceOne_root_pow_smul_D Λ h hi]

end Tower

end KaehlerDifferential

namespace KaehlerDifferential

variable {p : ℕ} [Fact p.Prime]

private theorem coeff_pow_pred_mul_derivative_charZero
    {U : Type*} [CommRing U] [IsDomain U] [CharZero U]
    (q : U[X]) {k : ℕ} (hk : 0 < k) :
    (q ^ (p - 1) * derivative q).coeff (k * p - 1) =
      (k : U) * (q ^ p).coeff (k * p) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hi : k * p - 1 + 1 = k * p :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.mul_pos hk hp))
  have hi_cast := congrArg (fun n : ℕ => (n : U)) hi
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_mul] at hi_cast
  have hd := congrArg (fun f : U[X] => f.coeff (k * p - 1)) (derivative_pow q p)
  simp only [coeff_derivative, hi, mul_assoc, coeff_C_mul] at hd
  rw [hi_cast] at hd
  apply mul_left_cancel₀ (show (p : U) ≠ 0 from Nat.cast_ne_zero.mpr hp.ne')
  exact hd.symm.trans (by ring)

private theorem coeff_pow_pred_mul_derivative
    {R : Type*} [CommRing R] [CharP R p]
    (q : R[X]) {k : ℕ} (hk : 0 < k) :
    (q ^ (p - 1) * derivative q).coeff (k * p - 1) =
      (k : R) * (q.coeff k) ^ p := by
  let U := MvPolynomial R ℤ
  let e : U →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) id
  have he : Function.Surjective e := fun r =>
    ⟨MvPolynomial.X r, MvPolynomial.eval₂Hom_X' (Int.castRingHom R) id r⟩
  obtain ⟨Q, hQ⟩ := Polynomial.map_surjective e he q
  have h := congrArg e (coeff_pow_pred_mul_derivative_charZero (p := p) Q hk)
  have hl : e ((Q ^ (p - 1) * derivative Q).coeff (k * p - 1)) =
      (q ^ (p - 1) * derivative q).coeff (k * p - 1) := by
    rw [← coeff_map]
    simp only [Polynomial.map_mul, Polynomial.map_pow, ← derivative_map, hQ]
  have hr : e ((Q ^ p).coeff (k * p)) = (q.coeff k) ^ p := by
    rw [← coeff_map, Polynomial.map_pow, hQ, ← map_frobenius_expand p q,
      coeff_map, coeff_expand_mul (Fact.out : p.Prime).pos, frobenius_def]
  simpa only [map_mul, map_natCast, hl, hr] using h

variable {R : Type*} [CommRing R]

/-- A private polynomial coefficient selector for the existing trace calculation. -/
private def residueSection : R[X] →ₗ[R] R[X] where
  toFun q := (contract p (q * X)).divX
  map_add' q r := by
    ext n
    simp only [coeff_divX, coeff_contract (Fact.out : p.Prime).ne_zero,
      add_mul, coeff_add]
  map_smul' r q := by
    ext n
    simp only [coeff_divX, coeff_contract (Fact.out : p.Prime).ne_zero,
      smul_mul_assoc, coeff_smul, RingHom.id_apply]

private theorem residueSection_coeff (q : R[X]) (n : ℕ) :
    (residueSection (p := p) q).coeff n = q.coeff (n * p + (p - 1)) := by
  have hi : (n + 1) * p = (n * p + (p - 1)) + 1 := by
    rw [add_mul, one_mul, add_assoc, Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
  change ((contract p (q * X)).divX).coeff n = _
  rw [coeff_divX, coeff_contract (Fact.out : p.Prime).ne_zero, hi, coeff_mul_X]

private theorem residueSection_mul_expand (q r : R[X]) :
    residueSection (p := p) (q * expand R p r) = residueSection (p := p) q * r := by
  have hc : (contract p (q * X)).coeff 0 = 0 := by
    rw [coeff_contract (Fact.out : p.Prime).ne_zero]
    simp
  have he : contract p (q * X) = residueSection (p := p) q * X := by
    change contract p (q * X) = (contract p (q * X)).divX * X
    have hd : (contract p (q * X)).divX * X + C ((contract p (q * X)).coeff 0) =
        contract p (q * X) := divX_mul_X_add (contract p (q * X))
    rw [hc, C_0, add_zero] at hd
    exact hd.symm
  change (contract p ((q * expand R p r) * X)).divX = _
  rw [show (q * expand R p r) * X = (q * X) * expand R p r by ring,
    contract_mul_expand (Fact.out : p.Prime).ne_zero, he]
  rw [show (residueSection (p := p) q * X) * r =
      (residueSection (p := p) q * r) * X by ring]
  ext n
  simp only [coeff_divX, coeff_mul_X]

private theorem residueSection_of_natDegree_lt (q : R[X]) (hq : q.natDegree < p) :
    residueSection (p := p) q = C (q.coeff (p - 1)) := by
  ext n
  cases n with
  | zero => simp only [residueSection_coeff, zero_mul, zero_add, coeff_C_zero]
  | succ n =>
    rw [residueSection_coeff, coeff_C_succ]
    apply coeff_eq_zero_of_natDegree_lt
    apply hq.trans_le
    rw [Nat.succ_mul]
    omega

private theorem residueSection_relation_eval (a : R) (q : R[X]) :
    (residueSection (p := p) (q * (X ^ p - C a))).eval a = 0 := by
  have he : expand R p (X - C a) = X ^ p - C a := by simp
  rw [← he, residueSection_mul_expand, eval_mul, eval_sub, eval_X, eval_C, sub_self,
    mul_zero]

private theorem residueSection_top [CharP R p] (q : R[X]) :
    residueSection (p := p) (q ^ (p - 1) * derivative q) =
      derivative (q.map (frobenius R p)) := by
  ext n
  have hi : n * p + (p - 1) = (n + 1) * p - 1 := by
    rw [add_mul, one_mul, Nat.add_sub_assoc (Fact.out : p.Prime).one_le]
  rw [residueSection_coeff, hi,
    coeff_pow_pred_mul_derivative q (Nat.succ_pos n), coeff_derivative,
    coeff_map, frobenius_def]
  simpa only [Nat.cast_succ] using
    (mul_comm (n.succ : R) ((q.coeff n.succ) ^ p))

variable {S : Type*} [CommRing S] [Algebra R S] [CharP R p] {a : R}

private theorem pureDegreePCoeff_map_residueSection
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (q : R[X]) :
    pureDegreePCoeff h (h.map q) = (residueSection (p := p) q).eval a := by
  let : Nontrivial R :=
    CharP.nontrivial_of_char_ne_one (R := R) (Fact.out : p.Prime).ne_one
  let f : R[X] := X ^ p - C a
  have hf : f ≠ 1 := by
    intro he
    have hd := congrArg Polynomial.natDegree he
    have hp := (Fact.out : p.Prime).ne_zero
    exact hp (by simpa only [f, natDegree_X_pow_sub_C, natDegree_one] using hd)
  have hr : (q %ₘ f).natDegree < p := by
    simpa only [f, natDegree_X_pow_sub_C] using natDegree_modByMonic_lt q h.monic hf
  have hv : (residueSection (p := p) q).eval a =
      (residueSection (p := p) (q %ₘ f)).eval a := by
    conv_lhs => rw [← modByMonic_add_div q f]
    rw [map_add, eval_add, mul_comm f (q /ₘ f)]
    change (residueSection (p := p) (q %ₘ f)).eval a +
      (residueSection (p := p) ((q /ₘ f) * (X ^ p - C a))).eval a = _
    rw [residueSection_relation_eval, add_zero]
  rw [hv, residueSection_of_natDegree_lt _ hr, eval_C]
  change (h.modByMonicHom (h.map q)).coeff (p - 1) = (q %ₘ f).coeff (p - 1)
  rw [h.modByMonicHom_map]

private theorem pureDegreePCoeff_top_change
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (q : R[X]) :
    pureDegreePCoeff h (h.map q ^ (p - 1) * pureDegreePDerivation h (h.map q)) =
      (derivative (q.map (frobenius R p))).eval a := by
  rw [pureDegreePDerivation_map, ← map_pow, ← map_mul,
    pureDegreePCoeff_map_residueSection, residueSection_top]

private theorem pureDegreePCoeff_derivation
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (s : S) :
    pureDegreePCoeff h (pureDegreePDerivation h s) = 0 := by
  let : Nontrivial R :=
    CharP.nontrivial_of_char_ne_one (R := R) (Fact.out : p.Prime).ne_one
  have he : (pureDegreePCoeff h).comp (pureDegreePDerivation h).toLinearMap = 0 := by
    apply h.basis.ext
    intro i
    have hi : (i : ℕ) < p := by
      simpa only [natDegree_X_pow_sub_C] using i.isLt
    have hpred : (i : ℕ) - 1 < p := (Nat.sub_le _ _).trans_lt hi
    have hne : (i : ℕ) - 1 ≠ p - 1 := by
      have hp := (Fact.out : p.Prime).two_le
      omega
    change pureDegreePCoeff h (pureDegreePDerivation h (h.basis i)) = 0
    rw [h.basis_apply, Derivation.leibniz_pow, pureDegreePDerivation_root]
    simp only [smul_eq_mul, mul_one, map_nsmul, pureDegreePCoeff_root_pow h hpred,
      ite_eq_right hne, nsmul_zero]
  exact LinearMap.congr_fun he s

private theorem pureDegreePCoeff_lower_change
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (s : S)
    {i : ℕ} (hi : i < p - 1) :
    pureDegreePCoeff h (s ^ i * pureDegreePDerivation h s) = 0 := by
  have hi' : i + 1 < p := by omega
  have hu : IsUnit ((i + 1 : ℕ) : R) :=
    (CharP.isUnit_natCast_iff (Fact.out : p.Prime)).mpr
      (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos i) hi')
  have hz := pureDegreePCoeff_derivation h (s ^ (i + 1))
  rw [Derivation.leibniz_pow, Nat.add_sub_cancel] at hz
  simp only [smul_eq_mul, map_nsmul] at hz
  rw [← Nat.cast_smul_eq_nsmul R, smul_eq_mul] at hz
  obtain ⟨u, hu⟩ := hu.exists_left_inv
  have he := congrArg (fun r : R => u * r) hz
  simpa only [← mul_assoc, hu, one_mul, mul_zero] using he

omit [Fact p.Prime] [CharP R p] in
private theorem pureDegreeP_root_pow
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) :
    h.root ^ p = algebraMap R S a := by
  have he := h.aeval_root_self
  simpa only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] using he

private theorem pureDegreeP_algebraMap_injective
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) :
    Function.Injective (algebraMap R S) := by
  let : Nontrivial R :=
    CharP.nontrivial_of_char_ne_one (R := R) (Fact.out : p.Prime).ne_one
  have hp : 0 < ((X : R[X]) ^ p - C a).natDegree := by
    simpa only [natDegree_X_pow_sub_C] using (Fact.out : p.Prime).pos
  let i : Fin ((X ^ p - C a : R[X]).natDegree) := ⟨0, hp⟩
  intro r s hrs
  have he : r • h.basis i = s • h.basis i := by
    simp only [Algebra.smul_def, hrs]
  have hc := congrArg (fun t : S => h.basis.repr t i) he
  simpa only [map_smul, Finsupp.smul_apply, h.basis.repr_self,
    Finsupp.single_eq_same, smul_eq_mul, mul_one] using hc

private theorem pureDegreeP_map_pow
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (q : R[X]) :
    h.map q ^ p = algebraMap R S ((q.map (frobenius R p)).eval a) := by
  rw [← map_pow, ← h.aeval_root_eq_map, ← map_frobenius_expand p q, map_expand,
    expand_aeval, pureDegreeP_root_pow h, aeval_algebraMap_apply_eq_algebraMap_eval]

section Tower

variable (Λ : Type*) [CommRing Λ] [Algebra Λ R] [Algebra Λ S]
  [IsScalarTower Λ R S]

omit [Fact p.Prime] in
private theorem pureDegreeP_D_pow (r : R) : D Λ R (r ^ p) = 0 := by
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul R]
  simp only [CharP.cast_eq_zero, zero_smul]

private theorem pureDegreeP_D_eval_frobenius (q : R[X]) (r : R) :
    D Λ R ((q.map (frobenius R p)).eval r) =
      (derivative (q.map (frobenius R p))).eval r • D Λ R r := by
  induction q using Polynomial.induction_on' with
  | add q q' hq hq' =>
    simp only [Polynomial.map_add, eval_add, map_add, hq, hq', add_smul]
  | monomial n c =>
    simp only [map_monomial, frobenius_def, eval_monomial, derivative_monomial]
    rw [Derivation.leibniz, pureDegreeP_D_pow Λ c, smul_zero, add_zero,
      Derivation.leibniz_pow]
    simp only [← Nat.cast_smul_eq_nsmul R, smul_smul, mul_assoc]

omit [Fact p.Prime] in
private theorem pureDegreePTraceOne_pow_smul_D_apply
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (s : S) (i : ℕ) :
    pureDegreePTraceOne Λ h (s ^ i • D Λ S s) =
      pureDegreePCoeff h (s ^ i * pureDegreePDerivation h s) • D Λ R a := by
  rw [pureDegreePTraceOne_apply]
  simp only [map_smul, map_D, Algebra.algebraMap_self, RingHom.id_apply,
    pureDegreePDifferentialEquiv_D, smul_eq_mul]

/-- This formula proves the coordinate calculation for every element of the actual
algebra having a specified pth power in the original coefficient ring. -/
theorem pureDegreePTraceOne_pow_smul_D_of_pow_eq
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a))
    (s : S) (c : R) (hs : s ^ p = algebraMap R S c) {i : ℕ} (hi : i < p) :
    pureDegreePTraceOne Λ h (s ^ i • D Λ S s) =
      if i = p - 1 then D Λ R c else 0 := by
  by_cases he : i = p - 1
  · subst i
    rw [ite_eq_left rfl]
    obtain ⟨q, rfl⟩ := h.map_surjective s
    have hc : (q.map (frobenius R p)).eval a = c :=
      pureDegreeP_algebraMap_injective h ((pureDegreeP_map_pow h q).symm.trans hs)
    rw [pureDegreePTraceOne_pow_smul_D_apply, pureDegreePCoeff_top_change,
      ← pureDegreeP_D_eval_frobenius, hc]
  · have hlt : i < p - 1 := by omega
    rw [ite_eq_right he, pureDegreePTraceOne_pow_smul_D_apply,
      pureDegreePCoeff_lower_change h s hlt, zero_smul]

end Tower

section NaturalMaps

variable (Λ : Type*) [CommRing Λ]

private theorem differential_map_map
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra Λ A] [Algebra Λ B] [Algebra Λ C]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower Λ A B] [IsScalarTower Λ B C] [IsScalarTower Λ A C]
    [IsScalarTower A B C] (η : KaehlerDifferential Λ A) :
    map Λ Λ B C (map Λ Λ A B η) = map Λ Λ A C η := by
  have he : ((map Λ Λ B C).restrictScalars A).comp (map Λ Λ A B) =
      map Λ Λ A C := by
    apply Derivation.liftKaehlerDifferential_unique
    apply Derivation.ext
    intro x
    change map Λ Λ B C (map Λ Λ A B (D Λ A x)) = map Λ Λ A C (D Λ A x)
    simp only [map_D, ← IsScalarTower.algebraMap_apply A B C]
  exact LinearMap.congr_fun he η

variable [Algebra Λ R] [Algebra Λ S] [IsScalarTower Λ R S]

variable {T : Type*} [CommRing T] [Algebra R T] [Algebra S T]
  [Algebra Λ T] [IsScalarTower R S T] [IsScalarTower Λ S T]
  [IsScalarTower Λ R T]

/-- The actual Kähler map for any map between two degree-p presentations
commutes with the one-form trace; no compatibility hypothesis is supplied. -/
theorem pureDegreePTraceOne_naturality
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a))
    {b : R} (h' : IsAdjoinRootMonic T ((X : R[X]) ^ p - C b)) :
    (pureDegreePTraceOne Λ h').comp ((map Λ Λ S T).restrictScalars R) =
      pureDegreePTraceOne Λ h := by
  apply pureDegreePTraceOne_unique Λ h
  · intro s η
    change pureDegreePTraceOne Λ h' (map Λ Λ S T (s • map Λ Λ R S η)) = 0
    rw [map_smul, ← IsScalarTower.algebraMap_smul T s, differential_map_map]
    exact pureDegreePTraceOne_smul_map Λ h' (algebraMap S T s) η
  · intro i hi
    have hx : (algebraMap S T h.root) ^ p = algebraMap R T a := by
      rw [← map_pow, pureDegreeP_root_pow h, ← IsScalarTower.algebraMap_apply R S T]
    change pureDegreePTraceOne Λ h'
      (map Λ Λ S T (h.root ^ i • D Λ S h.root)) = _
    rw [map_smul, map_D, ← IsScalarTower.algebraMap_smul T (h.root ^ i), map_pow]
    exact pureDegreePTraceOne_pow_smul_D_of_pow_eq Λ h' (algebraMap S T h.root) a hx hi

section BaseChange

variable {R' : Type*} [CommRing R'] [Algebra R R'] [Algebra R' T]
  [Algebra Λ R'] [IsScalarTower Λ R R'] [IsScalarTower Λ R' T]
  [IsScalarTower R R' T] [CharP R' p]

/-- Naturality for an actual scalar square, allowing the target presentation
to use any monogenic coordinate. -/
theorem pureDegreePTraceOne_baseChange
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a))
    {b : R'} (h' : IsAdjoinRootMonic T ((X : R'[X]) ^ p - C b)) :
    ((pureDegreePTraceOne Λ h').restrictScalars R).comp
        ((map Λ Λ S T).restrictScalars R) =
      (map Λ Λ R R').comp (pureDegreePTraceOne Λ h) := by
  apply pureDegreePTraceOne_ext Λ h
  · intro s η
    change pureDegreePTraceOne Λ h' (map Λ Λ S T (s • map Λ Λ R S η)) =
      map Λ Λ R R' (pureDegreePTraceOne Λ h (s • map Λ Λ R S η))
    rw [pureDegreePTraceOne_smul_map, map_zero, map_smul,
      ← IsScalarTower.algebraMap_smul T s, differential_map_map,
      ← differential_map_map Λ (A := R) (B := R') (C := T)]
    exact pureDegreePTraceOne_smul_map Λ h' (algebraMap S T s) (map Λ Λ R R' η)
  · intro i hi
    have hx : (algebraMap S T h.root) ^ p =
        algebraMap R' T (algebraMap R R' a) := by
      rw [← map_pow, pureDegreeP_root_pow h, ← IsScalarTower.algebraMap_apply R S T,
        IsScalarTower.algebraMap_apply R R' T]
    change pureDegreePTraceOne Λ h'
      (map Λ Λ S T (h.root ^ i • D Λ S h.root)) =
        map Λ Λ R R' (pureDegreePTraceOne Λ h (h.root ^ i • D Λ S h.root))
    rw [map_smul, map_D, ← IsScalarTower.algebraMap_smul T (h.root ^ i), map_pow,
      pureDegreePTraceOne_pow_smul_D_of_pow_eq Λ h' _ _ hx hi,
      pureDegreePTraceOne_root_pow_smul_D Λ h hi]
    split_ifs
    · exact (map_D Λ Λ R R' a).symm
    · exact (map_zero (map Λ Λ R R')).symm

/-- The actual localized linear map is the trace on the actual localized algebra.
The target presentation may use a different root. The required localization
instance is proved from the native Kähler localization instance. -/
theorem pureDegreePTraceOne_localization (U : Submonoid R)
    [IsLocalization U R']
    [IsLocalization (Algebra.algebraMapSubmonoid S U) T]
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a))
    {b : R'} (h' : IsAdjoinRootMonic T ((X : R'[X]) ^ p - C b)) :
    let _ : IsLocalizedModule (Algebra.algebraMapSubmonoid S U) (map Λ Λ S T) :=
      KaehlerDifferential.isLocalizedModule_map (R := Λ) (S := S) (T := T)
        (Algebra.algebraMapSubmonoid S U)
    let _ : IsLocalizedModule U ((map Λ Λ S T).restrictScalars R) :=
      IsLocalizedModule.restrictScalars U (map Λ Λ S T)
    IsLocalizedModule.mapExtendScalars U ((map Λ Λ S T).restrictScalars R)
        (map Λ Λ R R') R' (pureDegreePTraceOne Λ h) =
      pureDegreePTraceOne Λ h' := by
  let : IsLocalizedModule (Algebra.algebraMapSubmonoid S U) (map Λ Λ S T) :=
    KaehlerDifferential.isLocalizedModule_map (R := Λ) (S := S) (T := T)
      (Algebra.algebraMapSubmonoid S U)
  let : IsLocalizedModule U ((map Λ Λ S T).restrictScalars R) :=
    IsLocalizedModule.restrictScalars U (map Λ Λ S T)
  apply LinearMap.restrictScalars_injective R
  apply IsLocalizedModule.linearMap_ext U ((map Λ Λ S T).restrictScalars R) (map Λ Λ R R')
  apply LinearMap.ext
  intro ω
  change IsLocalizedModule.map U ((map Λ Λ S T).restrictScalars R)
      (map Λ Λ R R') (pureDegreePTraceOne Λ h) (((map Λ Λ S T).restrictScalars R) ω) =
        pureDegreePTraceOne Λ h' (((map Λ Λ S T).restrictScalars R) ω)
  rw [IsLocalizedModule.map_apply]
  exact (LinearMap.congr_fun (pureDegreePTraceOne_baseChange Λ h h') ω).symm

end BaseChange

end NaturalMaps

end KaehlerDifferential
