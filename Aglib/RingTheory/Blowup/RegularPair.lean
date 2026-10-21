/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Localization.Away.SaturatedChart
public import Aglib.RingTheory.RegularLocalRing.Parameters
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Saturated blowup charts of a regular pair

For a regular pair `a, b`, the original quotient by `a * X - b` embeds in
`A[1/a]`, with image the actual saturated chart `A[(a,b)/a]`. In particular,
the quotient model has no denominator torsion. The forward comparison keeps
the original scalar map and sends the polynomial coordinate to `b/a`.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

universe u

namespace Localization.Away

variable {A : Type u} [CommRing A] (a b : A)

/-- The actual equation of the chart where the first generator divides the second. -/
def pairPolynomial : A[X] := C a * X - C b

/-- The polynomial quotient before comparison with the saturated chart. -/
abbrev pairQuotient := AdjoinRoot (pairPolynomial a b)

/-- The original polynomial coordinate in the quotient. -/
def pairCoordinate : pairQuotient a b := AdjoinRoot.root (pairPolynomial a b)

/-- The polynomial quotient satisfies the original generator equation. -/
theorem pairCoordinate_relation :
    algebraMap A (pairQuotient a b) a * pairCoordinate a b =
      algebraMap A (pairQuotient a b) b := by
  change AdjoinRoot.of (pairPolynomial a b) a * AdjoinRoot.root (pairPolynomial a b) =
    AdjoinRoot.of (pairPolynomial a b) b
  have h := AdjoinRoot.eval₂_root (pairPolynomial a b)
  change (C a * X - C b).eval₂ (AdjoinRoot.of (pairPolynomial a b))
    (AdjoinRoot.root (pairPolynomial a b)) = 0 at h
  simpa only [eval₂_sub, eval₂_mul, eval₂_C, eval₂_X, sub_eq_zero] using h

/-- Evaluation at the literal fraction in the actual localization. -/
def pairToLocalization : pairQuotient a b →ₐ[A] Localization.Away a :=
  AdjoinRoot.liftAlgHom (pairPolynomial a b) (Algebra.ofId A (Localization.Away a))
    (fraction a b) (by
      change (C a * X - C b).eval₂ (algebraMap A (Localization.Away a)) (fraction a b) = 0
      simp only [eval₂_sub, eval₂_mul, eval₂_C, eval₂_X]
      rw [mul_comm, fraction_mul_self, sub_self])

@[simp]
theorem pairToLocalization_coordinate : pairToLocalization a b (pairCoordinate a b) =
    fraction a b := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

private theorem pairPolynomial_dvd_of_C_mul_dvd
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (p : A[X]) (hp : pairPolynomial a b ∣ C a * p) : pairPolynomial a b ∣ p := by
  obtain ⟨g, hg⟩ := hp
  let q : A →+* A ⧸ Ideal.span {a} := Ideal.Quotient.mk (Ideal.span {a})
  have hqa : q a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hgm : C (q b) * g.map q = 0 := by
    have h := congrArg (Polynomial.map q) hg.symm
    simpa only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X,
      pairPolynomial, hqa, C_0, zero_mul, zero_sub, neg_mul, neg_eq_zero] using h
  have hgq : g.map q = 0 := by
    ext n
    apply hb.right_eq_zero_of_smul
    change q b * (g.map q).coeff n = 0
    simpa only [coeff_C_mul, coeff_zero] using congrArg (fun p => p.coeff n) hgm
  have hag : C a ∣ g := (C_dvd_iff_dvd_coeff a g).mpr fun n => by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [coeff_map, coeff_zero] using congrArg (fun p => p.coeff n) hgq
  obtain ⟨g', rfl⟩ := hag
  refine ⟨g', ?_⟩
  ext n
  apply ha
  change a * p.coeff n = a * (pairPolynomial a b * g').coeff n
  have h : C a * p = C a * (pairPolynomial a b * g') := by
    simpa only [mul_assoc, mul_left_comm] using hg
  simpa only [coeff_C_mul] using congrArg (fun p => p.coeff n) h

/-- The first parameter remains a nonzerodivisor in the actual polynomial quotient.
The second regularity assumption is on the original quotient by the first parameter. -/
theorem pairQuotient_smulRegular
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b) :
    IsSMulRegular (pairQuotient a b) a := by
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro x hx
  induction x using AdjoinRoot.induction_on with
  | ih p =>
    apply AdjoinRoot.mk_eq_zero.mpr
    apply pairPolynomial_dvd_of_C_mul_dvd a b ha hb p
    apply AdjoinRoot.mk_eq_zero.mp
    rw [map_mul, AdjoinRoot.mk_C]
    simpa only [Algebra.smul_def, AdjoinRoot.algebraMap_eq] using hx

private def pairLocalizationLift :
    Localization.Away a →ₐ[A]
      Localization.Away (algebraMap A (pairQuotient a b) a) :=
  IsLocalization.Away.liftAlgHom a
    (f := Algebra.ofId A (Localization.Away (algebraMap A (pairQuotient a b) a))) (by
      change IsUnit (algebraMap A (Localization.Away (algebraMap A (pairQuotient a b) a)) a)
      rw [IsScalarTower.algebraMap_apply A (pairQuotient a b)]
      exact IsLocalization.Away.algebraMap_isUnit
        (S := Localization.Away (algebraMap A (pairQuotient a b) a))
        (algebraMap A (pairQuotient a b) a))

private theorem pairLocalizationLift_comp :
    (pairLocalizationLift a b).comp (pairToLocalization a b) =
      IsScalarTower.toAlgHom A (pairQuotient a b)
        (Localization.Away (algebraMap A (pairQuotient a b) a)) := by
  let Q := pairQuotient a b
  let L := Localization.Away (algebraMap A Q a)
  apply AdjoinRoot.algHom_ext
  apply (IsLocalization.Away.algebraMap_isUnit (S := L) (algebraMap A Q a)).mul_left_injective
  change pairLocalizationLift a b (pairToLocalization a b (pairCoordinate a b)) *
      algebraMap Q L (algebraMap A Q a) =
    algebraMap Q L (pairCoordinate a b) * algebraMap Q L (algebraMap A Q a)
  rw [pairToLocalization_coordinate, ← IsScalarTower.algebraMap_apply A Q L]
  have hf := congrArg (pairLocalizationLift a b) (fraction_mul_self a b)
  simp only [map_mul, AlgHom.commutes] at hf
  rw [hf]
  rw [IsScalarTower.algebraMap_apply A Q L a, ← map_mul, mul_comm,
    pairCoordinate_relation, ← IsScalarTower.algebraMap_apply A Q L b]

/-- The canonical evaluation into the localization is injective for the original regular pair. -/
theorem pairToLocalization_injective
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b) :
    Function.Injective (pairToLocalization a b) := by
  let Q := pairQuotient a b
  let L := Localization.Away (algebraMap A Q a)
  have hleft : IsLeftRegular (algebraMap A Q a) := by
    intro x y h
    apply pairQuotient_smulRegular a b ha hb
    simpa only [Algebra.smul_def] using h
  have hregular : IsRegular (algebraMap A Q a) :=
    ⟨hleft, hleft.right_of_commute (fun _ => mul_comm _ _)⟩
  have hinj : Function.Injective (algebraMap Q L) :=
    IsLocalization.injectiveₛ (S := L) (M := Submonoid.powers (algebraMap A Q a))
      (by rintro _ ⟨n, rfl⟩; exact hregular.pow n)
  intro x y hxy
  apply hinj
  have hx := congrArg (fun f : Q →ₐ[A] L => f x) (pairLocalizationLift_comp a b)
  have hy := congrArg (fun f : Q →ₐ[A] L => f y) (pairLocalizationLift_comp a b)
  change pairLocalizationLift a b (pairToLocalization a b x) = algebraMap Q L x at hx
  change pairLocalizationLift a b (pairToLocalization a b y) = algebraMap Q L y at hy
  rw [← hx, ← hy]
  exact congrArg (pairLocalizationLift a b) hxy

/-- The image is the actual subalgebra generated by all fractions of the original ideal. -/
theorem pairToLocalization_range :
    (pairToLocalization a b).range = saturatedChart A (Ideal.span {a, b}) a := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using AdjoinRoot.induction_on with
    | ih p =>
      have hcoord : fraction a b ∈ saturatedChart A (Ideal.span {a, b}) a :=
        fraction_mem _ _ _ (Ideal.subset_span (by simp))
      change (pairToLocalization a b) (AdjoinRoot.mk (pairPolynomial a b) p) ∈ _
      rw [pairToLocalization, AdjoinRoot.liftAlgHom_mk]
      induction p using Polynomial.induction_on' with
      | add p q hp hq => simpa using (saturatedChart A (Ideal.span {a, b}) a).add_mem hp hq
      | monomial n r =>
        simpa using (saturatedChart A (Ideal.span {a, b}) a).mul_mem
          ((saturatedChart A (Ideal.span {a, b}) a).algebraMap_mem r)
          ((saturatedChart A (Ideal.span {a, b}) a).pow_mem hcoord n)
  · apply saturatedChart_le
    · intro r
      exact (pairToLocalization a b).range.algebraMap_mem r
    · intro r hr
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with h | h
      · subst r
        rw [fraction_self]
        exact (pairToLocalization a b).range.one_mem
      · subst r
        exact ⟨pairCoordinate a b, pairToLocalization_coordinate a b⟩

/-- The quotient and saturated chart are canonically isomorphic as algebras over the original
base. Injectivity, and hence removal of possible denominator torsion, is proved above. -/
def pairChartEquiv
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b) :
    pairQuotient a b ≃ₐ[A] saturatedChart A (Ideal.span {a, b}) a :=
  (AlgEquiv.ofInjective (pairToLocalization a b) (pairToLocalization_injective a b ha hb)).trans
    (Subalgebra.equivOfEq _ _ (pairToLocalization_range a b))

@[simp]
theorem pairChartEquiv_coe
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (x : pairQuotient a b) :
    (pairChartEquiv a b ha hb x : Localization.Away a) = pairToLocalization a b x := rfl

/-- The coordinate is sent to the original ratio `b/a`. -/
theorem pairChartEquiv_coordinate
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b) :
    (pairChartEquiv a b ha hb (pairCoordinate a b) : Localization.Away a) = fraction a b :=
  pairToLocalization_coordinate a b

/-- The forward comparison preserves the original scalar map. -/
theorem pairChartEquiv_base
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b) (r : A) :
    pairChartEquiv a b ha hb (algebraMap A (pairQuotient a b) r) =
      algebraMap A (saturatedChart A (Ideal.span {a, b}) a) r :=
  (pairChartEquiv a b ha hb).commutes r

end Localization.Away

namespace Localization.Away

open Polynomial
variable {A : Type u} [CommRing A] (a b : A)

/-- The literal residue fibre of the polynomial quotient over the two-generated ideal. -/
abbrev pairFibre := pairQuotient a b ⧸
  (Ideal.span {a, b}).map (AdjoinRoot.of (pairPolynomial a b))

/-- The original defining polynomial vanishes after reducing its two coefficients. -/
theorem pairReduction_relation :
    (pairPolynomial a b).eval₂ (Algebra.ofId A (A ⧸ Ideal.span {a, b})[X]).toRingHom X = 0 := by
  have ha : algebraMap A (A ⧸ Ideal.span {a, b}) a = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hb : algebraMap A (A ⧸ Ideal.span {a, b}) b = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  change (C a * X - C b).eval₂ (algebraMap A (A ⧸ Ideal.span {a, b})[X]) X = 0
  simp only [eval₂_sub, eval₂_mul, eval₂_C, eval₂_X]
  rw [IsScalarTower.algebraMap_apply A (A ⧸ Ideal.span {a, b}) _ a,
    IsScalarTower.algebraMap_apply A (A ⧸ Ideal.span {a, b}) _ b,
    ha, hb, map_zero, zero_mul, sub_self]

/-- Reduction of the original polynomial equation, with its coordinate sent to `X`. -/
def pairReduction :
    pairQuotient a b →ₐ[A] (A ⧸ Ideal.span {a, b})[X] :=
  AdjoinRoot.liftAlgHom (pairPolynomial a b)
    (Algebra.ofId A (A ⧸ Ideal.span {a, b})[X]) X (pairReduction_relation a b)

/-- The coefficient-ideal image is killed by the actual polynomial reduction. -/
theorem pairReduction_kills (x : pairQuotient a b)
    (hx : x ∈ (Ideal.span {a, b}).map (algebraMap A (pairQuotient a b))) :
    pairReduction a b x = 0 := by
  have h : (Ideal.span {a, b}).map (algebraMap A (pairQuotient a b)) ≤
      RingHom.ker (pairReduction a b).toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change pairReduction a b (algebraMap A (pairQuotient a b) r) = 0
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A (A ⧸ Ideal.span {a, b})]
    change algebraMap (A ⧸ Ideal.span {a, b}) (A ⧸ Ideal.span {a, b})[X]
      (Ideal.Quotient.mk (Ideal.span {a, b}) r) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]
  exact h hx

/-- The canonical residue map keeps the polynomial coordinate. -/
def pairFibreToPolynomial : pairFibre a b →ₐ[A] (A ⧸ Ideal.span {a, b})[X] :=
  Ideal.Quotient.liftₐ _ (pairReduction a b) (pairReduction_kills a b)

/-- The quotient lift keeps the original polynomial coordinate. -/
@[simp]
theorem pairFibreToPolynomial_coordinate :
    pairFibreToPolynomial a b (Ideal.Quotient.mk _ (pairCoordinate a b)) = X := by
  have h := congrArg
    (fun f : pairQuotient a b →ₐ[A] (A ⧸ Ideal.span {a, b})[X] => f (pairCoordinate a b))
    (Ideal.Quotient.liftₐ_comp
      ((Ideal.span {a, b}).map (algebraMap A (pairQuotient a b)))
      (pairReduction a b) (pairReduction_kills a b))
  change pairFibreToPolynomial a b (Ideal.Quotient.mk _ (pairCoordinate a b)) =
    pairReduction a b (pairCoordinate a b) at h
  exact h.trans (AdjoinRoot.liftAlgHom_root (pairPolynomial a b)
    (Algebra.ofId A (A ⧸ Ideal.span {a, b})[X]) X (pairReduction_relation a b))

/-- The original quotient coefficients act on the actual fibre quotient. -/
def pairFibreCoefficient : (A ⧸ Ideal.span {a, b}) →ₐ[A] pairFibre a b :=
  Ideal.Quotient.liftₐ _ (Algebra.ofId A (pairFibre a b)) (by
    intro r hr
    change Ideal.Quotient.mk _ (algebraMap A (pairQuotient a b) r) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr))

/-- The polynomial variable is sent back to the original quotient coordinate. -/
def pairFibreFromPolynomial : (A ⧸ Ideal.span {a, b})[X] →ₐ[A] pairFibre a b :=
  Polynomial.eval₂AlgHom (pairFibreCoefficient a b)
    (Ideal.Quotient.mk _ (pairCoordinate a b)) (fun _ => mul_comm _ _)

/-- The inverse polynomial map also keeps the original coordinate. -/
@[simp]
theorem pairFibreFromPolynomial_X : pairFibreFromPolynomial a b X =
    Ideal.Quotient.mk _ (pairCoordinate a b) := by
  change (X : (A ⧸ Ideal.span {a, b})[X]).eval₂ (pairFibreCoefficient a b).toRingHom
    (Ideal.Quotient.mk _ (pairCoordinate a b)) = _
  exact Polynomial.eval₂_X _ _

/-- The two actual fibre maps compose to the original polynomial identity. -/
theorem pairFibreToPolynomial_comp :
    (pairFibreToPolynomial a b).comp (pairFibreFromPolynomial a b) =
      AlgHom.id A (A ⧸ Ideal.span {a, b})[X] := by
  apply AlgHom.coe_ringHom_injective
  apply Polynomial.ringHom_ext
  · intro r
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    simp [pairFibreFromPolynomial, pairFibreCoefficient, pairFibreToPolynomial,
      pairReduction, Polynomial.eval₂AlgHom]
  · change pairFibreToPolynomial a b (pairFibreFromPolynomial a b X) = X
    rw [pairFibreFromPolynomial_X, pairFibreToPolynomial_coordinate]

/-- The reverse composite fixes the actual fibre quotient. -/
theorem pairFibreFromPolynomial_comp :
    (pairFibreFromPolynomial a b).comp (pairFibreToPolynomial a b) =
      AlgHom.id A (pairFibre a b) := by
  apply Ideal.Quotient.algHom_ext A
  apply AdjoinRoot.algHom_ext
  simp [pairFibreFromPolynomial, pairFibreToPolynomial, pairReduction,
    pairCoordinate, Polynomial.eval₂AlgHom]

/-- Reduction by the original two-generated ideal leaves the original polynomial variable free. -/
def pairFibreEquiv : pairFibre a b ≃ₐ[A] (A ⧸ Ideal.span {a, b})[X] :=
  AlgEquiv.ofAlgHom (pairFibreToPolynomial a b) (pairFibreFromPolynomial a b)
    (pairFibreToPolynomial_comp a b) (pairFibreFromPolynomial_comp a b)

@[simp]
theorem pairFibreEquiv_coordinate :
    pairFibreEquiv a b (Ideal.Quotient.mk _ (pairCoordinate a b)) = X := by
  exact pairFibreToPolynomial_coordinate a b

/-- The chart equivalence carries the image of the original coefficient ideal to the same image. -/
theorem pairChartEquiv_mapIdeal
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b) :
    (Ideal.span {a, b}).map (algebraMap A (saturatedChart A (Ideal.span {a, b}) a)) =
      ((Ideal.span {a, b}).map (algebraMap A (pairQuotient a b))).map
        (pairChartEquiv a b ha hb).toRingHom := by
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro r
  exact ((pairChartEquiv a b ha hb).commutes r).symm

/-- The actual residue fibre ring of the saturated chart is a polynomial ring over the
original coefficient quotient, through the proved chart injection. -/
def pairChartFibreEquiv
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b) :
    (saturatedChart A (Ideal.span {a, b}) a ⧸
      (Ideal.span {a, b}).map (algebraMap A (saturatedChart A (Ideal.span {a, b}) a))) ≃ₐ[A]
        (A ⧸ Ideal.span {a, b})[X] :=
  (Ideal.quotientEquivAlg _ _ (pairChartEquiv a b ha hb)
    (pairChartEquiv_mapIdeal a b ha hb)).symm.trans (pairFibreEquiv a b)

end Localization.Away

namespace Localization.Away

variable {A : Type u} [CommRing A] (a b : A)

/-- Cancelling a regular first parameter also proves its regularity modulo the second. -/
theorem regularPair_swap_quotient
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b) :
    IsSMulRegular (A ⧸ Ideal.span {b}) a := by
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem (Ideal.span {b}) a).mpr
  intro x hx
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
  have hay : y ∈ Ideal.span {a} := by
    apply (isSMulRegular_quotient_iff_mem_of_smul_mem (Ideal.span {a}) b).mp hb y
    change b * y ∈ Ideal.span {a}
    rw [← hy]
    exact Ideal.mem_span_singleton.mpr ⟨x, rfl⟩
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.mp hay
  apply Ideal.mem_span_singleton.mpr
  refine ⟨z, ?_⟩
  apply ha
  change a * x = a * (b * z)
  simpa only [smul_eq_mul, mul_assoc, mul_left_comm] using hy

end Localization.Away

namespace IsRegularLocalRing

open IsLocalRing
variable (A : Type u) [CommRing A] [IsRegularLocalRing A]

/-- Every two-dimensional regular local ring has actual generators of its maximal ideal
which are regular in both chart orientations. -/
theorem exists_regularPair (hd : ringKrullDim A = 2) :
    ∃ a b : A, a ∈ maximalIdeal A ∧ b ∈ maximalIdeal A ∧
      Ideal.span {a, b} = maximalIdeal A ∧
      IsSMulRegular A a ∧ IsSMulRegular (A ⧸ Ideal.span {a}) b ∧
      IsSMulRegular A b ∧ IsSMulRegular (A ⧸ Ideal.span {b}) a := by
  obtain ⟨a, ha, hareg, hQ, hdQ⟩ := exists_regular_parameter A 1 (by simpa using hd)
  let Q := A ⧸ Ideal.span {a}
  let : IsRegularLocalRing Q := hQ
  let : IsDomain Q := isDomain_of_regularLocal Q
  let q : A →+* Q := Ideal.Quotient.mk (Ideal.span {a})
  let : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  have hspan : (maximalIdeal Q).spanFinrank = 1 := by
    have hh := (IsRegularLocalRing.spanFinrank_maximalIdeal (R := Q)).trans hdQ
    exact_mod_cast hh
  have hprincipal := (Submodule.spanFinrank_eq_one_iff (maximalIdeal Q)).mp hspan
  obtain ⟨c, hc⟩ := hprincipal.1
  have hc0 : c ≠ 0 := by
    intro h
    apply hprincipal.2
    simpa only [h, Submodule.span_zero_singleton] using hc
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective c
  have hbmem : b ∈ maximalIdeal A := by
    rw [← maximalIdeal_comap q]
    change q b ∈ maximalIdeal Q
    rw [hb, hc]
    exact Ideal.subset_span (by simp)
  have hgen : Ideal.span {a, b} = maximalIdeal A := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      intro r hr
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl
      · exact ha
      · exact hbmem
    · intro r hr
      have hrQ : q r ∈ maximalIdeal Q := map_nonunit q r hr
      rw [hc] at hrQ
      obtain ⟨sQ, hsQ⟩ := Ideal.mem_span_singleton.mp hrQ
      obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective sQ
      have hz : q (r - b * s) = 0 := by
        rw [map_sub, map_mul, hb, hs, hsQ, sub_self]
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
      apply Ideal.mem_span_pair.mpr
      refine ⟨t, s, ?_⟩
      calc
        t * a + s * b = a * t + b * s := by ring
        _ = r := by rw [← ht, sub_add_cancel]
  have hbreg : IsSMulRegular Q b := by
    apply IsSMulRegular.of_right_eq_zero_of_smul
    intro z hz
    change q b * z = 0 at hz
    rw [hb] at hz
    exact (mul_eq_zero.mp hz).resolve_left hc0
  have hb0 : b ≠ 0 := by
    intro h
    apply hc0
    simpa only [h, map_zero] using hb.symm
  exact ⟨a, b, ha, hbmem, hgen, hareg, hbreg,
    isSMulRegular_of_regularLocal_ne_zero A b hb0,
    Localization.Away.regularPair_swap_quotient a b hareg hbreg⟩

end IsRegularLocalRing
