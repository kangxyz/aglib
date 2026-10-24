/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPolynomial.QuadraticClosedPoint
public import Aglib.RingTheory.Blowup.MarkedChart
public import Aglib.RingTheory.Blowup.RegularPair
public import Aglib.RingTheory.RegularLocalRing.ParameterQuotient
public import Aglib.RingTheory.RegularLocalRing.QuotientLift
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.Localization.Ideal

/-!
# The conditional local chart core for Case I

The input is the actual saturated chart's exceptional quotient, including its
original coefficient and fraction equations. Its production from the full
canonical quadratic tangent kernel remains with the cone/exceptional-chart
assembly. The local argument derives square membership of the original plane
equation from singularity, then proves bijectivity of the original residue map.
No ambient hypersurface presentation of the chart or rational-point premise is
used. The original exceptional element remains explicit throughout.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped nonZeroDivisors Polynomial

namespace Localization.Away.CaseOne

universe u

section LocalizedQuotients

variable {C P : Type u} [CommRing C] [CommRing P]

/-- Quotienting retains the original prime containing the defining ideal. -/
theorem quotient_prime_comap (J : Ideal P) (M : Ideal P)
    (hJM : J ≤ M) : (M.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = M := by
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
  have hker : (⊥ : Ideal (P ⧸ J)).comap (Ideal.Quotient.mk J) = J := Ideal.mk_ker
  rw [hker, sup_eq_left.mpr hJM]

/-- The actual quotient equivalence identifies the images of the two original
prime-complement submonoids. -/
theorem localizedQuotient_submonoid
    (I : Ideal C) (J : Ideal P) (E : C ⧸ I ≃+* P ⧸ J)
    (M : Ideal P) [M.IsPrime] (hJM : J ≤ M)
    (n : Ideal C) [n.IsPrime]
    (hn : n = (M.map (Ideal.Quotient.mk J)).comap
      (E.toRingHom.comp (Ideal.Quotient.mk I))) :
    (Algebra.algebraMapSubmonoid (C ⧸ I) n.primeCompl).map E.toMonoidHom =
      Algebra.algebraMapSubmonoid (P ⧸ J) M.primeCompl := by
  let p := M.map (Ideal.Quotient.mk J)
  let : p.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hJM
  let red := E.toRingHom.comp (Ideal.Quotient.mk I)
  have hred : Function.Surjective red := E.surjective.comp Ideal.Quotient.mk_surjective
  have hnCompl : n.primeCompl = (p.comap red).primeCompl := by
    ext x
    change x ∉ n ↔ x ∉ p.comap red
    rw [hn]
  have hM : p.comap (Ideal.Quotient.mk J) = M := quotient_prime_comap J M hJM
  have hMCompl : M.primeCompl = (p.comap (Ideal.Quotient.mk J)).primeCompl := by
    ext x
    change x ∉ M ↔ x ∉ p.comap (Ideal.Quotient.mk J)
    rw [hM]
  have hl : n.primeCompl.map red.toMonoidHom = p.primeCompl := by
    rw [hnCompl]
    exact Ideal.map_primeCompl_comap_of_surjective red hred p
  have hr : M.primeCompl.map (Ideal.Quotient.mk J).toMonoidHom = p.primeCompl := by
    rw [hMCompl]
    exact Ideal.map_primeCompl_comap_of_surjective
      (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective p
  change (n.primeCompl.map (Ideal.Quotient.mk I).toMonoidHom).map E.toMonoidHom =
    M.primeCompl.map (Ideal.Quotient.mk J).toMonoidHom
  rw [Submonoid.map_map]
  exact hl.trans hr.symm

/-- Localize an actual quotient comparison at its actual corresponding primes.
Both quotient rings retain their original localization and coefficient maps. -/
def localizedQuotientEquiv
    (I : Ideal C) (J : Ideal P) (E : C ⧸ I ≃+* P ⧸ J)
    (M : Ideal P) [M.IsPrime] (hJM : J ≤ M)
    (n : Ideal C) [n.IsPrime]
    (hn : n = (M.map (Ideal.Quotient.mk J)).comap
      (E.toRingHom.comp (Ideal.Quotient.mk I)))
    (S : Type u) [CommRing S] [Algebra C S] [IsLocalization n.primeCompl S]
    (T : Type u) [CommRing T] [Algebra P T] [IsLocalization M.primeCompl T] :
    (S ⧸ I.map (algebraMap C S)) ≃+*
      (T ⧸ J.map (algebraMap P T)) :=
  IsLocalization.ringEquivOfRingEquiv
    (S ⧸ I.map (algebraMap C S))
    (T ⧸ J.map (algebraMap P T)) E
      (localizedQuotient_submonoid I J E M hJM n hn)

/-- The localized quotient equivalence retains every original quotient scalar. -/
theorem localizedQuotientEquiv_base
    (I : Ideal C) (J : Ideal P) (E : C ⧸ I ≃+* P ⧸ J)
    (M : Ideal P) [M.IsPrime] (hJM : J ≤ M)
    (n : Ideal C) [n.IsPrime]
    (hn : n = (M.map (Ideal.Quotient.mk J)).comap
      (E.toRingHom.comp (Ideal.Quotient.mk I)))
    (S : Type u) [CommRing S] [Algebra C S] [IsLocalization n.primeCompl S]
    (T : Type u) [CommRing T] [Algebra P T] [IsLocalization M.primeCompl T]
    (x : C ⧸ I) :
    localizedQuotientEquiv I J E M hJM n hn S T
      (algebraMap (C ⧸ I)
        (S ⧸ I.map (algebraMap C S)) x) =
      algebraMap (P ⧸ J)
        (T ⧸ J.map (algebraMap P T)) (E x) := by
  exact IsLocalization.ringEquivOfRingEquiv_eq
    (localizedQuotient_submonoid I J E M hJM n hn) x

end LocalizedQuotients

section Plane

variable {k : Type u} [Field k]

private def planeRegroup : MvPolynomial (Fin 2) k ≃ₐ[k] k[X][X] :=
  (MvPolynomial.finSuccEquiv k 1).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv k (Fin 1)))

/-- Every actual closed point of the affine plane has a two-dimensional local ring,
including closed points with inseparable residue fields. -/
theorem plane_local_dimension (M : Ideal (MvPolynomial (Fin 2) k)) [M.IsMaximal] :
    ringKrullDim (Localization.AtPrime M) = 2 := by
  let e := planeRegroup (k := k)
  let P := M.map e.toRingHom
  let : P.IsMaximal := (Ideal.isMaximal_map_iff_of_bijective e.toRingHom e.bijective).mpr
    inferInstance
  let N : Ideal k[X] := P.comap Polynomial.C
  let : N.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P
  let : P.LiesOver N := ⟨rfl⟩
  have hN : N.height = 1 :=
    IsPrincipalIdealRing.height_eq_one_of_isMaximal N (Polynomial.not_isField k)
  have hP : P.height = 2 := by
    rw [Polynomial.height_eq_height_add_one N P, hN]
    norm_num
  have hM : M.height = 2 := by
    rw [← e.toRingEquiv.height_map M]
    exact hP
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height M (Localization.AtPrime M)]
  rw [hM]
  exact ENat.WithBot.coe_eq_natCast 2

/-- The actual localization of the plane is regular, without a residue-field
separability hypothesis. -/
theorem plane_local_regular (M : Ideal (MvPolynomial (Fin 2) k)) [M.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime M) := inferInstance

private theorem principal_quotient_dimension
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
    (x : R) (hx : x ∈ maximalIdeal R) (hx0 : x ≠ 0) (hd : ringKrullDim R = 2) :
    ringKrullDim (R ⧸ Ideal.span {x}) = 1 := by
  have hupper := ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (mem_nonZeroDivisors_iff_ne_zero.mpr hx0)
  have hlower := Ideal.height_le_ringKrullDim_quotient_add_one hx
  rw [hd] at hupper
  rw [maximalIdeal_height_eq_ringKrullDim, hd] at hlower
  have hupper' : ringKrullDim (R ⧸ Ideal.span {x}) + 1 ≤
      ((1 + 1 : ℕ) : WithBot ℕ∞) := hupper
  have hlower' : ((1 + 1 : ℕ) : WithBot ℕ∞) ≤
      ringKrullDim (R ⧸ Ideal.span {x}) + 1 := hlower
  apply le_antisymm
  · apply (ENat.WithBot.add_le_add_natCast_right_iff (c := 1)).mp
    simpa only [Nat.cast_add, Nat.cast_one] using hupper'
  · apply (ENat.WithBot.add_le_add_natCast_right_iff (c := 1)).mp
    simpa only [Nat.cast_add, Nat.cast_one] using hlower'

/-- The local plane curve has dimension one for its original nonzero equation. -/
theorem plane_quotient_dimension (M : Ideal (MvPolynomial (Fin 2) k)) [M.IsMaximal]
    (Q : MvPolynomial (Fin 2) k) (hQ : Q ∈ M) (hQ0 : Q ≠ 0) :
    ringKrullDim (Localization.AtPrime M ⧸
      Ideal.span {algebraMap _ (Localization.AtPrime M) Q}) = 1 := by
  let P := MvPolynomial (Fin 2) k
  let S := Localization.AtPrime M
  have hinj : Function.Injective (algebraMap P S) :=
    IsLocalization.injective S M.primeCompl_le_nonZeroDivisors
  have hq : algebraMap P S Q ∈ maximalIdeal S := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal M S]
    exact Ideal.mem_map_of_mem _ hQ
  exact principal_quotient_dimension S _ hq (map_ne_zero_iff _ hinj |>.mpr hQ0)
    (plane_local_dimension M)

/-- The passed quadratic result forces surjectivity of the ORIGINAL constant
map to the actual closed-point quotient in Case I. -/
theorem plane_residue_bijective
    (M : Ideal (MvPolynomial (Fin 2) k)) [M.IsMaximal]
    (Q : MvPolynomial (Fin 2) k) (hQ0 : Q ≠ 0) (hdeg : Q.totalDegree ≤ 2)
    (hQsq : Q ∈ M ^ 2)
    (hcase : ¬ ∃ c : k, c ≠ 0 ∧ ∃ l : MvPolynomial (Fin 2) k,
      l.totalDegree ≤ 1 ∧ Q = MvPolynomial.C c * l ^ 2) :
    Function.Bijective (algebraMap k (MvPolynomial (Fin 2) k ⧸ M)) := by
  let : Field (MvPolynomial (Fin 2) k ⧸ M) := Ideal.Quotient.field M
  let : Module.Finite k (MvPolynomial (Fin 2) k ⧸ M) :=
    finite_of_finite_type_of_isJacobsonRing k (MvPolynomial (Fin 2) k ⧸ M)
  have hle : Module.finrank k (MvPolynomial (Fin 2) k ⧸ M) ≤ 1 := by
    by_contra h
    obtain ⟨c, hc, l, _, hl, he⟩ :=
      MvPolynomial.exists_scalar_linear_sq_of_mem_maximal_sq M Q hQ0 hdeg hQsq (by omega)
    exact hcase ⟨c, hc, l, hl, he⟩
  have hdim : Module.finrank k (MvPolynomial (Fin 2) k ⧸ M) = 1 := by
    have hpos : 0 < Module.finrank k (MvPolynomial (Fin 2) k ⧸ M) := Module.finrank_pos
    omega
  refine ⟨(algebraMap k (MvPolynomial (Fin 2) k ⧸ M)).injective, ?_⟩
  intro z
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero'
    (1 : MvPolynomial (Fin 2) k ⧸ M) one_ne_zero).mp hdim z
  exact ⟨a, by simpa only [Algebra.smul_def, mul_one] using ha⟩

end Plane

section Presentation

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- The polynomial plane over the original local ring's residue field. -/
abbrev Plane := MvPolynomial (Fin 2) (ResidueField A)

/-- The literal saturated maximal-ideal blowup chart with denominator `t`. -/
abbrev Chart (t : maximalIdeal A) := saturatedChart A (maximalIdeal A) (t : A)

/-- The original exceptional ideal on the literal saturated chart. -/
def exceptionalIdeal (t : maximalIdeal A) : Ideal (Chart A t) :=
  Ideal.span {algebraMap A (Chart A t) (t : A)}

/-- The exact exceptional quotient and its original scalar and fraction laws.
This is upstream presentation data, not an ambient presentation of the chart,
and contains no singularity, square-membership or residue-rationality result. -/
structure Presentation (t : maximalIdeal A) (g : Fin 2 → maximalIdeal A) (Q : Plane A) where
  /-- The exceptional quotient identified with the original plane equation quotient. -/
  equiv : (Chart A t ⧸ exceptionalIdeal A t) ≃+* (Plane A ⧸ Ideal.span {Q})
  coefficient (a : A) :
    equiv (Ideal.Quotient.mk (exceptionalIdeal A t) (algebraMap A (Chart A t) a)) =
      Ideal.Quotient.mk (Ideal.span {Q}) (MvPolynomial.C (residue A a))
  coordinate (i : Fin 2) :
    equiv (Ideal.Quotient.mk (exceptionalIdeal A t)
      (SaturatedChart.fractionElement (maximalIdeal A) t (g i))) =
        Ideal.Quotient.mk (Ideal.span {Q}) (MvPolynomial.X i)

variable {A}

namespace Presentation

variable {t : maximalIdeal A} {g : Fin 2 → maximalIdeal A} {Q : Plane A}
  (D : Presentation A t g Q) (M : Ideal (Plane A)) [M.IsMaximal] (hQM : Q ∈ M)

/-- The original exceptional quotient map. -/
def reduction : Chart A t →+* Plane A ⧸ Ideal.span {Q} :=
  D.equiv.toRingHom.comp (Ideal.Quotient.mk (exceptionalIdeal A t))

theorem reduction_surjective : Function.Surjective D.reduction :=
  D.equiv.surjective.comp Ideal.Quotient.mk_surjective

/-- The original chart point valued in the actual plane residue quotient. -/
def point (hQM : Q ∈ M) : Chart A t →+* Plane A ⧸ M :=
  (Ideal.Quotient.factor ((Ideal.span_singleton_le_iff_mem M).mpr hQM)).comp D.reduction

omit [M.IsMaximal] in
theorem point_surjective : Function.Surjective (D.point M hQM) :=
  (Ideal.Quotient.factor_surjective ((Ideal.span_singleton_le_iff_mem M).mpr hQM)).comp
    D.reduction_surjective

omit [M.IsMaximal] in
@[simp] theorem point_base (a : A) :
    D.point M hQM (algebraMap A (Chart A t) a) =
      algebraMap (ResidueField A) (Plane A ⧸ M) (residue A a) := by
  change Ideal.Quotient.factor ((Ideal.span_singleton_le_iff_mem M).mpr hQM) (D.equiv
    (Ideal.Quotient.mk (exceptionalIdeal A t) (algebraMap A (Chart A t) a))) = _
  rw [D.coefficient, Ideal.Quotient.factor_mk]
  rfl

omit [M.IsMaximal] in
@[simp] theorem point_fraction (i : Fin 2) :
    D.point M hQM (SaturatedChart.fractionElement (maximalIdeal A) t (g i)) =
      Ideal.Quotient.mk M (MvPolynomial.X i) := by
  change Ideal.Quotient.factor ((Ideal.span_singleton_le_iff_mem M).mpr hQM) (D.equiv
    (Ideal.Quotient.mk (exceptionalIdeal A t)
      (SaturatedChart.fractionElement (maximalIdeal A) t (g i)))) = _
  rw [D.coordinate, Ideal.Quotient.factor_mk]

/-- The actual prime selected by the displayed plane point. -/
def prime : Ideal (Chart A t) := RingHom.ker (D.point M hQM)

instance prime_isMaximal : (D.prime M hQM).IsMaximal := by
  let : Field (Plane A ⧸ M) := Ideal.Quotient.field M
  exact RingHom.ker_isMaximal_of_surjective _ (D.point_surjective M hQM)

instance prime_isPrime : (D.prime M hQM).IsPrime := inferInstance

omit [M.IsMaximal] in
/-- The chart prime is the actual pullback of the original plane-quotient prime. -/
theorem prime_eq_comap : D.prime M hQM =
    (M.map (Ideal.Quotient.mk (Ideal.span {Q}))).comap D.reduction := by
  ext x
  change Ideal.Quotient.factor ((Ideal.span_singleton_le_iff_mem M).mpr hQM)
    (D.reduction x) = 0 ↔ D.reduction x ∈ M.map (Ideal.Quotient.mk (Ideal.span {Q}))
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (D.reduction x)
  rw [← hp, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
  change p ∈ M ↔ p ∈
    (M.map (Ideal.Quotient.mk (Ideal.span {Q}))).comap (Ideal.Quotient.mk (Ideal.span {Q}))
  rw [quotient_prime_comap (Ideal.span {Q}) M
    ((Ideal.span_singleton_le_iff_mem M).mpr hQM)]

/-- The actual chart prime lies over the original closed point, before any
residue-rationality conclusion. -/
theorem prime_comap_base :
    (D.prime M hQM).comap (algebraMap A (Chart A t)) = maximalIdeal A := by
  let : Field (Plane A ⧸ M) := Ideal.Quotient.field M
  ext a
  change D.point M hQM (algebraMap A (Chart A t) a) = 0 ↔ a ∈ maximalIdeal A
  rw [D.point_base]
  constructor
  · intro h
    apply (residue_eq_zero_iff a).mp
    apply (algebraMap (ResidueField A) (Plane A ⧸ M)).injective
    exact h.trans (map_zero _).symm
  · intro h
    rw [(residue_eq_zero_iff a).mpr h, map_zero]

/-- The literal prime localization of the original saturated chart. The named
instances below retain this type while fixing one coherent ring structure. -/
def LocalRing : Type u := Localization.AtPrime (D.prime M hQM)

instance localRingCommRing : CommRing (D.LocalRing M hQM) :=
  inferInstanceAs (CommRing (Localization.AtPrime (D.prime M hQM)))

instance localRingAlgebra : Algebra (Chart A t) (D.LocalRing M hQM) :=
  inferInstanceAs (Algebra (Chart A t) (Localization.AtPrime (D.prime M hQM)))

instance localRing_isLocalization :
    IsLocalization (D.prime M hQM).primeCompl (D.LocalRing M hQM) :=
  inferInstanceAs (IsLocalization (D.prime M hQM).primeCompl
    (Localization.AtPrime (D.prime M hQM)))

instance localRing_isLocal : IsLocalRing (D.LocalRing M hQM) :=
  IsLocalization.AtPrime.isLocalRing (D.LocalRing M hQM) (D.prime M hQM)

/-- The original local coefficient map, through the original chart and its localization. -/
def localMap : A →+* D.LocalRing M hQM :=
  (algebraMap (Chart A t) (D.LocalRing M hQM)).comp (algebraMap A (Chart A t))

/-- The same original element, in the actual child local ring. -/
def parameter : D.LocalRing M hQM := D.localMap M hQM (t : A)

/-- Every element of the actual prime complement maps to a unit under the original point. -/
theorem point_isUnit_of_mem_primeCompl (c : (D.prime M hQM).primeCompl) :
    IsUnit (D.point M hQM c) := by
  let : Field (Plane A ⧸ M) := Ideal.Quotient.field M
  exact isUnit_iff_ne_zero.mpr c.property

/-- The original point extends through the actual prime localization. -/
def localPoint : D.LocalRing M hQM →+* Plane A ⧸ M := by
  let : Field (Plane A ⧸ M) := Ideal.Quotient.field M
  exact IsLocalization.lift (M := (D.prime M hQM).primeCompl)
    (g := D.point M hQM) (D.point_isUnit_of_mem_primeCompl M hQM)

@[simp] theorem localPoint_algebraMap (c : Chart A t) :
    D.localPoint M hQM (algebraMap (Chart A t) (D.LocalRing M hQM) c) =
      D.point M hQM c := by
  let : Field (Plane A ⧸ M) := Ideal.Quotient.field M
  exact IsLocalization.lift_eq (D.point_isUnit_of_mem_primeCompl M hQM) c

@[simp] theorem localPoint_base (a : A) :
    D.localPoint M hQM (D.localMap M hQM a) =
      algebraMap (ResidueField A) (Plane A ⧸ M) (residue A a) :=
  (D.localPoint_algebraMap M hQM (algebraMap A (Chart A t) a)).trans
    (D.point_base M hQM a)

instance localPoint_isLocal : IsLocalHom (D.localPoint M hQM) := by
  let : Field (Plane A ⧸ M) := Ideal.Quotient.field M
  have hker : maximalIdeal (D.LocalRing M hQM) ≤ RingHom.ker (D.localPoint M hQM) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal
      (D.prime M hQM) (D.LocalRing M hQM)]
    apply Ideal.map_le_iff_le_comap.mpr
    intro c hc
    change D.localPoint M hQM (algebraMap (Chart A t) (D.LocalRing M hQM) c) = 0
    rw [D.localPoint_algebraMap]
    exact hc
  refine ⟨fun x hx => ?_⟩
  by_contra hn
  exact (isUnit_iff_ne_zero.mp hx) (hker hn)

theorem localMap_isLocal : IsLocalHom (D.localMap M hQM) := by
  let : Field (Plane A ⧸ M) := Ideal.Quotient.field M
  have hc : (D.localPoint M hQM).comp (D.localMap M hQM) =
      (algebraMap (ResidueField A) (Plane A ⧸ M)).comp (residue A) := by
    ext a
    exact D.localPoint_base M hQM a
  let : IsLocalHom ((D.localPoint M hQM).comp (D.localMap M hQM)) :=
    hc.symm ▸ inferInstance
  exact isLocalHom_of_comp (D.localMap M hQM) (D.localPoint M hQM)

/-- The centre identity keeps the original maximal ideal and the original parameter. -/
theorem centre : (maximalIdeal A).map (D.localMap M hQM) =
    Ideal.span {D.parameter M hQM} := by
  rw [localMap, ← Ideal.map_map, map_center_eq_span (maximalIdeal A) (t : A) t.property,
    Ideal.map_span, Set.image_singleton]
  rfl

theorem parameter_mem_maximal : D.parameter M hQM ∈ maximalIdeal (D.LocalRing M hQM) := by
  let : IsLocalHom (D.localMap M hQM) := D.localMap_isLocal M hQM
  exact (map_maximalIdeal_le (D.localMap M hQM)) (Ideal.mem_map_of_mem _ t.property)

/-- The exceptional ideal becomes the principal ideal of the original parameter
under the original chart localization. -/
theorem exceptionalIdeal_map :
    (exceptionalIdeal A t).map (algebraMap (Chart A t) (D.LocalRing M hQM)) =
      Ideal.span {D.parameter M hQM} := by
  rw [exceptionalIdeal, Ideal.map_span, Set.image_singleton]
  rfl

/-- The actual localized exceptional quotient, with its original two local rings. -/
def localQuotientEquiv :
    (D.LocalRing M hQM ⧸ Ideal.span {D.parameter M hQM}) ≃+*
      (Localization.AtPrime M ⧸
        Ideal.span {algebraMap (Plane A) (Localization.AtPrime M) Q}) :=
  (Ideal.quotEquivOfEq (D.exceptionalIdeal_map M hQM).symm).trans
    ((localizedQuotientEquiv (exceptionalIdeal A t) (Ideal.span {Q}) D.equiv M
      ((Ideal.span_singleton_le_iff_mem M).mpr hQM) (D.prime M hQM)
      (D.prime_eq_comap M hQM) (D.LocalRing M hQM) (Localization.AtPrime M)).trans
        (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])))

/-- Every displayed global quotient identity is retained by the actual local
quotient comparison. -/
theorem localQuotientEquiv_mk (c : Chart A t) (p : Plane A)
    (hcp : D.equiv (Ideal.Quotient.mk (exceptionalIdeal A t) c) =
      Ideal.Quotient.mk (Ideal.span {Q}) p) :
    D.localQuotientEquiv M hQM
      (Ideal.Quotient.mk (Ideal.span {D.parameter M hQM})
        (algebraMap (Chart A t) (D.LocalRing M hQM) c)) =
      Ideal.Quotient.mk
        (Ideal.span {algebraMap (Plane A) (Localization.AtPrime M) Q})
        (algebraMap (Plane A) (Localization.AtPrime M) p) := by
  have h := localizedQuotientEquiv_base
    (exceptionalIdeal A t) (Ideal.span {Q}) D.equiv M
    ((Ideal.span_singleton_le_iff_mem M).mpr hQM) (D.prime M hQM)
    (D.prime_eq_comap M hQM) (D.LocalRing M hQM) (Localization.AtPrime M)
    (Ideal.Quotient.mk (exceptionalIdeal A t) c)
  rw [hcp] at h
  change localizedQuotientEquiv _ _ _ _ _ _ _ _ _
    (Ideal.Quotient.mk ((exceptionalIdeal A t).map
      (algebraMap (Chart A t) (D.LocalRing M hQM)))
        (algebraMap (Chart A t) (D.LocalRing M hQM) c)) =
    Ideal.Quotient.mk ((Ideal.span {Q}).map
      (algebraMap (Plane A) (Localization.AtPrime M)))
        (algebraMap (Plane A) (Localization.AtPrime M) p) at h
  simpa only [localQuotientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk] using
    congrArg (Ideal.quotEquivOfEq
      (show (Ideal.span {Q}).map (algebraMap (Plane A) (Localization.AtPrime M)) =
        Ideal.span {algebraMap (Plane A) (Localization.AtPrime M) Q} from by
          rw [Ideal.map_span, Set.image_singleton])) h

/-- The localized quotient comparison retains the original residue scalar. -/
theorem localQuotientEquiv_coefficient (a : A) :
    D.localQuotientEquiv M hQM
      (Ideal.Quotient.mk (Ideal.span {D.parameter M hQM}) (D.localMap M hQM a)) =
      Ideal.Quotient.mk
        (Ideal.span {algebraMap (Plane A) (Localization.AtPrime M) Q})
        (algebraMap (Plane A) (Localization.AtPrime M)
          (MvPolynomial.C (residue A a))) :=
  D.localQuotientEquiv_mk M hQM _ _ (D.coefficient a)

/-- The localized quotient comparison retains each original fraction coordinate. -/
theorem localQuotientEquiv_fraction (i : Fin 2) :
    D.localQuotientEquiv M hQM
      (Ideal.Quotient.mk (Ideal.span {D.parameter M hQM})
        (algebraMap (Chart A t) (D.LocalRing M hQM)
          (SaturatedChart.fractionElement (maximalIdeal A) t (g i)))) =
      Ideal.Quotient.mk
        (Ideal.span {algebraMap (Plane A) (Localization.AtPrime M) Q})
        (algebraMap (Plane A) (Localization.AtPrime M) (MvPolynomial.X i)) :=
  D.localQuotientEquiv_mk M hQM _ _ (D.coordinate i)

instance chart_isNoetherian [IsNoetherianRing A] : IsNoetherianRing (Chart A t) :=
  saturatedChart_isNoetherian (maximalIdeal A) (t : A)

instance localRing_isNoetherian [IsNoetherianRing A] :
    IsNoetherianRing (D.LocalRing M hQM) :=
  IsLocalization.isNoetherianRing (D.prime M hQM).primeCompl (D.LocalRing M hQM)
    (saturatedChart_isNoetherian (maximalIdeal A) (t : A))

/-- Nonzero original denominators make the actual saturated chart a domain. -/
theorem chart_isDomain [IsDomain A] (ht : (t : A) ≠ 0) : IsDomain (Chart A t) := by
  let : IsDomain (Localization.Away (t : A)) := Localization.Away.isDomain ht
  infer_instance

/-- The actual child localization is a domain, derived from the original domain. -/
theorem localRing_isDomain [IsDomain A] (ht : (t : A) ≠ 0) :
    IsDomain (D.LocalRing M hQM) := by
  let : IsDomain (Chart A t) := chart_isDomain ht
  exact IsLocalization.isDomain_of_le_nonZeroDivisors (D.LocalRing M hQM)
    (D.prime M hQM).primeCompl_le_nonZeroDivisors

/-- The original coefficient map into the actual child local ring is injective. -/
theorem localMap_injective [IsDomain A] (ht : (t : A) ≠ 0) :
    Function.Injective (D.localMap M hQM) := by
  let : IsDomain (Chart A t) := chart_isDomain ht
  have haway : Function.Injective (algebraMap A (Localization.Away (t : A))) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors ht)
  have hchart : Function.Injective (algebraMap A (Chart A t)) := by
    intro a b h
    apply haway
    exact congrArg (fun x : Chart A t => (x : Localization.Away (t : A))) h
  have hloc : Function.Injective (algebraMap (Chart A t) (D.LocalRing M hQM)) :=
    IsLocalization.injective (D.LocalRing M hQM)
      (D.prime M hQM).primeCompl_le_nonZeroDivisors
  exact hloc.comp hchart

/-- The original exceptional element remains a nonzerodivisor in the actual child. -/
theorem parameter_ne_zero [IsDomain A] (ht : (t : A) ≠ 0) :
    D.parameter M hQM ≠ 0 := by
  change D.localMap M hQM (t : A) ≠ 0
  exact (map_ne_zero_iff (D.localMap M hQM) (D.localMap_injective M hQM ht)).mpr ht

/-- Singularity forces square membership in the ORIGINAL plane-point ideal.
The proof uses the actual localized exceptional quotient and regularity lifting
through the original nonzero parameter. -/
theorem equation_mem_sq_of_not_regular [IsNoetherianRing A] [IsDomain A]
    (ht : (t : A) ≠ 0) (hsing : ¬ IsRegularLocalRing (D.LocalRing M hQM)) :
    Q ∈ M ^ 2 := by
  by_contra hn
  let S := Localization.AtPrime M
  let R := D.LocalRing M hQM
  let q : S := algebraMap (Plane A) S Q
  let : IsRegularLocalRing S := plane_local_regular M
  have hq : q ∈ maximalIdeal S := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal M S]
    exact Ideal.mem_map_of_mem _ hQM
  have hq2 : q ∉ maximalIdeal S ^ 2 := by
    intro h
    apply hn
    rw [← IsLocalization.AtPrime.under_maximalIdeal_pow M S 2]
    exact h
  have hregular := (IsRegularLocalRing.regularLocal_quotient_parameter S 1
    (by simpa using plane_local_dimension M) q hq hq2).1
  let : IsRegularLocalRing (S ⧸ Ideal.span {q}) := hregular
  let : IsRegularLocalRing (R ⧸ Ideal.span {D.parameter M hQM}) :=
    IsRegularLocalRing.of_ringEquiv (R := S ⧸ Ideal.span {q})
      (R' := R ⧸ Ideal.span {D.parameter M hQM}) (D.localQuotientEquiv M hQM).symm
  let : IsDomain R := D.localRing_isDomain M hQM ht
  apply hsing
  apply IsRegularLocalRing.of_quotient_span_singleton R (D.parameter M hQM)
  intro x y h
  exact mul_left_cancel₀ (D.parameter_ne_zero M hQM ht)
    (by simpa only [smul_eq_mul] using h)

/-- The actual child has dimension two, from the nonzero original plane equation
and the original nonzero exceptional parameter. -/
theorem local_dimension [IsNoetherianRing A] [IsDomain A]
    (ht : (t : A) ≠ 0) (hQ0 : Q ≠ 0) : ringKrullDim (D.LocalRing M hQM) = 2 := by
  let R := D.LocalRing M hQM
  let : IsDomain R := D.localRing_isDomain M hQM ht
  have hquot : ringKrullDim (R ⧸ Ideal.span {D.parameter M hQM}) = 1 :=
    (ringKrullDim_eq_of_ringEquiv (D.localQuotientEquiv M hQM)).trans
      (plane_quotient_dimension M Q hQM hQ0)
  have hregular : D.parameter M hQM ∈ R⁰ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr (D.parameter_ne_zero M hQM ht)
  have hlo := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hregular
  have hhi := Ideal.height_le_ringKrullDim_quotient_add_one
    (D.parameter_mem_maximal M hQM)
  rw [maximalIdeal_height_eq_ringKrullDim, hquot] at hhi
  rw [hquot] at hlo
  have htwo : (1 : WithBot ℕ∞) + 1 = 2 := by
    calc
      (1 : WithBot ℕ∞) + 1 = ((1 + 1 : ℕ) : WithBot ℕ∞) := by
        rw [Nat.cast_add, Nat.cast_one]
      _ = 2 := rfl
  rw [htwo] at hhi hlo
  exact le_antisymm hhi hlo

private theorem principal_quotient_isLocal
    (R : Type u) [CommRing R] [IsLocalRing R] (x : R) (hx : x ∈ maximalIdeal R) :
    IsLocalRing (R ⧸ Ideal.span {x}) := by
  have hproper : Ideal.span {x} ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top
      ((Ideal.span_singleton_le_iff_mem (maximalIdeal R)).mpr hx)
  let : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hproper
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x}))
    Ideal.Quotient.mk_surjective

/-- Two generators of the actual regular plane localization lift, together with
exactly the original exceptional element, to generators of the child maximal ideal. -/
theorem maximalIdeal_generated_by_parameter :
    ∃ x y : D.LocalRing M hQM, maximalIdeal (D.LocalRing M hQM) =
      Ideal.span ({D.parameter M hQM, x, y} : Set (D.LocalRing M hQM)) := by
  let R := D.LocalRing M hQM
  let S := Localization.AtPrime M
  let RQ := R ⧸ Ideal.span {D.parameter M hQM}
  let : IsLocalRing RQ := principal_quotient_isLocal R _ (D.parameter_mem_maximal M hQM)
  let : IsRegularLocalRing S := plane_local_regular M
  let η : S →+* RQ := (D.localQuotientEquiv M hQM).symm.toRingHom.comp
    (Ideal.Quotient.mk (Ideal.span {algebraMap (Plane A) S Q}))
  have hη : Function.Surjective η :=
    (D.localQuotientEquiv M hQM).symm.surjective.comp Ideal.Quotient.mk_surjective
  obtain ⟨a, b, _, _, hab, _⟩ :=
    IsRegularLocalRing.exists_regularPair S (plane_local_dimension M)
  have hgenQ : Ideal.span ({η a, η b} : Set RQ) = maximalIdeal RQ := by
    have h := congrArg (Ideal.map η) hab
    rw [Ideal.map_span, Set.image_pair, map_maximalIdeal_of_surjective η hη] at h
    exact h
  let qR : R →+* RQ := Ideal.Quotient.mk (Ideal.span {D.parameter M hQM})
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (η a)
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (η b)
  have hmap : (Ideal.span ({x, y} : Set R)).map qR = maximalIdeal RQ := by
    rw [Ideal.map_span, Set.image_pair]
    rw [hx, hy]
    exact hgenQ
  let : IsLocalHom qR := IsLocalHom.of_surjective qR Ideal.Quotient.mk_surjective
  have h := congrArg (Ideal.comap qR) hmap
  have hker : (⊥ : Ideal RQ).comap qR = Ideal.span {D.parameter M hQM} := Ideal.mk_ker
  rw [Ideal.comap_map_of_surjective qR Ideal.Quotient.mk_surjective, hker,
    maximalIdeal_comap qR] at h
  refine ⟨x, y, ?_⟩
  symm
  rw [Ideal.span_insert, sup_comm]
  exact h

/-- In a singular child, the same original exceptional parameter remains minimal.
Dimension and the three-generator presentation are derived above. -/
theorem parameter_not_mem_sq [IsNoetherianRing A] [IsDomain A]
    (ht : (t : A) ≠ 0) (hQ0 : Q ≠ 0)
    (hsing : ¬ IsRegularLocalRing (D.LocalRing M hQM)) :
    D.parameter M hQM ∉ maximalIdeal (D.LocalRing M hQM) ^ 2 := by
  obtain ⟨x, y, hgen⟩ := D.maximalIdeal_generated_by_parameter M hQM
  exact first_not_mem_sq_of_span_triple_of_not_regular (D.LocalRing M hQM)
    (D.parameter M hQM) x y hgen (D.local_dimension M hQM ht hQ0) hsing

/-- The actual child residue field identifies with the original plane-point quotient.
This comparison is constructed before any rationality conclusion. -/
def residueEquiv : ResidueField (D.LocalRing M hQM) ≃+* Plane A ⧸ M := by
  let : Field (Plane A ⧸ M) := Ideal.Quotient.field M
  exact RingEquiv.ofBijective (ResidueField.lift (D.localPoint M hQM))
    ⟨RingHom.injective _, fun z => by
      obtain ⟨c, rfl⟩ := D.point_surjective M hQM z
      exact ⟨residue (D.LocalRing M hQM)
        (algebraMap (Chart A t) (D.LocalRing M hQM) c),
          D.localPoint_algebraMap M hQM c⟩⟩

/-- The comparison of residue fields preserves the original coefficient map. -/
theorem residueEquiv_coefficient (a : A) :
    D.residueEquiv M hQM (residue (D.LocalRing M hQM) (D.localMap M hQM a)) =
      algebraMap (ResidueField A) (Plane A ⧸ M) (residue A a) := by
  let : Field (Plane A ⧸ M) := Ideal.Quotient.field M
  change D.localPoint M hQM (D.localMap M hQM a) = _
  exact D.localPoint_base M hQM a

/-- The original induced residue homomorphism, followed by the actual plane-residue
comparison, is literally the original constant map. -/
theorem residue_map_comparison :
    let _ := D.localMap_isLocal M hQM
    (D.residueEquiv M hQM).toRingHom.comp
      (ResidueField.map (D.localMap M hQM)) =
      algebraMap (ResidueField A) (Plane A ⧸ M) := by
  let : IsLocalHom (D.localMap M hQM) := D.localMap_isLocal M hQM
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro a
  exact D.residueEquiv_coefficient M hQM a

/-- At a singular actual chart point in Case I, the ORIGINAL induced residue map
is bijective. No abstract field isomorphism, separability, or coefficient-field
section replaces that homomorphism. -/
theorem residue_map_bijective [IsNoetherianRing A] [IsDomain A]
    (ht : (t : A) ≠ 0) (hQ0 : Q ≠ 0) (hdeg : Q.totalDegree ≤ 2)
    (hcase : ¬ ∃ c : ResidueField A, c ≠ 0 ∧ ∃ l : Plane A,
      l.totalDegree ≤ 1 ∧ Q = MvPolynomial.C c * l ^ 2)
    (hsing : ¬ IsRegularLocalRing (D.LocalRing M hQM)) :
    let _ := D.localMap_isLocal M hQM
    Function.Bijective (ResidueField.map (D.localMap M hQM)) := by
  let : IsLocalHom (D.localMap M hQM) := D.localMap_isLocal M hQM
  have hα := plane_residue_bijective M Q hQ0 hdeg
    (D.equation_mem_sq_of_not_regular M hQM ht hsing) hcase
  refine ⟨(ResidueField.map (D.localMap M hQM)).injective, ?_⟩
  intro z
  obtain ⟨a, ha⟩ := hα.surjective (D.residueEquiv M hQM z)
  refine ⟨a, (D.residueEquiv M hQM).injective ?_⟩
  exact (RingHom.congr_fun (D.residue_map_comparison M hQM) a).trans ha

end Presentation
end Presentation

end Localization.Away.CaseOne
