/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.GradedAlgebra.AlgHom
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# The full kernel of an original monic quadratic graded presentation

The original variables are `V = X 0`, `S = X 1`, and `T = X 2`.
A genuine relation `V² + q₁(S,T)V + q₀(S,T)` and the genuine target Hilbert
function `2n+1` determine the entire kernel of the original graded surjection.

Monic division constructs the original normal representatives. Their degree-n
subspace has the two actual monomial families `S^(n-i)T^i` and
`V*S^(n-1-i)T^i`. Their dimensions are `n+1` and `n`; the original graded
map is therefore injective on every normal component. No presentation,
normal-form basis, coefficient section, or kernel equality is assumed.

The Hilbert function is an explicit premise of this algebraic result.
Its rational/Gorenstein geometric supplier is a separate obligation.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v

open Polynomial

namespace GradedAlgebra.MonicQuadratic

variable {k : Type u} [Field k]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Include the original binary variables as `S = X 1` and `T = X 2`. -/
def binaryInclusion : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 3) k :=
  MvPolynomial.rename Fin.succ

/-- The original homogeneous relation, with `V = X 0`. -/
def relation (q₁ q₀ : MvPolynomial (Fin 2) k) : MvPolynomial (Fin 3) k :=
  MvPolynomial.X 0 ^ 2 + binaryInclusion q₁ * MvPolynomial.X 0 + binaryInclusion q₀

/-- Regrouping the original variable V retains every original binary coefficient. -/
theorem finSuccEquiv_binaryInclusion (p : MvPolynomial (Fin 2) k) :
    MvPolynomial.finSuccEquiv k 2 (binaryInclusion p) = Polynomial.C p := by
  have h : (MvPolynomial.finSuccEquiv k 2).toAlgHom.comp binaryInclusion =
      (Polynomial.CAlgHom : MvPolynomial (Fin 2) k →ₐ[k] (MvPolynomial (Fin 2) k)[X]) := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa only [AlgHom.comp_apply, binaryInclusion, MvPolynomial.rename_X,
      AlgEquiv.coe_toAlgHom, Polynomial.CAlgHom_apply] using
      (MvPolynomial.finSuccEquiv_X_succ (R := k) (n := 2) (j := i))
  exact AlgHom.congr_fun h p

private def univariateRelation (q₁ q₀ : MvPolynomial (Fin 2) k) :
    (MvPolynomial (Fin 2) k)[X] := X ^ 2 + C q₁ * X + C q₀

/-- The original coordinate regrouping makes the relation literally monic in V. -/
theorem finSuccEquiv_relation (q₁ q₀ : MvPolynomial (Fin 2) k) :
    MvPolynomial.finSuccEquiv k 2 (relation q₁ q₀) = X ^ 2 + C q₁ * X + C q₀ := by
  rw [relation, map_add, map_add, map_pow, map_mul,
    MvPolynomial.finSuccEquiv_X_zero, finSuccEquiv_binaryInclusion,
    finSuccEquiv_binaryInclusion]

/-- The displayed relation has the original total degree two. -/
theorem relation_isHomogeneous (q₁ q₀ : MvPolynomial (Fin 2) k)
    (h₁ : q₁.IsHomogeneous 1) (h₀ : q₀.IsHomogeneous 2) :
    (relation q₁ q₀).IsHomogeneous 2 :=
  ((MvPolynomial.isHomogeneous_X_pow 0 2).add
    ((h₁.rename_isHomogeneous (f := Fin.succ)).mul
      (MvPolynomial.isHomogeneous_X k 0))).add
    (h₀.rename_isHomogeneous (f := Fin.succ))

private theorem univariateRelation_monic (q₁ q₀ : MvPolynomial (Fin 2) k) :
    (univariateRelation q₁ q₀).Monic := by
  rw [univariateRelation, add_assoc]
  exact Polynomial.monic_X_pow_add Polynomial.degree_linear_lt

private theorem univariateRelation_natDegree (q₁ q₀ : MvPolynomial (Fin 2) k) :
    (univariateRelation q₁ q₀).natDegree = 2 := by
  simpa only [univariateRelation, map_one, one_mul] using
    (Polynomial.natDegree_quadratic (a := (1 : MvPolynomial (Fin 2) k))
      (b := q₁) (c := q₀) one_ne_zero)

private def normalRemainder (q₁ q₀ : MvPolynomial (Fin 2) k)
    (p : MvPolynomial (Fin 3) k) : MvPolynomial (Fin 3) k :=
  (MvPolynomial.finSuccEquiv k 2).symm
    ((MvPolynomial.finSuccEquiv k 2 p) %ₘ univariateRelation q₁ q₀)

private theorem normalRemainder_degreeOf (q₁ q₀ : MvPolynomial (Fin 2) k)
    (p : MvPolynomial (Fin 3) k) : (normalRemainder q₁ q₀ p).degreeOf 0 ≤ 1 := by
  have hne : univariateRelation q₁ q₀ ≠ 1 := by
    intro h
    have hd := congrArg Polynomial.natDegree h
    rw [univariateRelation_natDegree, Polynomial.natDegree_one] at hd
    omega
  have h := Polynomial.natDegree_modByMonic_lt
    (MvPolynomial.finSuccEquiv k 2 p) (univariateRelation_monic q₁ q₀) hne
  rw [univariateRelation_natDegree] at h
  rw [← MvPolynomial.natDegree_finSuccEquiv, normalRemainder,
    AlgEquiv.apply_symm_apply]
  omega

private theorem sub_normalRemainder_mem (q₁ q₀ : MvPolynomial (Fin 2) k)
    (p : MvPolynomial (Fin 3) k) :
    p - normalRemainder q₁ q₀ p ∈ Ideal.span {relation q₁ q₀} := by
  apply Ideal.mem_span_singleton.mpr
  let e := MvPolynomial.finSuccEquiv k 2
  have hd : univariateRelation q₁ q₀ ∣ e p - e (normalRemainder q₁ q₀ p) := by
    have her : e (normalRemainder q₁ q₀ p) =
        e p %ₘ univariateRelation q₁ q₀ := e.apply_symm_apply _
    rw [her]
    refine ⟨e p /ₘ univariateRelation q₁ q₀, ?_⟩
    exact sub_eq_iff_eq_add.mpr
      ((Polynomial.modByMonic_add_div (e p) (univariateRelation q₁ q₀)).symm.trans
        (add_comm _ _))
  have he : e (relation q₁ q₀) = univariateRelation q₁ q₀ :=
    finSuccEquiv_relation q₁ q₀
  rw [← he] at hd
  simpa only [map_sub, AlgEquiv.symm_apply_apply] using map_dvd e.symm hd

private theorem eq_of_normal_sub_mem (q₁ q₀ : MvPolynomial (Fin 2) k)
    (p r : MvPolynomial (Fin 3) k) (hp : p.degreeOf 0 ≤ 1) (hr : r.degreeOf 0 ≤ 1)
    (hsub : p - r ∈ Ideal.span {relation q₁ q₀}) : p = r := by
  let e := MvPolynomial.finSuccEquiv k 2
  have hd := map_dvd e (Ideal.mem_span_singleton.mp hsub)
  have hd' : univariateRelation q₁ q₀ ∣ e p - e r := by
    simpa only [e, univariateRelation, map_sub, finSuccEquiv_relation] using hd
  have hmod (s : MvPolynomial (Fin 3) k) (hs : s.degreeOf 0 ≤ 1) :
      e s %ₘ univariateRelation q₁ q₀ = e s := by
    apply (Polynomial.modByMonic_eq_self_iff (univariateRelation_monic q₁ q₀)).mpr
    calc
      (e s).degree ≤ (e s).natDegree := Polynomial.degree_le_natDegree
      _ < (2 : WithBot ℕ) := by
        rw [MvPolynomial.natDegree_finSuccEquiv]
        exact_mod_cast (by omega : s.degreeOf 0 < 2)
      _ = (univariateRelation q₁ q₀).degree := by
        rw [Polynomial.degree_eq_natDegree (univariateRelation_monic q₁ q₀).ne_zero,
          univariateRelation_natDegree]
        exact_mod_cast (rfl : (2 : ℕ) = 2)
  have h := Polynomial.modByMonic_eq_of_dvd_sub (univariateRelation_monic q₁ q₀) hd'
  rw [hmod p hp, hmod r hr] at h
  exact e.injective h

private theorem degreeOf_homogeneousComponent_le (p : MvPolynomial (Fin 3) k) (n : ℕ) :
    (MvPolynomial.homogeneousComponent n p).degreeOf 0 ≤ p.degreeOf 0 := by
  classical
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  rw [MvPolynomial.support_homogeneousComponent] at hd
  exact (MvPolynomial.degreeOf_le_iff.mp le_rfl) d (Finset.mem_filter.mp hd).1

private theorem normalRemainder_isHomogeneous (q₁ q₀ : MvPolynomial (Fin 2) k)
    (h₁ : q₁.IsHomogeneous 1) (h₀ : q₀.IsHomogeneous 2)
    (p : MvPolynomial (Fin 3) k) (n : ℕ) (hp : p.IsHomogeneous n) :
    (normalRemainder q₁ q₀ p).IsHomogeneous n := by
  let I : Ideal (MvPolynomial (Fin 3) k) := Ideal.span {relation q₁ q₀}
  have hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) k) :=
    Ideal.homogeneous_span _ _ (by
      rintro f (rfl : f = relation q₁ q₀)
      exact ⟨2, relation_isHomogeneous q₁ q₀ h₁ h₀⟩)
  let r := normalRemainder q₁ q₀ p
  have hpr : p - r ∈ I := sub_normalRemainder_mem q₁ q₀ p
  have hpn : p - MvPolynomial.homogeneousComponent n r ∈ I := by
    have h := MvPolynomial.homogeneousComponent_mem_of_mem hI hpr n
    rwa [map_sub, MvPolynomial.homogeneousComponent_eq_self hp] at h
  have hdiff : r - MvPolynomial.homogeneousComponent n r ∈ I := by
    have he : r - MvPolynomial.homogeneousComponent n r =
        (p - MvPolynomial.homogeneousComponent n r) - (p - r) := by ring
    rw [he]
    exact I.sub_mem hpn hpr
  have he : r = MvPolynomial.homogeneousComponent n r :=
    eq_of_normal_sub_mem q₁ q₀ _ _ (normalRemainder_degreeOf q₁ q₀ p)
      ((degreeOf_homogeneousComponent_le r n).trans (normalRemainder_degreeOf q₁ q₀ p)) hdiff
  rw [show normalRemainder q₁ q₀ p = r from rfl, he]
  exact MvPolynomial.homogeneousComponent_mem n r

private theorem degree_fin_three (d : Fin 3 →₀ ℕ) : d.degree = d 0 + d 1 + d 2 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_succ, Fin.sum_univ_two]
  exact (Nat.add_assoc _ _ _).symm

private abbrev NormalIndex (n : ℕ) := {d : Fin 3 →₀ ℕ // d.degree = n ∧ d 0 ≤ 1}

private def normalIndexLeft (n : ℕ) (i : Fin (n + 1)) : NormalIndex n :=
  ⟨Finsupp.single 1 (n - i.val) + Finsupp.single 2 i.val, by
    constructor
    · rw [map_add, Finsupp.degree_single, Finsupp.degree_single,
        Nat.sub_add_cancel (Nat.le_of_lt_succ i.is_lt)]
    · simp⟩

private def normalIndexRight (n : ℕ) (i : Fin n) : NormalIndex n :=
  ⟨Finsupp.single 0 1 + Finsupp.single 1 (n - 1 - i.val) + Finsupp.single 2 i.val, by
    constructor
    · rw [map_add, map_add, Finsupp.degree_single, Finsupp.degree_single,
        Finsupp.degree_single]
      have hi := i.is_lt
      omega
    · simp⟩

private def normalIndexEquiv (n : ℕ) : NormalIndex n ≃ Fin (n + 1) ⊕ Fin n where
  toFun d := if h : d.1 0 = 0 then
    Sum.inl ⟨d.1 2, by
      have hd := d.2.1
      rw [degree_fin_three] at hd
      omega⟩
    else Sum.inr ⟨d.1 2, by
      have hd := d.2.1
      have hv := d.2.2
      rw [degree_fin_three] at hd
      omega⟩
  invFun i := match i with
    | Sum.inl j => normalIndexLeft n j
    | Sum.inr j => normalIndexRight n j
  left_inv d := by
    have hd := d.2.1
    have hv := d.2.2
    rw [degree_fin_three] at hd
    by_cases h : d.1 0 = 0
    · simp only [dite_eq_left h]
      apply Subtype.ext
      ext i
      fin_cases i <;> simp [normalIndexLeft] <;> omega
    · simp only [dite_eq_right h]
      apply Subtype.ext
      ext i
      fin_cases i <;> simp [normalIndexRight] <;> omega
  right_inv i := by
    cases i with
    | inl j => simp [normalIndexLeft]
    | inr j => simp [normalIndexRight]

private def normalSpace (k : Type u) [Field k] (n : ℕ) :
    Submodule k (MvPolynomial (Fin 3) k) :=
  AddMonoidAlgebra.supported k k {d : Fin 3 →₀ ℕ | d.degree = n ∧ d 0 ≤ 1}

private theorem mem_normalSpace_iff (n : ℕ) (p : MvPolynomial (Fin 3) k) :
    p ∈ normalSpace k n ↔ p.IsHomogeneous n ∧ p.degreeOf 0 ≤ 1 := by
  rw [normalSpace, AddMonoidAlgebra.mem_supported]
  constructor
  · intro h
    refine ⟨?_, MvPolynomial.degreeOf_le_iff.mpr fun d hd => (h hd).2⟩
    change p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) k n
    rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
      AddMonoidAlgebra.mem_supported]
    exact fun d hd => (h hd).1
  · rintro ⟨hh, hd⟩ d hdp
    have hh' : p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) k n := hh
    rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
      AddMonoidAlgebra.mem_supported] at hh'
    exact ⟨hh' hdp, (MvPolynomial.degreeOf_le_iff.mp hd) d hdp⟩

private def normalSpaceEquiv (n : ℕ) :
    normalSpace k n ≃ₗ[k] (NormalIndex n →₀ k) :=
  AddMonoidAlgebra.supportedEquivFinsupp (R := k) (S := k)
    {d : Fin 3 →₀ ℕ | d.degree = n ∧ d 0 ≤ 1}

private instance normalSpace_finite (n : ℕ) : Module.Finite k (normalSpace k n) := by
  let _ : Fintype (NormalIndex n) :=
    Fintype.ofEquiv (Fin (n + 1) ⊕ Fin n) (normalIndexEquiv n).symm
  exact Module.Finite.of_surjective (normalSpaceEquiv (k := k) n).symm.toLinearMap
    (normalSpaceEquiv (k := k) n).symm.surjective

private theorem finrank_normalSpace (n : ℕ) :
    Module.finrank k (normalSpace k n) = 2 * n + 1 := by
  let _ : Fintype (NormalIndex n) :=
    Fintype.ofEquiv (Fin (n + 1) ⊕ Fin n) (normalIndexEquiv n).symm
  rw [(normalSpaceEquiv (k := k) n).finrank_eq, Module.finrank_finsupp_self,
    Fintype.card_congr (normalIndexEquiv n), Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  omega

private theorem homogeneousComponent_mem_normalSpace (p : MvPolynomial (Fin 3) k)
    (hp : p.degreeOf 0 ≤ 1) (n : ℕ) :
    MvPolynomial.homogeneousComponent n p ∈ normalSpace k n :=
  (mem_normalSpace_iff n _).mpr ⟨MvPolynomial.homogeneousComponent_mem n p,
    (degreeOf_homogeneousComponent_le p n).trans hp⟩

private theorem map_normalRemainder {G : Type v} [Ring G]
    (q₁ q₀ : MvPolynomial (Fin 2) k) (f : MvPolynomial (Fin 3) k →+* G)
    (hf : f (relation q₁ q₀) = 0) (p : MvPolynomial (Fin 3) k) :
    f (normalRemainder q₁ q₀ p) = f p := by
  have hker : Ideal.span {relation q₁ q₀} ≤ RingHom.ker f := by
    apply Ideal.span_le.mpr
    rintro x (rfl : x = relation q₁ q₀)
    exact hf
  have h := hker (sub_normalRemainder_mem q₁ q₀ p)
  change f (p - normalRemainder q₁ q₀ p) = 0 at h
  rw [map_sub] at h
  exact (sub_eq_zero.mp h).symm

section Presentation

variable {G : Type v} [Ring G] [Algebra k G]
  (H : ℕ → Submodule k G) [GradedAlgebra H]
  (π : MvPolynomial.homogeneousSubmodule (Fin 3) k →ₐᵍ[k] H)

private theorem map_homogeneousComponent (p : MvPolynomial (Fin 3) k) (n : ℕ) :
    π (MvPolynomial.homogeneousComponent n p) = (DirectSum.decompose H (π p) n : G) := by
  have h := _root_.map_directSumDecompose
    (MvPolynomial.homogeneousSubmodule (Fin 3) k) H π (x := p) (i := n)
  have he : (DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin 3) k) p n :
      MvPolynomial (Fin 3) k) = MvPolynomial.homogeneousComponent n p := by
    simpa only [DirectSum.Decomposition.decompose'_eq] using
      MvPolynomial.decomposition.decompose'_apply p n
  exact (congrArg π he).symm.trans h

private def normalMap
    (π : MvPolynomial.homogeneousSubmodule (Fin 3) k →ₐᵍ[k] H)
    (n : ℕ) : normalSpace k n →ₗ[k] H n where
  toFun p := ⟨π (p : MvPolynomial (Fin 3) k), by
    apply π.map_mem
    apply (MvPolynomial.mem_homogeneousSubmodule n (p : MvPolynomial (Fin 3) k)).mpr
    exact ((mem_normalSpace_iff (k := k) n (p : MvPolynomial (Fin 3) k)).mp p.property).1⟩
  map_add' p q := Subtype.ext (map_add π (p : MvPolynomial (Fin 3) k) q)
  map_smul' a p := Subtype.ext (map_smul π.toAlgHom a (p : MvPolynomial (Fin 3) k))

private theorem normalMap_surjective (q₁ q₀ : MvPolynomial (Fin 2) k)
    (h₁ : q₁.IsHomogeneous 1) (h₀ : q₀.IsHomogeneous 2)
    (hπ : Function.Surjective π) (hrel : π (relation q₁ q₀) = 0) (n : ℕ) :
    Function.Surjective (normalMap H π n) := by
  intro y
  obtain ⟨p, hp⟩ := hπ (y : G)
  let a := MvPolynomial.homogeneousComponent n p
  let r := normalRemainder q₁ q₀ a
  have hr : r ∈ normalSpace k n :=
    (mem_normalSpace_iff n r).mpr
      ⟨normalRemainder_isHomogeneous q₁ q₀ h₁ h₀ a n
        (MvPolynomial.homogeneousComponent_mem n p), normalRemainder_degreeOf q₁ q₀ a⟩
  refine ⟨⟨r, hr⟩, Subtype.ext ?_⟩
  change π r = (y : G)
  calc
    _ = π a := map_normalRemainder q₁ q₀ π.toAlgHom.toRingHom hrel a
    _ = (DirectSum.decompose H (π p) n : G) := map_homogeneousComponent H π p n
    _ = y := by rw [hp, DirectSum.decompose_of_mem H y.property]; simp

private theorem normalMap_injective (q₁ q₀ : MvPolynomial (Fin 2) k)
    (h₁ : q₁.IsHomogeneous 1) (h₀ : q₀.IsHomogeneous 2)
    (hπ : Function.Surjective π) (hrel : π (relation q₁ q₀) = 0)
    (hHilbert : ∀ n, Module.finrank k (H n) = 2 * n + 1) (n : ℕ) :
    Function.Injective (normalMap H π n) := by
  have hs := normalMap_surjective H π q₁ q₀ h₁ h₀ hπ hrel n
  let _ : Module.Finite k (H n) := Module.Finite.of_surjective (normalMap H π n) hs
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    ((finrank_normalSpace (k := k) n).trans (hHilbert n).symm)).mpr hs

/-- The true monic quadratic and the genuine Hilbert function determine the
entire kernel of the original graded map, with its original variables retained. -/
theorem kernel_eq_span (q₁ q₀ : MvPolynomial (Fin 2) k)
    (h₁ : q₁.IsHomogeneous 1) (h₀ : q₀.IsHomogeneous 2)
    (hπ : Function.Surjective π) (hrel : π (relation q₁ q₀) = 0)
    (hHilbert : ∀ n, Module.finrank k (H n) = 2 * n + 1) :
    RingHom.ker π.toAlgHom = Ideal.span {relation q₁ q₀} := by
  apply le_antisymm
  · intro p hp
    let r := normalRemainder q₁ q₀ p
    have hrmap : π r = 0 :=
      (map_normalRemainder q₁ q₀ π.toAlgHom.toRingHom hrel p).trans hp
    have hrcomp (n : ℕ) : MvPolynomial.homogeneousComponent n r = 0 := by
      let z : normalSpace k n := ⟨MvPolynomial.homogeneousComponent n r,
        homogeneousComponent_mem_normalSpace r (normalRemainder_degreeOf q₁ q₀ p) n⟩
      have hz : normalMap H π n z = 0 := by
        apply Subtype.ext
        change π (MvPolynomial.homogeneousComponent n r) = 0
        rw [map_homogeneousComponent H π, hrmap]
        exact DirectSum.decompose_of_mem_same H (H n).zero_mem
      have he : z = 0 := normalMap_injective H π q₁ q₀ h₁ h₀ hπ hrel hHilbert n
        (by simpa only [map_zero] using hz)
      exact congrArg Subtype.val he
    have hrzero : r = 0 := by
      rw [← MvPolynomial.sum_homogeneousComponent (φ := r)]
      exact Finset.sum_eq_zero fun n _ => hrcomp n
    have h := sub_normalRemainder_mem q₁ q₀ p
    change p - r ∈ Ideal.span {relation q₁ q₀} at h
    rwa [hrzero, sub_zero] at h
  · apply Ideal.span_le.mpr
    rintro p (rfl : p = relation q₁ q₀)
    exact hrel

/-- The actual quotient by the derived entire kernel is the original target algebra. -/
def quotientEquiv (q₁ q₀ : MvPolynomial (Fin 2) k)
    (h₁ : q₁.IsHomogeneous 1) (h₀ : q₀.IsHomogeneous 2)
    (hπ : Function.Surjective π) (hrel : π (relation q₁ q₀) = 0)
    (hHilbert : ∀ n, Module.finrank k (H n) = 2 * n + 1) :
    (MvPolynomial (Fin 3) k ⧸ Ideal.span {relation q₁ q₀}) ≃ₐ[k] G :=
  (Ideal.quotientEquivAlgOfEq k (kernel_eq_span H π q₁ q₀ h₁ h₀ hπ hrel hHilbert).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := π.toAlgHom) hπ)

/-- Every original polynomial maps through the original graded presentation. -/
theorem quotientEquiv_mk (q₁ q₀ : MvPolynomial (Fin 2) k)
    (h₁ : q₁.IsHomogeneous 1) (h₀ : q₀.IsHomogeneous 2)
    (hπ : Function.Surjective π) (hrel : π (relation q₁ q₀) = 0)
    (hHilbert : ∀ n, Module.finrank k (H n) = 2 * n + 1)
    (p : MvPolynomial (Fin 3) k) :
    quotientEquiv H π q₁ q₀ h₁ h₀ hπ hrel hHilbert
      (Ideal.Quotient.mk (Ideal.span {relation q₁ q₀}) p) = π p := by
  rw [quotientEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    Ideal.quotientKerAlgEquivOfSurjective_mk]
  exact congrFun (GradedAlgHom.coe_toAlgHom π) p

/-- In particular the quotient equivalence retains each original coefficient. -/
theorem quotientEquiv_C (q₁ q₀ : MvPolynomial (Fin 2) k)
    (h₁ : q₁.IsHomogeneous 1) (h₀ : q₀.IsHomogeneous 2)
    (hπ : Function.Surjective π) (hrel : π (relation q₁ q₀) = 0)
    (hHilbert : ∀ n, Module.finrank k (H n) = 2 * n + 1) (a : k) :
    quotientEquiv H π q₁ q₀ h₁ h₀ hπ hrel hHilbert
      (Ideal.Quotient.mk (Ideal.span {relation q₁ q₀}) (MvPolynomial.C a)) = algebraMap k G a := by
  rw [quotientEquiv_mk]
  exact π.toAlgHom.commutes a

/-- In particular the quotient equivalence retains V, S and T at indices 0, 1 and 2. -/
theorem quotientEquiv_X (q₁ q₀ : MvPolynomial (Fin 2) k)
    (h₁ : q₁.IsHomogeneous 1) (h₀ : q₀.IsHomogeneous 2)
    (hπ : Function.Surjective π) (hrel : π (relation q₁ q₀) = 0)
    (hHilbert : ∀ n, Module.finrank k (H n) = 2 * n + 1) (i : Fin 3) :
    quotientEquiv H π q₁ q₀ h₁ h₀ hπ hrel hHilbert
      (Ideal.Quotient.mk (Ideal.span {relation q₁ q₀}) (MvPolynomial.X i)) = π (MvPolynomial.X i) :=
  quotientEquiv_mk H π q₁ q₀ h₁ h₀ hπ hrel hHilbert (MvPolynomial.X i)

end Presentation

end GradedAlgebra.MonicQuadratic
