/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.Tactic.LinearCombination

/-!
# Nonmonic standard-etale presentations

Relocated unchanged declarations from R5 revision
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`; original namespaces and explicit
source and hypothesis boundaries are retained.
-/

/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/RingTheory/Etale/NonmonicPair.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`92486f1ce8ce88332540cf6cb0321491402f7f093bd272ed2f80dcbff9152e39`.
-/

@[expose] public section

section Recovered25NonmonicEtale
/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from mathlib's StandardEtale.lean by dropping the unused monicity field.
-/

/-!
A nonmonic form of mathlib's standard-etale presentation. The square-zero
lifting proof below is adapted from Mathlib/RingTheory/Etale/StandardEtale.lean
(Andrew Yang, Apache 2.0), dropping its unused monicity field.
-/
noncomputable section
open Polynomial
open scoped Bivariate
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

variable (R) in
/-- Arbitrary one-polynomial presentation with an explicit derivative-invertibility witness. -/
structure NonmonicEtalePair : Type _ where
  /-- The arbitrary polynomial to be quotiented out. -/
  f : R[X]
  /-- The polynomial to be localized away from in a one-polynomial localization algebra. -/
  g : R[X]
  cond : ∃ p₁ p₂ n, derivative f * p₁ + f * p₂ = g ^ n

variable (P : NonmonicEtalePair R)

/-- The one-polynomial localization algebra `R[X][Y]/⟨f, Yg-1⟩` associated to a `NonmonicEtalePair
R`.
Also see
`equivPolynomialQuotient   : P.Ring ≃ R[X][Y]/⟨f, Yg-1⟩`
`equivAwayAdjoinRoot       : P.Ring ≃ (R[X]/f)[1/g]` -/
protected def NonmonicEtalePair.Ring := R[X][Y] ⧸ Ideal.span {C P.f, Y * C P.g - 1}
  deriving CommRing, Algebra R

namespace NonmonicEtalePair

/-- The `X` in the one-polynomial localization algebra `R[X][Y]/⟨f, Yg-1⟩`. -/
protected def X : P.Ring := Ideal.Quotient.mk _ (C .X)

/-- There is a map from a one-polynomial localization algebra `R[X][Y]/⟨f, Yg-1⟩` to `S` sending `X`
to `x` iff
`f(x) = 0` and `g(x)` is invertible. Also see `NonmonicEtalePair.homEquiv`. -/
def HasMap (x : S) : Prop :=
  aeval x P.f = 0 ∧ IsUnit (aeval x P.g)

/-- The map `R[X][Y]/⟨f, Yg-1⟩ →ₐ[R] S` sending `X` to `x`, given `P.HasMap x`. -/
def lift (x : S) (h : P.HasMap x) : P.Ring →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ (aevalAeval x ↑(h.2.unit⁻¹))
    (Ideal.span_le (I := RingHom.ker _).mpr (by simp [Set.pair_subset_iff, h.1]))

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma lift_X (x : S) (h : P.HasMap x) : P.lift x h P.X = x := by
  simp [lift, NonmonicEtalePair.Ring, NonmonicEtalePair.X]

variable {P} in
lemma HasMap.map {x : S} (h : P.HasMap x) (f : S →ₐ[R] T) : P.HasMap (f x) :=
  ⟨by simp [aeval_algHom, h.1], by simpa [aeval_algHom] using h.2.map f⟩

lemma HasMap.isUnit_derivative_f {x : S} (h : P.HasMap x) :
    IsUnit (P.f.derivative.aeval x) := by
  obtain ⟨p₁, p₂, n, e⟩ := P.cond
  have : aeval x P.f.derivative ∣ aeval x P.g ^ n :=
    ⟨_, by simpa [h.1] using congr(aeval x $e.symm)⟩
  exact isUnit_of_dvd_unit this (.pow _ h.2)

set_option backward.isDefEq.respectTransparency false in
lemma aeval_X_g_mul_mk_X : aeval P.X P.g * Ideal.Quotient.mk _ .X = 1 := by
  have : aeval (R := R) P.X = (Ideal.Quotient.mkₐ _ _).comp Polynomial.CAlgHom := by
    ext; simp [NonmonicEtalePair.Ring, NonmonicEtalePair.X]
  rw [this]
  dsimp [NonmonicEtalePair.Ring]
  rw [← map_mul, ← map_one (Ideal.Quotient.mk _), ← sub_eq_zero, ← map_sub, mul_comm]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))

set_option backward.isDefEq.respectTransparency false in
variable {P} in
lemma hasMap_X : P.HasMap P.X :=
  have : aeval (R := R) P.X = (Ideal.Quotient.mkₐ _ _).comp Polynomial.CAlgHom := by
    ext; simp [NonmonicEtalePair.Ring, NonmonicEtalePair.X]
  ⟨this ▸ Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _)),
    IsUnit.of_mul_eq_one _ P.aeval_X_g_mul_mk_X⟩

set_option backward.isDefEq.respectTransparency false in
variable {P} in
@[ext]
lemma hom_ext {f g : P.Ring →ₐ[R] S} (H : f P.X = g P.X) : f = g := by
  have H : (f.comp (Ideal.Quotient.mkₐ R _)).comp CAlgHom =
    (g.comp (Ideal.Quotient.mkₐ R _)).comp CAlgHom := Polynomial.algHom_ext (by simpa)
  have H' : aeval (R := R) P.X = (Ideal.Quotient.mkₐ _ _).comp CAlgHom := by
    ext; simp [NonmonicEtalePair.Ring, NonmonicEtalePair.X]
  refine Ideal.Quotient.algHom_ext _ (Polynomial.algHom_ext' H ?_)
  change f.toMonoidHom (Ideal.Quotient.mk _ .X) = g.toMonoidHom (Ideal.Quotient.mk _ .X)
  rw [← show (↑P.hasMap_X.2.unit⁻¹ : P.Ring) = Ideal.Quotient.mk _ .X from
    Units.mul_eq_one_iff_inv_eq.mp P.aeval_X_g_mul_mk_X, ← Units.coe_map_inv, ← Units.coe_map_inv]
  congr 2
  ext
  simpa [H'] using! congr($H _)

@[simp]
lemma lift_X_left : P.lift P.X P.hasMap_X = .id _ _ :=
  P.hom_ext (by simp)

lemma inv_aeval_X_g :
    (↑P.hasMap_X.2.unit⁻¹ : P.Ring) = Ideal.Quotient.mk _ .X :=
  Units.mul_eq_one_iff_inv_eq.mp P.aeval_X_g_mul_mk_X

/-- Maps out of `R[X][Y]/⟨f, Yg-1⟩` corresponds bijectively with
`x` such that `f(x) = 0` and `g(x)` is invertible. -/
@[simps]
def homEquiv : (P.Ring →ₐ[R] S) ≃ { x : S // P.HasMap x } where
  toFun f := ⟨f P.X, hasMap_X.map f⟩
  invFun x := P.lift x.1 x.2
  left_inv f := P.hom_ext (by simp)
  right_inv x := by simp

lemma existsUnique_hasMap_of_hasMap_quotient_of_sq_eq_bot
    (I : Ideal S) (hI : I ^ 2 = ⊥) (x : S) (hx : P.HasMap (Ideal.Quotient.mk I x)) :
    ∃! ε, ε ∈ I ∧ P.HasMap (x + ε) := by
  have hf := Ideal.Quotient.eq_zero_iff_mem.mp
    ((aeval_algHom_apply (Ideal.Quotient.mkₐ R I) _ _).symm.trans hx.1)
  obtain ⟨⟨_, a, ha, -⟩, rfl⟩ := hx.2
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  simp_rw [← Ideal.Quotient.mkₐ_eq_mk R, aeval_algHom_apply, ← map_mul, ← map_one
    (Ideal.Quotient.mkₐ R I), Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at ha
  obtain ⟨p₁, p₂, n, e⟩ := P.cond
  apply_fun aeval x at e
  simp only [map_add, map_mul, map_pow] at e
  obtain ⟨ε, hεI, b, hb⟩ : ∃ ε ∈ I, ∃ b, aeval x (derivative P.f) * b = 1 + ε := by
    refine ⟨_, ?_, (a ^ n * aeval x p₁), sub_eq_iff_eq_add'.mp rfl⟩
    convert_to (aeval x P.g * a) ^ n - 1 - aeval x P.f * (a ^ n * aeval x p₂) ∈ I
    · linear_combination a ^ n * e
    · exact sub_mem (Ideal.mem_of_dvd _ (sub_one_dvd_pow_sub_one _ _) ha) (I.mul_mem_right _ hf)
  have : aeval x P.f ^ 2 = 0 := hI.le (Ideal.pow_mem_pow hf 2)
  have : aeval x P.f * ε = 0 := ((pow_two _).symm.trans hI).le (Ideal.mul_mem_mul hf hεI)
  refine ⟨aeval x P.f * -b, ⟨I.mul_mem_right _ hf, ?_, ?_⟩, ?_⟩
  · rw [Polynomial.aeval_add_of_sq_eq_zero _ _ _ (by grind)]; grind
  · rw [← IsNilpotent.isUnit_quotient_mk_iff (I := I) ⟨2, hI⟩, ← Ideal.Quotient.mkₐ_eq_mk R,
      ← aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, map_add,
      Ideal.Quotient.eq_zero_iff_mem.mpr (I.mul_mem_right _ hf), add_zero]
    exact hx.2
  · rintro ε' ⟨hε'I, hε', hε''⟩
    rw [Polynomial.aeval_add_of_sq_eq_zero _ _ _ (hI.le (Ideal.pow_mem_pow hε'I 2))] at hε'
    have : ε * ε' = 0 := ((pow_two _).symm.trans hI).le (Ideal.mul_mem_mul hεI hε'I)
    grind

-- The proof uses no degree or monicity hypothesis.
instance : Algebra.FormallyEtale R P.Ring := by
  refine Algebra.FormallyEtale.iff_comp_bijective.mpr fun S _ _ I hI ↦ ?_
  rw [← P.homEquiv.symm.bijective.of_comp_iff, ← P.homEquiv.bijective.of_comp_iff']
  suffices ∀ x, P.HasMap (Ideal.Quotient.mk I x) → ∃! a : { x : S // P.HasMap x }, a - x ∈ I by
    simpa [Function.bijective_iff_existsUnique, Ideal.Quotient.mk_surjective.forall,
      Subtype.ext_iff, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  intro x hx
  obtain ⟨ε, ⟨hεI, hε⟩, H⟩ := P.existsUnique_hasMap_of_hasMap_quotient_of_sq_eq_bot I hI _ hx
  exact ⟨⟨x + ε, hε⟩, by simpa, fun y hy ↦
    Subtype.ext (sub_eq_iff_eq_add'.mp (H _ ⟨hy, by simpa using y.2⟩))⟩

instance : Algebra.Etale R P.Ring where
  finitePresentation := .quotient (Submodule.fg_span (by simp))

/-- An `AlgEquiv` between `P.Ring` and `R[X][Y]/⟨f, Yg-1⟩`,
to not abuse the defeq between the two. -/
def equivPolynomialQuotient :
    P.Ring ≃ₐ[R] R[X][Y] ⧸ Ideal.span {C P.f, Y * C P.g - 1} := .refl ..

set_option backward.isDefEq.respectTransparency.types false in
/-- `R[X][Y]/⟨f, Yg-1⟩ ≃ (R[X]/f)[1/g]` -/
def equivAwayAdjoinRoot :
    P.Ring ≃ₐ[R] Localization.Away (AdjoinRoot.mk P.f P.g) := by
  refine .ofAlgHom (P.lift (algebraMap (AdjoinRoot P.f) _ (.root P.f)) ⟨?_, ?_⟩)
    (IsLocalization.Away.liftAlgHom (AdjoinRoot.mk P.f P.g)
      (f := AdjoinRoot.liftAlgHom _ _ P.X P.hasMap_X.1) P.hasMap_X.2) ?_ ?_
  · rw [aeval_algebraMap_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  · rw [aeval_algebraMap_apply, AdjoinRoot.aeval_eq]
    exact IsLocalization.Away.algebraMap_isUnit ..
  · ext; simp [Algebra.algHom]
  · ext; simp

end NonmonicEtalePair

end -- original noncomputable section
end Recovered25NonmonicEtale
