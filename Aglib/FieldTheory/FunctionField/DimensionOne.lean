/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.NoetherNormalization.DimensionOne
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.Localization.Integral

/-! # Actual fraction fields in dimension at most one

A fraction field of a finite-type domain of dimension at most one is algebraic
over the constants or over an actual embedded one-variable rational function
field. The latter embedding respects the supplied constant-field map.
-/

@[expose] public noncomputable section

attribute [local instance] Polynomial.algebra

namespace Field

variable (k A E : Type*) [Field k] [CommRing A] [IsDomain A] [Field E]
  [Algebra k A] [Algebra k E] [Algebra A E] [IsScalarTower k A E]
  [IsFractionRing A E]

omit [IsDomain A] in
/-- An actual integral polynomial normalization induces the compatible rational
function field algebra on the original fraction field. -/
theorem exists_ratFuncAlgebra_of_integral_polynomial
    (g : Polynomial k →ₐ[k] A) (hg : Function.Injective g) (hint : g.IsIntegral) :
    ∃ a : Algebra (RatFunc k) E,
      letI := a
      Algebra.IsAlgebraic (RatFunc k) E ∧ IsScalarTower k (RatFunc k) E := by
  let h : Polynomial k →ₐ[k] E := (IsScalarTower.toAlgHom k A E).comp g
  have hh : Function.Injective h := (IsFractionRing.injective A E).comp hg
  let i : RatFunc k →ₐ[k] E := IsFractionRing.liftAlgHom hh
  let a := i.toRingHom.toAlgebra
  refine ⟨a, ?_⟩
  let : Algebra (RatFunc k) E := a
  let : Algebra (Polynomial k) A := g.toRingHom.toAlgebra
  let : Algebra (Polynomial k) E := h.toRingHom.toAlgebra
  let : IsScalarTower (Polynomial k) A E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower (Polynomial k) (RatFunc k) E :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      exact (IsFractionRing.lift_algebraMap (K := RatFunc k) hh x).symm)
  let : Algebra.IsIntegral (Polynomial k) A := ⟨hint⟩
  refine ⟨isAlgebraic_of_isFractionRing (Polynomial k) A (RatFunc k) E, ?_⟩
  exact IsScalarTower.of_algebraMap_eq (fun x => (i.commutes x).symm)

/-- Finite-type domains of dimension at most one have algebraic or one-variable
algebraic function fields, without a perfectness or separable-generation premise. -/
theorem algebraic_or_exists_ratFuncAlgebra_of_dim_le_one
    [Algebra.FiniteType k A] (hdim : ringKrullDim A ≤ 1) :
    Algebra.IsAlgebraic k E ∨ ∃ a : Algebra (RatFunc k) E,
      letI := a
      Algebra.IsAlgebraic (RatFunc k) E ∧ IsScalarTower k (RatFunc k) E := by
  obtain ⟨n, hn, g, hg, hint⟩ :=
    NoetherNormalization.exists_integral_inj_algHom_dim_le_one k A hdim
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
  · left
    let e := (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).symm
    have he : e.toRingHom.IsIntegral :=
      RingHom.isIntegral_of_surjective _ e.surjective
    have hf : (algebraMap k A).IsIntegral := by
      have hcomp := he.trans e.toRingHom g.toRingHom hint
      have hmap : g.toRingHom.comp e.toRingHom = algebraMap k A := by
        ext x
        exact (g.comp e.toAlgHom).commutes x
      rwa [hmap] at hcomp
    let : Algebra.IsIntegral k A := ⟨hf⟩
    exact (IsFractionRing.isAlgebraic_iff' k A E).mp inferInstance
  · right
    let e := (MvPolynomial.uniqueAlgEquiv k (Fin 1)).symm
    let g' : Polynomial k →ₐ[k] A := g.comp e.toAlgHom
    have he : e.toRingHom.IsIntegral :=
      RingHom.isIntegral_of_surjective _ e.surjective
    exact exists_ratFuncAlgebra_of_integral_polynomial k A E g'
      (hg.comp e.injective) (he.trans e.toRingHom g.toRingHom hint)

end Field
