/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.RationalPrime
public import Aglib.KTheory.MilnorK.Residue.Polynomial.LinearLaurentSeries
public import Aglib.FieldTheory.RatFuncTranslation

/-!
# The actual prime-normal rational norm at every linear place

Literal rational translation commutes with the specified rational-function
norm by coefficient base change. The already-constructed translated Laurent
map identifies the original residue at `X - a` with the original `X` residue
after translation. The proved prime-normal square at `X` therefore gives the
square at every actual linear place, with the original evaluation maps.
-/

@[expose] public noncomputable section

open Polynomial
open scoped RatFunc

namespace Polynomial.LocalResidue

variable {k : Type*} [Field k]

/-- The existing translated completion is ordinary completion after literal translation. -/
theorem linearPlaceLaurentSeriesMap_eq_translation (a : k) :
    linearPlaceLaurentSeriesMap a =
      (algebraMap (RatFunc k) (LaurentSeries k)).comp (RatFunc.translationHom a) := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors k[X])
  apply RingHom.ext
  intro q
  simp only [RingHom.comp_apply, linearPlaceLaurentSeriesMap_polynomial,
    RatFunc.translationHom_polynomial]
  exact RatFunc.coe_coe (algEquivAevalXAddC a q)

end Polynomial.LocalResidue

namespace MilnorK.PolynomialResidue

open Polynomial.LocalResidue

variable {k : Type*} [Field k]

local instance : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩
local instance (a : k) : Fact (Irreducible (X - C a)) := ⟨irreducible_X_sub_C a⟩

/-- The original evaluated residue at `a` is the original residue at zero
after literal rational translation, in every characteristic. -/
theorem residueAt_linear_eq_residueAt_X_translation (a : k) (n : ℕ)
    (x : K (RatFunc k) (n + 1)) :
    map n (linearRootEquiv a).toRingHom (residueAt (X - C a) n x) =
      map n (InfinityResidue.rootXEquiv k).toRingHom
        (residueAt (X : k[X]) n (map (n + 1) (RatFunc.translationHom a) x)) := by
  rw [residueAt_linear_eq_laurentSeries_residue, residueAt_X_eq_laurentSeries_residue,
    linearPlaceLaurentSeriesMap_eq_translation, map_comp, LinearMap.comp_apply]

end MilnorK.PolynomialResidue

namespace MilnorK.PolynomialNorm

open Polynomial.LocalResidue PolynomialResidue

attribute [local instance] Polynomial.algebra

variable {k : Type*} [Field k]

/-- A constant presentation is fixed literally by coefficient translation. -/
theorem polynomial_map_translation_map_C (a : k) (q : k[X]) :
    (q.map (RatFunc.C : k →+* RatFunc k)).map (RatFunc.translationHom a) =
      q.map (RatFunc.C : k →+* RatFunc k) := by
  rw [Polynomial.map_map]
  congr 1
  ext b
  exact RatFunc.translationHom_C a b

variable (p : MonicIrreducible k)

local instance : Fact (Irreducible (p.val.map (RatFunc.C : k →+* RatFunc k))) :=
  ⟨p.property.1.irreducible_map_ratFunc_C p.property.2⟩

/-- Translation of the literal quotient root field becomes translation of
the actual rational-function field under its proved root identification. -/
theorem rationalCoefficientAlgEquiv_comp_translation (a : k) :
    (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).toRingHom.comp
      (adjoinRootMap (RatFunc.translationHom a) (p.val.map RatFunc.C) (p.val.map RatFunc.C)
        (by rw [polynomial_map_translation_map_C])) =
      (RatFunc.translationHom (algebraMap k (AdjoinRoot p.val) a)).comp
        (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).toRingHom := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro x
    change (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1)
      (adjoinRootMap (RatFunc.translationHom a) (p.val.map RatFunc.C) (p.val.map RatFunc.C) _
        (algebraMap (RatFunc k) (AdjoinRoot (p.val.map RatFunc.C)) x)) =
      RatFunc.translationHom (algebraMap k (AdjoinRoot p.val) a)
        ((AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1)
          (algebraMap (RatFunc k) (AdjoinRoot (p.val.map RatFunc.C)) x))
    rw [adjoinRootMap_algebraMap, AdjoinRoot.rationalCoefficientAlgEquiv_algebraMap,
      AdjoinRoot.rationalCoefficientAlgEquiv_algebraMap]
    exact fractionMap_translation _ a x
  · change (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1)
      (adjoinRootMap (RatFunc.translationHom a) (p.val.map RatFunc.C) (p.val.map RatFunc.C) _
        (AdjoinRoot.root (p.val.map RatFunc.C))) =
      RatFunc.translationHom (algebraMap k (AdjoinRoot p.val) a)
        ((AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1)
          (AdjoinRoot.root (p.val.map RatFunc.C)))
    rw [adjoinRootMap_root, AdjoinRoot.rationalCoefficientAlgEquiv_root,
      RatFunc.translationHom_C]

/-- The inverse root identification preserves the same literal translation square. -/
theorem rationalCoefficientAlgEquiv_symm_comp_translation (a : k) :
    (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm.toRingHom.comp
      (RatFunc.translationHom (algebraMap k (AdjoinRoot p.val) a)) =
      (adjoinRootMap (RatFunc.translationHom a) (p.val.map RatFunc.C) (p.val.map RatFunc.C)
        (by rw [polynomial_map_translation_map_C])).comp
        (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm.toRingHom := by
  apply RingHom.ext
  intro x
  apply (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).injective
  change (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1)
    ((AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm
      (RatFunc.translationHom (algebraMap k (AdjoinRoot p.val) a) x)) = _
  rw [AlgEquiv.apply_symm_apply]
  have h := RingHom.congr_fun (rationalCoefficientAlgEquiv_comp_translation p a)
    ((AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm x)
  change (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1)
    (adjoinRootMap (RatFunc.translationHom a) (p.val.map RatFunc.C) (p.val.map RatFunc.C) _
      ((AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm x)) =
      RatFunc.translationHom (algebraMap k (AdjoinRoot p.val) a)
        ((AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1)
          ((AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm x)) at h
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

/-- The actual rational-function norm commutes with translation, without any
normality, degree or norm-tower assumption. -/
theorem rationalFunctionNorm_translation [CharZero k] (a : k) (n : ℕ)
    (x : K (RatFunc (AdjoinRoot p.val)) n) :
    map n (RatFunc.translationHom a) (rationalFunctionNorm n p x) =
      rationalFunctionNorm n p
        (map n (RatFunc.translationHom (algebraMap k (AdjoinRoot p.val) a)) x) := by
  unfold rationalFunctionNorm
  simp only [LinearMap.comp_apply]
  rw [polynomialNorm_restrict_irreducible (RatFunc.translationHom a) n
    (rationalCoefficientPolynomial p) (rationalCoefficientPolynomial p)
    (polynomial_map_translation_map_C a p.val).symm]
  apply congrArg (polynomialNorm n (rationalCoefficientPolynomial p))
  have h := congrArg (map n) (rationalCoefficientAlgEquiv_symm_comp_translation p a)
  unfold rationalCoefficientPolynomial at h ⊢
  rw [map_comp, map_comp] at h
  exact (LinearMap.congr_fun h x).symm

local instance (a : k) : Fact (Irreducible (X - C a)) := ⟨irreducible_X_sub_C a⟩
local instance (a : AdjoinRoot p.val) : Fact (Irreducible (X - C a)) :=
  ⟨irreducible_X_sub_C a⟩

/-- The prime-normal rational norm commutes with the original residue at
every linear place, retaining both literal evaluation identifications. -/
theorem residueAt_linear_rationalFunctionNorm_prime [CharZero k]
    [Normal k (AdjoinRoot p.val)] (hp : p.val.natDegree.Prime) (a : k) (n : ℕ)
    (x : K (RatFunc (AdjoinRoot p.val)) (n + 1)) :
    map n (linearRootEquiv a).toRingHom
      (residueAt (X - C a) n (rationalFunctionNorm (n + 1) p x)) =
      polynomialNorm n p
        (map n (linearRootEquiv (algebraMap k (AdjoinRoot p.val) a)).toRingHom
          (residueAt (X - C (algebraMap k (AdjoinRoot p.val) a)) n x)) := by
  rw [residueAt_linear_eq_residueAt_X_translation a, rationalFunctionNorm_translation,
    residueAt_X_rationalFunctionNorm_prime p hp,
    ← residueAt_linear_eq_residueAt_X_translation]

end MilnorK.PolynomialNorm
