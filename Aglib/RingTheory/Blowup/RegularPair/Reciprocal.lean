/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Blowup.RegularPair

/-!
# Reciprocal coordinates in the actual regular-pair chart rings

The opposite polynomial quotient maps into the localization of the first
quotient at its original coordinate. The opposite coordinate is the literal
inverse, and the original coefficient maps commute. The saturated fibre-ring
comparison also keeps the same original coordinate after reduction.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace Localization.Away

open Polynomial
variable {A : Type u} [CommRing A] (a b : A)

/-- The opposite defining relation holds at the original reciprocal coordinate. -/
theorem pairReciprocal_relation :
    (pairPolynomial b a).eval₂
      (Algebra.ofId A (Localization.Away (pairCoordinate a b))).toRingHom
      (IsLocalization.Away.invSelf (pairCoordinate a b)) = 0 := by
  let Q := pairQuotient a b
  let L := Localization.Away (pairCoordinate a b)
  change (C b * X - C a).eval₂ (algebraMap A L)
    (IsLocalization.Away.invSelf (pairCoordinate a b)) = 0
  simp only [eval₂_sub, eval₂_mul, eval₂_C, eval₂_X]
  have h : algebraMap A L b =
      algebraMap A L a * algebraMap Q L (pairCoordinate a b) := by
    rw [IsScalarTower.algebraMap_apply A Q L b,
      ← pairCoordinate_relation a b, map_mul, ← IsScalarTower.algebraMap_apply A Q L a]
  rw [h, mul_assoc, IsLocalization.Away.mul_invSelf, mul_one, sub_self]

/-- The original opposite polynomial chart maps to the localization at the first coordinate,
with the opposite coordinate sent to its actual inverse. -/
def pairReciprocal : pairQuotient b a →ₐ[A] Localization.Away (pairCoordinate a b) :=
  AdjoinRoot.liftAlgHom (pairPolynomial b a)
    (Algebra.ofId A (Localization.Away (pairCoordinate a b)))
    (IsLocalization.Away.invSelf (pairCoordinate a b)) (pairReciprocal_relation a b)

@[simp]
theorem pairReciprocal_coordinate :
    pairReciprocal a b (pairCoordinate b a) =
      IsLocalization.Away.invSelf (pairCoordinate a b) :=
  AdjoinRoot.liftAlgHom_root (pairPolynomial b a)
    (Algebra.ofId A (Localization.Away (pairCoordinate a b)))
    (IsLocalization.Away.invSelf (pairCoordinate a b)) (pairReciprocal_relation a b)

/-- The actual residue ring comparison sends the class of the original coordinate to `X`. -/
theorem pairChartFibreEquiv_coordinate
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b) :
    pairChartFibreEquiv a b ha hb
      (Ideal.Quotient.mk _ (pairChartEquiv a b ha hb (pairCoordinate a b))) = X := by
  let e := Ideal.quotientEquivAlg _ _ (pairChartEquiv a b ha hb)
    (pairChartEquiv_mapIdeal a b ha hb)
  have h := Ideal.quotientEquivAlg_mk
    (I := (Ideal.span {a, b}).map (algebraMap A (pairQuotient a b)))
    ((Ideal.span {a, b}).map (algebraMap A (saturatedChart A (Ideal.span {a, b}) a)))
    (pairChartEquiv a b ha hb)
    (pairChartEquiv_mapIdeal a b ha hb) (pairCoordinate a b)
  change e (Ideal.Quotient.mk _ (pairCoordinate a b)) =
    Ideal.Quotient.mk _ (pairChartEquiv a b ha hb (pairCoordinate a b)) at h
  change pairFibreEquiv a b
    (e.symm (Ideal.Quotient.mk _ (pairChartEquiv a b ha hb (pairCoordinate a b)))) = X
  rw [← h, AlgEquiv.symm_apply_apply]
  simpa only [AdjoinRoot.algebraMap_eq] using pairFibreEquiv_coordinate a b

end Localization.Away
