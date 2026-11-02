/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Points.FieldExtensionBoundary
public import Aglib.AlgebraicGeometry.Curves.PointDivisor.BaseChange
public import Aglib.AlgebraicGeometry.Curves.Picard.OpenBoundary
public import Mathlib.Data.Finsupp.Ext

/-! # Original rational boundary divisors under field extension

Divisors are the existing finitely supported integer functions on closed
points. Extension uses native `Finsupp.mapDomain` along the actual rational
closed-point embedding, and recovery uses native `comapDomain`. The Picard
square is proved on singleton generators from the original point-ideal
pullback. No enumeration or replacement boundary-divisor group is used.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local
open AlgebraicGeometry.Scheme.OverField.Curve.Picard

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Divisors

variable {k K : Type u} [Field k] [IsAlgClosed k] [Field K]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
  (q : Spec (.of K) ⟶ Spec (.of k))

/-- Extend the original divisor along the actual rational closed-point map. -/
def fieldExtension : Divisor X →+ Divisor (pullback p q) :=
  Finsupp.mapDomain.addMonoidHom (ClosedPoint.fieldExtensionPoint p q)

/-- Recover the coefficients at the original rational closed points. -/
def fieldRestriction : Divisor (pullback p q) →+ Divisor X :=
  Finsupp.comapDomain.addMonoidHom (ClosedPoint.fieldExtensionPoint_injective p q)

/-- The original coefficient is retained at its actual lifted rational point. -/
@[simp]
theorem fieldExtension_apply_image (D : Divisor X) (x : ClosedPoint X) :
    fieldExtension p q D (ClosedPoint.fieldExtensionPoint p q x) = D x :=
  Finsupp.mapDomain_apply_of_injective (ClosedPoint.fieldExtensionPoint_injective p q) D x

/-- Restriction retains the literal target coefficient. -/
@[simp]
theorem fieldRestriction_apply (D : Divisor (pullback p q)) (x : ClosedPoint X) :
    fieldRestriction p q D x = D (ClosedPoint.fieldExtensionPoint p q x) := rfl

/-- Actual divisor extension is split by restriction to the original points. -/
@[simp]
theorem fieldRestriction_fieldExtension (D : Divisor X) :
    fieldRestriction p q (fieldExtension p q D) = D :=
  Finsupp.comapDomain_mapDomain (ClosedPoint.fieldExtensionPoint p q)
    (ClosedPoint.fieldExtensionPoint_injective p q) D

/-- A divisor with support in the actual closed-point image is recovered
without enumerating its support or choosing inverse image points. -/
theorem fieldExtension_fieldRestriction (D : Divisor (pullback p q))
    (hD : ∀ y ∈ D.support, y ∈ Set.range (ClosedPoint.fieldExtensionPoint p q)) :
    fieldExtension p q (fieldRestriction p q D) = D :=
  Finsupp.mapDomain_comapDomain (ClosedPoint.fieldExtensionPoint p q)
    (ClosedPoint.fieldExtensionPoint_injective p q) D hD

/-- A divisor supported outside the actual base-changed open is recovered
from the original rational points; finite support is already part of Finsupp. -/
theorem fieldExtension_fieldRestriction_of_boundary [IsIntegral X] [IsNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1) (V : X.Opens) [Nonempty V]
    (D : Divisor (pullback p q))
    (hD : ∀ y ∈ D.support, y.val ∉ (pullback.fst p q) ⁻¹ᵁ V) :
    fieldExtension p q (fieldRestriction p q D) = D :=
  fieldExtension_fieldRestriction p q D fun y hy =>
    ClosedPoint.mem_range_fieldExtensionPoint_of_not_mem_preimage p q hdim V y (hD y hy)

section Picard

variable [IsIntegral X] [IsNoetherian X]
  [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
  [IsIntegral (pullback p q)] [IsNoetherian (pullback p q)]
  [∀ y : ClosedPoint (pullback p q),
    IsDiscreteValuationRing ((pullback p q).presheaf.stalk y.val)]
  [SmoothOfRelativeDimension 1 p] [IsSeparated p]
  (hdim : topologicalKrullDim X ≤ 1)
  (hdim' : topologicalKrullDim (show Scheme from pullback p q) ≤ 1)

/-- The original Picard pullback and actual rational divisor extension form
an additive square. Singleton transport supplies the entire finite-sum law. -/
theorem pullbackHom_divisorToPicard :
    (pullbackHom (pullback.fst p q)).comp (DivisorClass.divisorToPicard X hdim) =
      (DivisorClass.divisorToPicard (pullback p q) hdim').comp (fieldExtension p q) := by
  apply Finsupp.addHom_ext'
  intro x
  apply AddMonoidHom.ext_int
  change pullbackClass (pullback.fst p q)
      (DivisorClass.divisorToPicard X hdim (Finsupp.single x 1)) = _
  let : IsIntegral (pullback (ClosedPoint.rationalPoint p x).structureMap q) :=
    inferInstanceAs (IsIntegral (pullback p q))
  let : IsNoetherian (pullback (ClosedPoint.rationalPoint p x).structureMap q) :=
    inferInstanceAs (IsNoetherian (pullback p q))
  let : ∀ y : ClosedPoint (pullback (ClosedPoint.rationalPoint p x).structureMap q),
      IsDiscreteValuationRing
        ((pullback (ClosedPoint.rationalPoint p x).structureMap q).presheaf.stalk y.val) :=
    inferInstanceAs (∀ y : ClosedPoint (pullback p q),
      IsDiscreteValuationRing ((pullback p q).presheaf.stalk y.val))
  let : SmoothOfRelativeDimension 1 (ClosedPoint.rationalPoint p x).structureMap :=
    inferInstanceAs (SmoothOfRelativeDimension 1 p)
  let : IsSeparated (ClosedPoint.rationalPoint p x).structureMap :=
    inferInstanceAs (IsSeparated p)
  have h := PointDivisor.pullbackClass_singleton_fieldExtension
    (ClosedPoint.rationalPoint p x) q hdim hdim'
  have hx : (⟨(ClosedPoint.rationalPoint p x).point,
      (ClosedPoint.rationalPoint p x).point_isClosed⟩ : ClosedPoint X) = x :=
    Subtype.ext (ClosedPoint.rationalPoint_point p x)
  change pullbackClass (pullback.fst p q)
      (DivisorClass.divisorToPicard X hdim
        (Finsupp.single ⟨(ClosedPoint.rationalPoint p x).point,
          (ClosedPoint.rationalPoint p x).point_isClosed⟩ 1)) =
    DivisorClass.divisorToPicard (pullback p q) hdim'
      (Finsupp.single (ClosedPoint.fieldExtensionPoint p q x) 1) at h
  rw [hx] at h
  change _ = DivisorClass.divisorToPicard (pullback p q) hdim'
    (Finsupp.mapDomain (ClosedPoint.fieldExtensionPoint p q) (Finsupp.single x 1))
  rw [Finsupp.mapDomain_single]
  exact h

/-- Value form of the original additive Picard square. -/
theorem pullbackClass_divisor_fieldExtension (D : Divisor X) :
    pullbackClass (pullback.fst p q) (DivisorClass.divisorToPicard X hdim D) =
      DivisorClass.divisorToPicard (pullback p q) hdim' (fieldExtension p q D) :=
  DFunLike.congr_fun (pullbackHom_divisorToPicard p q hdim hdim') D

end Picard

end AlgebraicGeometry.Scheme.OverField.Curve.Divisors
