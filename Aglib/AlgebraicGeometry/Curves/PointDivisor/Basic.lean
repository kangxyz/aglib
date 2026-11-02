/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Core
public import Aglib.AlgebraicGeometry.Curves.PointDivisor.IdealClass
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.GraphLineBundle
public import Aglib.AlgebraicGeometry.Geometrically.Integral.SmoothCurve
public import Aglib.AlgebraicGeometry.Stalk.OpenSmoothCurveDVR

/-! # Original point ideals and point divisors

These are the unchanged constructors formerly in Sections and PoleFunctions.
They do not use canonical degree, duality or global pole-section dimensions.
The original point ideal, its dual, rational section and divisor are retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors
open AlgebraicGeometry.Scheme.OverField.Curve.Picard

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.PointDivisor

variable {k : Type u} [Field k]

/-- The actual kernel ideal of the original rational point, with its proved
Cartier rank-one property. -/
def idealLineBundle (X : FScheme k) (hX : Properties X)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) : LineBundle X.left := by
  let := hX.smooth
  let := hX.proper
  exact ⟨Scheme.Hom.idealModule p,
    Scheme.Hom.sectionIdeal_isLocallyRankOne Scheme.Hom.smoothRelativeDivisorIdeal X.hom p hp⟩

/-- The original positive point module O(p), namely the actual dual ideal. -/
def positiveLineBundle (X : FScheme k) (hX : Properties X)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) : LineBundle X.left :=
  dualLineBundle X.left (idealLineBundle X hX p hp)

/-- The native rational point with exactly the original two morphisms. -/
def rationalPoint (X : FScheme k) (p : Spec (.of k) ⟶ X.left)
    (hp : p ≫ X.hom = 𝟙 _) : Scheme.RationalPoint k X.left := ⟨X.hom, p, hp⟩

@[simp] theorem rationalPoint_structureMap (X : FScheme k)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) :
    (rationalPoint X p hp).structureMap = X.hom := rfl

@[simp] theorem rationalPoint_sectionMap (X : FScheme k)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) :
    (rationalPoint X p hp).sectionMap = p := rfl

/-- The original closed point selected by the original rational section. -/
def closedPoint (X : FScheme k) (p : Spec (.of k) ⟶ X.left)
    (hp : p ≫ X.hom = 𝟙 _) : Scheme.ClosedPoint X.left :=
  ⟨(rationalPoint X p hp).point, (rationalPoint X p hp).point_isClosed⟩

@[simp] theorem closedPoint_val (X : FScheme k) (p : Spec (.of k) ⟶ X.left)
    (hp : p ≫ X.hom = 𝟙 _) :
    (closedPoint X p hp).val = p (IsLocalRing.closedPoint k) := rfl

/-- The existing closed-point divisor with its original multiplicity. -/
def pointDivisor (X : FScheme k) (p : Spec (.of k) ⟶ X.left)
    (hp : p ≫ X.hom = 𝟙 _) (n : ℤ) : Divisor X.left := Finsupp.single (closedPoint X p hp) n

theorem pointDivisor_nsmul (X : FScheme k) (p : Spec (.of k) ⟶ X.left)
    (hp : p ≫ X.hom = 𝟙 _) (n : ℕ) :
    n • pointDivisor X p hp 1 = pointDivisor X p hp n := by
  classical
  simp only [pointDivisor, Finsupp.smul_single, nsmul_eq_mul, mul_one]

theorem pointDivisor_one_add (X : FScheme k) (p : Spec (.of k) ⟶ X.left)
    (hp : p ≫ X.hom = 𝟙 _) (n : ℕ) :
    pointDivisor X p hp 1 + pointDivisor X p hp n = pointDivisor X p hp ((n + 1 : ℕ) : ℤ) := by
  classical
  simp only [pointDivisor, ← Finsupp.single_add]
  congr 1
  omega

theorem pointDivisor_nonneg (X : FScheme k) (p : Spec (.of k) ⟶ X.left)
    (hp : p ≫ X.hom = 𝟙 _) (n : ℕ) : ∀ x, 0 ≤ pointDivisor X p hp n x := by
  classical
  intro x
  by_cases hx : x = closedPoint X p hp
  · simpa only [pointDivisor, hx, Finsupp.single_eq_same] using Int.natCast_nonneg n
  · simp only [pointDivisor, Finsupp.single_eq_of_ne hx, le_refl]

/-- The native integral structure follows from the given smooth connected curve. -/
theorem isIntegral_of_properties (X : FScheme k) (hX : Properties X) : IsIntegral X.left := by
  let := hX.smooth
  let := hX.connected
  let : GeometricallyIntegral X.hom :=
    Scheme.geometricallyIntegral_of_smoothOfRelativeDimension_one_of_geometricallyConnected X.hom
  exact GeometricallyIntegral.isIntegral_of_subsingleton X.hom

/-- Every actual closed-point stalk of the given smooth curve is a DVR. -/
theorem isDiscreteValuationRing_stalk (X : FScheme k) (hX : Properties X) [IsIntegral X.left]
    (x : Scheme.ClosedPoint X.left) :
    IsDiscreteValuationRing (X.left.presheaf.stalk x.val) := by
  have h : SmoothOfRelativeDimension 1 (𝟙 X.left ≫ X.hom) := by
    simpa only [Category.id_comp] using hX.smooth
  let := h
  exact Scheme.smoothChart_closedPoint_dvr (𝟙 X.left) X.hom x.val x.property

end AlgebraicGeometry.Scheme.OverField.Curve.PointDivisor
