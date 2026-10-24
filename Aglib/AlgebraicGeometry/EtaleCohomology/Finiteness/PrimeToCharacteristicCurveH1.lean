/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.KummerCurveH1
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.HenselianConstant

/-! # Positive invertible cyclic H1 on smooth proper geometric curves

A rational point is obtained from a closed point over the algebraically closed
ground field. The actual strictly-henselian constant/root coefficient
isomorphism then transfers finite original Kummer H1 to the literal lifted
cyclic constant coefficient. No characteristic-zero premise is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve
open GroupCohomology.Kummer.Coefficients

universe u w
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finiteness

attribute [local instance] hasSheafifyLarge

/-- No chosen origin is required for finite original roots H1 on an actual
smooth proper geometrically connected curve over an algebraically closed field. -/
theorem finite_roots_h1_of_smooth_proper_curve {k : Type u} [Field k] [IsAlgClosed k]
    (X : FScheme k) (hX : Properties X) (n : ℕ) (hn : 0 < n)
    (hunit : IsUnit (n : k)) [HasExt.{w} (AbelianSheaf.{u, u + 1} X.left)] :
    Finite (H1Etale.{u, u + 1, w} X.left (mu X.left n)) := by
  let := hX.smooth
  let := hX.proper
  let := hX.isIntegral
  let : LocallyOfFiniteType X.hom := inferInstance
  let : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨x, _, hx⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set X.left).Nonempty) isOpen_univ.isLocallyClosed
  exact KummerFamilyValues.finite_roots_h1_of_curve X (pointOfClosedPoint X.hom x hx)
    (pointOfClosedPoint_comp X.hom x hx) hX n hn hunit

/-- The literal positive invertible cyclic constant coefficient has finite
original H1, in any original Ext universe, over the algebraically closed field. -/
theorem finite_cyclic_h1_of_smooth_proper_curve {k : Type u} [Field k] [IsAlgClosed k]
    (X : FScheme k) (hX : Properties X) (n : ℕ) (hn : 0 < n)
    (hunit : IsUnit (n : k)) [HasExt.{w} (AbelianSheaf.{u, u + 1} X.left)] :
    Finite (H1Etale.{u, u + 1, w} X.left
      (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X.left)) := by
  let : Finite (H1Etale.{u, u + 1, w} X.left (mu X.left n)) :=
    finite_roots_h1_of_smooth_proper_curve X hX n hn hunit
  have hinv : IsUnit (n : Γ(Spec (.of k), ⊤)) := by
    simpa only [map_natCast] using hunit.map (Scheme.ΓSpecIso (.of k)).inv.hom
  let : IsSepClosed (IsLocalRing.ResidueField k) :=
    Algebra.IsAlgebraic.isSepClosed (F := k) (E := IsLocalRing.ResidueField k)
  let e := coefficientIso (Kummer.HenselianConstant.constantRootIsoOver k n hn hinv X.hom)
  exact Finite.of_injective e e.injective

end AlgebraicGeometry.Scheme.EtaleCohomology.Finiteness
