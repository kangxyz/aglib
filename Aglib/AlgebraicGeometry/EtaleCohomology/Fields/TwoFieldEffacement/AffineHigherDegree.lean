/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.FiniteNormalCompactification
public import Aglib.AlgebraicGeometry.Curves.AffineCompactificationBoundary
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.FiniteConstantOpenVanishing
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.AlgebraicExtension.FiniteConstantDescent
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Higher finite-constant classes on the original smooth affine curve

Only the algebraic-closure base change is compactified. Its entire original
open has a closed boundary point, so the existing ordinary open-curve vanishing
applies. Actual finite-stage zero descent returns to the unchanged source and
class. No smooth compactification over an imperfect source field is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement

universe u w

attribute [local instance] hasSheafifyLarge HasExt.standard

/-- Whole-affine ordinary finite-constant vanishing, retaining the original Ext
world. The original coefficient has a positive invertible annihilator. -/
theorem affine_finiteConstant_subsingleton_H
    (k : Type u) [Field k] [IsAlgClosed k]
    (U : Scheme.{u}) [IsAffine U] [Nonempty U]
    (p : U ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} U)]
    (A : Type u) [AddCommGroup A] [Finite A]
    (n : ℕ) (hn : 0 < n) (hkill : ∀ a : A, n • a = 0)
    (hunit : IsUnit (n : k)) (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H.{w} (ConstantFinite.coefficient A U) q) := by
  obtain ⟨X, hX, j, hj, hfac⟩ := exists_whole_affine_curve_compactification k U p
  let : IsOpenImmersion j := hj
  let : IsProper X.hom := hX.proper
  have hx := exists_closedPoint_outside_affine_curve_compactification k p X.hom j hfac
    (smoothFieldDimension k U p 1 inferInstance inferInstance)
  exact Curves.finiteConstant_subsingleton_H_of_isOpenImmersion hX j hx
    A n hn hkill hunit q hq

/-- Over an arbitrary field, an original higher finite-constant class on the
whole smooth affine curve vanishes at an actual finite algebraic field stage.
The standard Ext realization is the one used by the finite-stage consumer. -/
theorem exists_affine_finiteField_killing_higher_constant
    (k : Type u) [Field k] (U : Scheme.{u}) [IsAffine U] [Nonempty U]
    (p : U ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p]
    (A : Type u) [AddCommGroup A] [Finite A]
    (n : ℕ) (hn : 0 < n) (hkill : ∀ a : A, n • a = 0)
    (hunit : IsUnit (n : k)) (q : ℕ) (hq : 2 ≤ q)
    (c : Sheaf.H.{u + 2} (ConstantFinite.coefficient A U) q) :
    ∃ s : Finset (AlgebraicClosure k),
      Curves.constantRestriction.{u, u + 2, u + 2} A
        ((FiniteEtale.FieldLimit.schemeDiagram k (AlgebraicClosure k) p).obj
          (op s)).hom q c = 0 := by
  let Ω := AlgebraicClosure k
  let b := Spec.algebraMap k Ω
  let : SmoothOfRelativeDimension 1 (pullback.snd p b) :=
    (@MorphismProperty.IsStableUnderBaseChange.of_isPullback
      Scheme.{u} _ (@SmoothOfRelativeDimension 1)
      (smoothOfRelativeDimension_isStableUnderBaseChange 1))
      (IsPullback.of_hasPullback p b) inferInstance
  have hunitΩ : IsUnit (n : Ω) := by
    simpa only [map_natCast] using hunit.map (algebraMap k Ω)
  have hzero := affine_finiteConstant_subsingleton_H.{u, u + 2}
    Ω (pullback p b) (pullback.snd p b) A n hn hkill hunitΩ q hq
  have hc : Curves.constantRestriction.{u, u + 2, u + 2} A
      (pullback.fst p b) q c = 0 := hzero.elim _ _
  exact ConstantFinite.AlgebraicExtension.exists_finiteField_constantRestriction_eq_zero
    k Ω p A q c hc

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
