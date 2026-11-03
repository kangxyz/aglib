/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve.AnticanonicalHilbert.ScalarExtension
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Anticanonical Hilbert numerics over an arbitrary field

The proved variable-field scalar-extension theorem is specialized to an
algebraic closure. The actual inverse-line cohomology remains over the
original field; no canonical-module gluing over the closure is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Hom

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- Over an arbitrary original field, actual inverse-line cohomology gives
the entire very-ample Hilbert function. Algebraic closure is used only inside
the proof to choose a regular Cartier divisor, not as a hypothesis on k. -/
theorem cmCurve_hyperplanePower_h0_finrank
    (k : Type u) [Field k] (ι : Type u) [Finite ι]
    {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (hCM : ∀ x : C, IsClosed ({x} : Set C) →
      ∃ b ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk x),
        IsSMulRegular (C.presheaf.stalk x) b ∧
          (Ideal.span {b}).radical = IsLocalRing.maximalIdeal (C.presheaf.stalk x))
    [Subsingleton (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (SheafOfModules.unit C.ringCatSheaf) 1)]
    [Subsingleton (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (dualLineBundle C (curveHyperplaneLine k ι j)).val 0)]
    (hO : Module.finrank k (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (SheafOfModules.unit C.ringCatSheaf) 0) = 1)
    (hJ : Module.finrank k (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (dualLineBundle C (curveHyperplaneLine k ι j)).val 1) = 1) (r : ℕ) :
    Module.finrank k (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (tensorPowerLineBundle C (curveHyperplaneLine k ι j) r).val 0) = 2 * r + 1 :=
  cmCurve_hyperplanePower_h0_finrank_of_algebraic_extension
    k (AlgebraicClosure k) ι j hCM hO hJ r

/-- Three actual first-power sections give every power dimension over
the original arbitrary field. The finite Cartier divisor is chosen only after
algebraic closure, using ordinary line-power base change. -/
theorem cmCurve_hyperplanePower_h0_finrank_of_firstPower
    (k : Type u) [Field k] (ι : Type u) [Finite ι]
    {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (hCM : ∀ x : C, IsClosed ({x} : Set C) →
      ∃ b ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk x),
        IsSMulRegular (C.presheaf.stalk x) b ∧
          (Ideal.span {b}).radical = IsLocalRing.maximalIdeal (C.presheaf.stalk x))
    [Subsingleton (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (SheafOfModules.unit C.ringCatSheaf) 1)]
    (hO : Module.finrank k (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (SheafOfModules.unit C.ringCatSheaf) 0) = 1)
    (hL : Module.finrank k (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (curveHyperplaneLine k ι j).val 0) = 3) (r : ℕ) :
    Module.finrank k (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (tensorPowerLineBundle C (curveHyperplaneLine k ι j) r).val 0) = 2 * r + 1 :=
  cmCurve_hyperplanePower_h0_finrank_of_firstPower_of_algebraic_extension
    k (AlgebraicClosure k) ι j hCM hO hL r


end AlgebraicGeometry.Scheme.Cohomology
