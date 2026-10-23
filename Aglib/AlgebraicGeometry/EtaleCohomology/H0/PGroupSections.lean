/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupTheory.PGroup.FiniteImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.InvariantSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.MarkedComparisonTransport

/-! # Nonzero original sections from p-group coefficient monodromy

The p-group hypothesis concerns the image of the actual intrinsic point
permutation action, not the absolute or fibre-automorphism group. Native
fixed-point counting and finite-etale fullness produce an original section
whose geometric value is explicitly nonzero.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
open Scheme.FiniteEtale Scheme.EtaleFundamentalGroups
open Scheme.FiniteEtale.FiberTorsorActions

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open MarkedCoefficients MarkedComparisonTransport

universe u

attribute [local instance] Over.cartesianMonoidalCategory

/-- Actual p-group monodromy produces an original represented global section
with a nonzero geometric value and its literal evaluation equation. -/
theorem exists_represented_section_of_isPGroup_image
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ X)
    [GaloisCategory (Scheme.FiniteEtale X)]
    [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
    (H : Grp (Over X)) [IsCommMonObj H.X] [IsFinite H.X.hom] [Etale H.X.hom]
    {p : ℕ} [Fact p.Prime] [Nontrivial (PointModule s H)]
    (hp : ∀ a : PointModule s H, p • a = 0)
    (himage : letI := pointEvaluationAction s H
      IsPGroup p (MulAction.toPermHom (FiberAutGroup s) (PointModule s H)).range) :
    ∃ a : PointModule s H, a ≠ 0 ∧
      ∃ r : (representedSheaf H).obj.obj (op (Scheme.Etale.mk (𝟙 X))),
        (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 X)) ≫ r.down.toMul =
          a.toMul := by
  let := pointEvaluationAction s H
  obtain ⟨a, ha, hfix⟩ :=
    MonoidHom.exists_ne_zero_fixedPoint_of_isPGroup_range
      (MulAction.toPermHom (FiberAutGroup s) (PointModule s H)) himage
      (fun g => smul_zero g) hp
  obtain ⟨r, hr⟩ := exists_represented_globalSection_of_fixed_point s H a.toMul
    (fun g => congrArg Additive.toMul (hfix g))
  exact ⟨a, ha, r, hr⟩

end AlgebraicGeometry.Scheme.EtaleCohomology
