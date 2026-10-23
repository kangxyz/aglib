/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.ProperHenselian
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ConstantFinite.ProperHenselian
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.ConstantRestriction
public import Aglib.AlgebraicGeometry.Curves.ProjectiveLine.Charts

/-! # Original proper-henselian comparison in degrees zero and one -/

@[expose] public noncomputable section

universe u w w'

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

attribute [local instance] hasSheafifyLarge

variable (A : Type u) [AddCommGroup A]
  {X S : Scheme.{u}} (f : S ⟶ X)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- The all-degree map retains the existing original degree-zero restriction. -/
@[simp]
theorem constantRestriction_zero :
    constantRestriction A f 0 = ConstantFinite.pullbackH0 A f := rfl

/-- The all-degree map retains the existing original degree-one restriction. -/
@[simp]
theorem constantRestriction_one :
    constantRestriction A f 1 = ConstantFinite.pullbackH1 A f := rfl

section ProperHenselian

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
  {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R)) [IsProper p]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} Y)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1}
    (pullback p (LocalRing.residueSpecMap R)))]
  [Finite A]

/-- Existing proper-henselian H0 and H1 bijections apply to the literal all-degree map. -/
theorem properHenselian_constantRestriction_bijective_of_le_one
    (q : ℕ) (hq : q ≤ 1) :
    Function.Bijective
      (constantRestriction A (pullback.fst p (LocalRing.residueSpecMap R)) q) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq with rfl | rfl
  · exact ConstantFinite.properHenselian_pullbackH0_bijective p A
  · exact ConstantFinite.properHenselian_pullbackH1_bijective p A

end ProperHenselian

section FiniteProjectiveLine

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
  {Y : Scheme.{u}} (p : Y ⟶ Scheme.ProjectiveLine.projectiveP1 R) [IsFinite p]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} Y)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1}
    (pullback (p ≫ Scheme.ProjectiveLine.structureMap R)
      (LocalRing.residueSpecMap R)))]
  [Finite A]

/-- The low-degree part of the finite-over-projective-line comparison is already bijective. -/
theorem finite_projectiveLine_constantRestriction_bijective_of_le_one
    (q : ℕ) (hq : q ≤ 1) :
    Function.Bijective (constantRestriction A
      (pullback.fst (p ≫ Scheme.ProjectiveLine.structureMap R)
        (LocalRing.residueSpecMap R)) q) := by
  let : IsProper (p ≫ Scheme.ProjectiveLine.structureMap R) := inferInstance
  exact properHenselian_constantRestriction_bijective_of_le_one A
    (p ≫ Scheme.ProjectiveLine.structureMap R) q hq

end FiniteProjectiveLine

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
