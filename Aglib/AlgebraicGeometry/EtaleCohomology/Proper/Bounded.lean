/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Universal.ProjectiveLine
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Universal.TargetLocality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Universal.AffineReduction

/-! # Original proper base change for bounded torsion coefficients

Universal native P1 exchange and the existing proper affine reduction give
the actual bounded property over every spectrum. Original target locality
extends this to arbitrary schemes, and the existing model transport retains
the four independently supplied derived-category universes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u dX dS dX' dS'

attribute [local instance] hasSheafifyLarge

/-- Every proper morphism satisfies original bounded base change over its
arbitrary target, at every positive annihilating modulus. -/
theorem boundedBaseChange_proper (n : ℕ) (hn : n ≠ 0)
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] : boundedBaseChange n f := by
  refine boundedBaseChange_proper_of_affineTargets n ?_ f
  intro R _ Y p _
  exact (boundedBaseChange n).universally_le p
    (universallyBoundedBaseChange_proper_affine_of_projectiveLine n R
      (universallyBoundedBaseChange_projectiveLine n hn R) p)

variable {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) [IsProper f] (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (H : IsPullback g' f' f g)

/-- The defined proper higher exchange is invertible on every coefficient
killed by a positive integer, in each of the original independent models. -/
theorem properHigherBaseChange_isIso_of_killed
    (n : ℕ) (hn : n ≠ 0) (F : AbelianSheaf.{u, u + 1} X)
    (hF : n • 𝟙 F = 0) (q : ℕ) :
    IsIso ((higherBaseChangeMap f f' g g' H.w.symm q).app F) :=
  higherBaseChangeMap_isIso_of_boundedExchange f f' g g' H.w.symm n
    ((boundedBaseChange_proper n hn f) f' g g' H) F hF q

/-- The same actual proper derived exchange is invertible on the original
degree-zero single of a bounded-torsion coefficient. -/
theorem properDerivedBaseChange_single_isIso_of_killed
    (n : ℕ) (hn : n ≠ 0) (F : AbelianSheaf.{u, u + 1} X)
    (hF : n • 𝟙 F = 0) :
    IsIso ((derivedBaseChangeMap f f' g g' H.w.symm).app
      ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)) :=
  (Reduction.derivedBaseChangeMap_single_isIso_iff_higher f f' g g' H.w.symm F).mpr
    (properHigherBaseChange_isIso_of_killed f f' g g' H n hn F hF)

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
