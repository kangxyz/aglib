/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.CyclicSection
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.DegreeZeroPullback

/-! # Original cyclic-section generator under a sheaf pullback

This uses the existing constant adjunction and cyclic value law. No cohomology,
higher direct image, roots coefficient or curve model enters the proof.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge

/-- Transport of the original cyclic generator for arbitrary original sheaves. -/
theorem cyclicSectionMap_pullback_adjoint_one
    {S T : Scheme.{u}} (t : T ⟶ S)
    (F : AbelianSheaf.{u, u + 1} S) (G : AbelianSheaf.{u, u + 1} T)
    (a : (inverseImage t).obj F ⟶ G)
    (n : ℕ) (r : (globalSections S).obj F) (hr : n • r = 0) :
    (constantAdjunction T).homEquiv _ _
      (((inverseImageConstantIso t).app (ConstantFinite.value (ULift.{u} (ZMod n)))).inv ≫
        (inverseImage t).map (cyclicSectionMap F n r hr) ≫ a)
      (ULift.up (ULift.up (1 : ZMod n))) =
    (globalSections T).map a (globalSectionsPullback t F r) := by
  rw [← Category.assoc, (constantAdjunction _).homEquiv_naturality_right,
    constantTransport_homEquiv, cyclicSectionMap_adjoint]
  change (globalSections T).map a
    (globalSectionsPullback t F
      (cyclicSectionValues F n r hr (ULift.up (ULift.up (1 : ZMod n))))) = _
  rw [cyclicSectionValues_one]

end AlgebraicGeometry.Scheme.EtaleCohomology
