/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.CategoryTheory.Whiskering
public import Aglib.CategoryTheory.NatTrans.TargetComparisonTransport

/-! # Restrict the original whole target equation without expanding its components -/
@[expose] public section
namespace CategoryTheory
variable {V U A : Type*} [Category* V] [Category* U] [Category* A]
  {F G H : U ⥤ A}

/-- Original target equations persist under restriction of the source functor. -/
theorem targetComparison_whiskerLeft (i : V ⥤ U)
    (a : F ⟶ G) (b : G ⟶ H) (c : F ⟶ H)
    (h : TargetComparisonEquation a b c) :
    TargetComparisonEquation (Functor.whiskerLeft i a) (Functor.whiskerLeft i b)
      (Functor.whiskerLeft i c) := by
  simpa only [TargetComparisonEquation, Functor.whiskerLeft_comp] using
    congrArg (Functor.whiskerLeft i) h

section ThreeIsomorphisms
variable {C : Type*} [Category* C] {X Y Z W T : C}

/-- Preserve the prescribed right-associated three-iso normalization formula. -/
theorem targetComparison_iso_trans_three (a : X ≅ Y) (d : Y ≅ Z) (n : Z ≅ W)
    (bX : X ⟶ T) (bZ : Z ⟶ T) (bW : W ⟶ T)
    (ha : TargetComparisonEquation (a ≪≫ d).hom bZ bX)
    (hn : TargetComparisonEquation n.hom bW bZ) :
    TargetComparisonEquation (a ≪≫ d ≪≫ n).hom bW bX := by
  simpa only [Iso.trans_assoc] using targetComparison_iso_trans (a ≪≫ d) n bX bZ bW ha hn
end ThreeIsomorphisms
end CategoryTheory
