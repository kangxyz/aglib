/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.ConstantRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.CohomologyTransfers
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackCohomologySystem

/-! # Original all-degree constant restriction in commuting triangles -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite

universe u e

attribute [local instance] hasSheafifyLarge

variable (A : Type u) [AddCommGroup A]

/-- Normalizing the complete fixed-system transfer gives the literal original
constant restriction, in every degree. -/
theorem constantRestriction_triangleTransfer {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ X) (a : T ⟶ S) (h : a ≫ f = g)
    [HasExt.{e} (AbelianSheaf.{u, u + 1} S)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} T)] (q : ℕ)
    (c : Sheaf.H.{e} ((inverseImage f).obj (coefficient A X)) q) :
    Sheaf.H.map ((inverseImageConstantIso g).app (value A)).hom q
      (Continuity.cohomologyTransfer a
        ((pullbackTriangleIso g f a h).inv.app (coefficient A X)) q c) =
      Curves.constantRestriction A a q
        (Sheaf.H.map ((inverseImageConstantIso f).app (value A)).hom q c) := by
  rw [Continuity.cohomologyTransfer_eq_extCoefficientTransfer]
  subst g
  let P := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let M := value A
  have hmap := Functor.constantExtRestriction_triangleTransfer
    (constantAdjunction X) (inverseImageAdjunction f) (inverseImageAdjunction a)
    (constantAdjunction S) (inverseImageAdjunction (a ≫ f)) (constantAdjunction T)
    (directImageGlobalSectionsIso f) (directImageCompIso f a)
    (directImageGlobalSectionsIso (a ≫ f)) (directImageGlobalSectionsIso a)
    (directImageGlobalSectionsIso_comp f a) P M q
  have hvalue := congrArg (fun k => k c) hmap
  change Sheaf.H.map ((inverseImageConstantCanonicalIso (a ≫ f)).app M).hom q
      ((inverseImage a).extCoefficientTransfer
        (((inverseImageConstantCanonicalIso a).app P).inv)
        ((inverseImageComp f a).inv.app (coefficient A X)) q c) =
    (inverseImage a).constantExtRestriction (inverseImageConstantCanonicalIso a) P M q
      (Sheaf.H.map ((inverseImageConstantCanonicalIso f).app M).hom q c) at hvalue
  simp only [inverseImageConstantCanonicalIso_eq] at hvalue
  simp only [pullbackTriangleIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl,
    Category.comp_id, Curves.constantRestriction] at hvalue ⊢
  exact hvalue

end AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite
