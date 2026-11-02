/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ConstantFinite.Coefficient
public import Aglib.AlgebraicGeometry.EtaleCohomology.Pullback
public import Aglib.CategoryTheory.Sites.ConstantRestriction.Cohomology

/-!
# Original constant-coefficient restriction for the curve comparison

The all-degree map is the native cohomology pullback followed by the native
constant-coefficient transport. The low-degree proper-henselian results are
kept in the separate LowDegree leaf, not imported by coefficient-only consumers.
-/

@[expose] public noncomputable section

universe u w w'

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

attribute [local instance] hasSheafifyLarge

variable (A : Type u) [AddCommGroup A]
  {X S : Scheme.{u}} (f : S ⟶ X)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- The original all-degree pullback with its canonical constant-coefficient transport. -/
def constantRestriction (q : ℕ) :
    Sheaf.H.{w} (ConstantFinite.coefficient A X) q →+
      Sheaf.H.{w'} (ConstantFinite.coefficient A S) q :=
  (inverseImage f).constantExtRestriction (inverseImageConstantIso f)
    (AddCommGrpCat.of (ULift.{u + 1} ℤ)) (ConstantFinite.value A) q

/-- The lower construction retains exactly the original pullback and coefficient map. -/
theorem constantRestriction_apply (q : ℕ)
    (c : Sheaf.H.{w} (ConstantFinite.coefficient A X) q) :
    constantRestriction A f q c =
      Sheaf.H.map ((inverseImageConstantIso f).app (ConstantFinite.value A)).hom q
        (cohomologyPullback f (ConstantFinite.coefficient A X) q c) := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe w''

attribute [local instance] hasSheafifyLarge

variable (A : Type u) [AddCommGroup A]

/-- The original all-degree constant restrictions compose with their native
constant coefficient identifications. -/
theorem constantRestriction_comp {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S)
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]
    [HasExt.{w''} (AbelianSheaf.{u, u + 1} T)]
    (q : ℕ) (c : Sheaf.H.{w} (ConstantFinite.coefficient A X) q) :
    constantRestriction A (g ≫ f) q c =
      constantRestriction A g q (constantRestriction A f q c) := by
  let P := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let M := ConstantFinite.value A
  have h := Functor.constantExtRestriction_comp
    (constantAdjunction X) (inverseImageAdjunction f) (inverseImageAdjunction g)
    (constantAdjunction S) (inverseImageAdjunction (g ≫ f)) (constantAdjunction T)
    (directImageGlobalSectionsIso f) (directImageCompIso f g)
    (directImageGlobalSectionsIso (g ≫ f)) (directImageGlobalSectionsIso g)
    (directImageGlobalSectionsIso_comp f g) P M q
  change ((inverseImage g).constantExtRestriction (inverseImageConstantCanonicalIso g) P M q).comp
      ((inverseImage f).constantExtRestriction (inverseImageConstantCanonicalIso f) P M q) =
    (inverseImage (g ≫ f)).constantExtRestriction
      (inverseImageConstantCanonicalIso (g ≫ f)) P M q at h
  simp only [inverseImageConstantCanonicalIso_eq] at h
  exact (congrArg (fun k => k c) h).symm

/-- Identity restriction keeps the original constant coefficient and Ext group. -/
theorem constantRestriction_id (X : Scheme.{u})
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] (q : ℕ)
    (c : Sheaf.H.{w} (ConstantFinite.coefficient A X) q) :
    constantRestriction A (𝟙 X) q c = c := by
  let P := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  have hs : ((inverseImageConstantIso (𝟙 X)).app P).inv ≫
      (inverseImageId X).hom.app
        ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj P) = 𝟙 _ := by
    rw [inverseImageId_constant]
    exact ((inverseImageConstantIso (𝟙 X)).app P).inv_hom_id
  have h := Functor.extCoefficientTransfer_id (inverseImage (𝟙 X)) (inverseImageId X)
    (((inverseImageConstantIso (𝟙 X)).app P).inv) hs (ConstantFinite.coefficient A X) q
  rw [inverseImageId_constant X (ConstantFinite.value A)] at h
  exact congrArg (fun k => k c) h

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
