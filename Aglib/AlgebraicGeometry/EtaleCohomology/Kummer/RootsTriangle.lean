/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootsPullbackSquare
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackCohomologySystem

/-! # Original coefficient triangles and raw orientation squares

All maps, coefficients and cohomology worlds are the original ones. The raw
square contains no small-site object or alternative cohomology model.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe u e e' a b c d

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

attribute [local instance] hasSheafifyLarge

theorem roots_triangle {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ X)
    (a : Y ⟶ Z) (h : a ≫ g = f) (n : ℕ) (hn : 0 < n)
    (hi : IsUnit (n : Γ(X, ⊤))) :
    (pullbackTriangleIso f g a h).inv.app (mu X n) ≫ (rootsPullbackIso f n hn hi).hom =
      (inverseImage a).map (rootsPullbackIso g n hn hi).hom ≫
        (rootsPullbackIso a n hn (levelInvertible g n hi)).hom := by
  subst f
  change (inverseImageComp g a).inv.app (mu X n) ≫
    (rootsPullbackIso (a ≫ g) n hn hi).hom = _
  apply (cancel_epi ((inverseImageComp g a).hom.app (mu X n))).mp
  simpa only [Iso.hom_inv_id_app_assoc, Category.assoc] using
    (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso_comp g a n hn hi).symm

theorem roots_cohomology_triangle {X Y Z : Scheme.{u}}
    [HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{e'} (AbelianSheaf.{u, u + 1} Z)]
    (f : Y ⟶ X) (g : Z ⟶ X) (a : Y ⟶ Z) (h : a ≫ g = f)
    (n : ℕ) (hn : 0 < n) (hi : IsUnit (n : Γ(X, ⊤)))
    (c : Sheaf.H.{e'} ((inverseImage g).obj (mu X n)) 1) :
    Sheaf.H.map (rootsPullbackIso f n hn hi).hom 1
      (Sheaf.H.map ((pullbackTriangleIso f g a h).inv.app (mu X n)) 1
        (cohomologyPullback a ((inverseImage g).obj (mu X n)) 1 c)) =
      rootsCohomologyPullback a n hn (levelInvertible g n hi) 1
        (Sheaf.H.map (rootsPullbackIso g n hn hi).hom 1 c) := by
  rw [← Sheaf.H.map_comp_apply, roots_triangle f g a h n hn hi,
    Sheaf.H.map_comp_apply]
  exact congrArg (fun z => Sheaf.H.map
    (rootsPullbackIso a n hn (levelInvertible g n hi)).hom 1 z)
    (cohomologyPullback_coefficientMap.{u, e', e} a
      (rootsPullbackIso g n hn hi).hom 1 c).symm

/-- Whole original coefficient triangles preserve the actual roots-to-Picard map. -/
theorem rootsPicard_triangle {X Y Z : Scheme.{u}}
    [HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{e'} (AbelianSheaf.{u, u + 1} Z)]
    (f : Y ⟶ X) (g : Z ⟶ X) (a : Y ⟶ Z) (h : a ≫ g = f)
    (n : ℕ) (hn : 0 < n) (hi : IsUnit (n : Γ(X, ⊤)))
    (c : Sheaf.H.{e'} ((inverseImage g).obj (mu X n)) 1) :
    rootsPicardMap Y n (Sheaf.H.map (rootsPullbackIso f n hn hi).hom 1
      (Sheaf.H.map ((pullbackTriangleIso f g a h).inv.app (mu X n)) 1
        (cohomologyPullback a ((inverseImage g).obj (mu X n)) 1 c))) =
      pullbackClass a (rootsPicardMap Z n
        (Sheaf.H.map (rootsPullbackIso g n hn hi).hom 1 c)) := by
  exact (congrArg (rootsPicardMap Y n)
    (roots_cohomology_triangle f g a h n hn hi c)).trans
      (DFunLike.congr_fun (rootsPicardMap_pullback a n hn (levelInvertible g n hi)) _)

/-- A coefficient triangle followed by an actual orientation square, with independent worlds. -/
theorem rootsCohomology_triangle_orientation {B Y Z Y' Z' : Scheme.{u}}
    [hY : HasExt.{a} (AbelianSheaf.{u, u + 1} Y)]
    [hZ : HasExt.{b} (AbelianSheaf.{u, u + 1} Z)]
    [hY' : HasExt.{c} (AbelianSheaf.{u, u + 1} Y')]
    [hZ' : HasExt.{d} (AbelianSheaf.{u, u + 1} Z')]
    (f : Y ⟶ B) (g : Z ⟶ B) (t : Y ⟶ Z) (ht : t ≫ g = f)
    (i : Y' ⟶ Y) (j : Z' ⟶ Z) (k : Y' ⟶ Z') (hs : i ≫ t = k ≫ j)
    (n : ℕ) (hn : 0 < n) (hi : IsUnit (n : Γ(B, ⊤)))
    (x : Sheaf.H.{b} ((inverseImage g).obj (mu B n)) 1) :
    rootsCohomologyPullback i n hn (levelInvertible f n hi) 1
      (Sheaf.H.map (rootsPullbackIso f n hn hi).hom 1
        (Sheaf.H.map ((pullbackTriangleIso f g t ht).inv.app (mu B n)) 1
          (cohomologyPullback t ((inverseImage g).obj (mu B n)) 1 x))) =
    rootsCohomologyPullback k n hn
      (levelInvertible j n (levelInvertible g n hi)) 1
      (rootsCohomologyPullback j n hn (levelInvertible g n hi) 1
        (Sheaf.H.map (rootsPullbackIso g n hn hi).hom 1 x)) := by
  have htri := @roots_cohomology_triangle B Y Z hY hZ f g t ht n hn hi x
  refine (congrArg (@rootsCohomologyPullback Y Y' hY hY' i n hn
    (levelInvertible f n hi) 1) htri).trans ?_
  exact @rootsPullback_commutativeSquare Z Y Z' Y' hZ hY hZ' hY'
    t j i k hs n hn (levelInvertible g n hi)
    (Sheaf.H.map (rootsPullbackIso g n hn hi).hom 1 x)

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
