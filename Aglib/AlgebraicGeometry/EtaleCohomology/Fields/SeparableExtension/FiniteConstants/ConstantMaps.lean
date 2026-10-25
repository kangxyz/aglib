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

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u w w' w''

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
  simp only [constantRestriction, AddMonoidHom.comp_apply]
  let z := cohomologyPullback.{u, w, w''} (g ≫ f) (ConstantFinite.coefficient A X) q c
  let φ := ((inverseImageConstantIso f).app (ConstantFinite.value A)).hom
  let ψ := ((inverseImageConstantIso g).app (ConstantFinite.value A)).hom
  let θ := (inverseImageComp f g).hom.app (ConstantFinite.coefficient A X)
  have hn := cohomologyPullback_coefficientMap.{u, w', w''} g φ q
    (cohomologyPullback.{u, w, w'} f (ConstantFinite.coefficient A X) q c)
  have hc := cohomologyPullback_comp.{u, w, w', w''} f g
    (ConstantFinite.coefficient A X) q c
  change Sheaf.H.map ((inverseImageConstantIso (g ≫ f)).app
      (ConstantFinite.value A)).hom q z =
    Sheaf.H.map ψ q (cohomologyPullback.{u, w', w''} g
      (ConstantFinite.coefficient A S) q
        (Sheaf.H.map φ q (cohomologyPullback.{u, w, w'} f
          (ConstantFinite.coefficient A X) q c)))
  calc
    Sheaf.H.map ((inverseImageConstantIso (g ≫ f)).app
        (ConstantFinite.value A)).hom q z =
      Sheaf.H.map (θ ≫ (inverseImage g).map φ ≫ ψ) q z :=
      congrArg (fun r => Sheaf.H.map r q z)
        (inverseImageComp_constant f g (ConstantFinite.value A)).symm
    _ = Sheaf.H.map ((inverseImage g).map φ ≫ ψ) q (Sheaf.H.map θ q z) :=
      Sheaf.H.map_comp_apply θ ((inverseImage g).map φ ≫ ψ) z
    _ = Sheaf.H.map ψ q
        (Sheaf.H.map ((inverseImage g).map φ) q (Sheaf.H.map θ q z)) :=
      Sheaf.H.map_comp_apply ((inverseImage g).map φ) ψ (Sheaf.H.map θ q z)
    _ = Sheaf.H.map ψ q (Sheaf.H.map ((inverseImage g).map φ) q
        (cohomologyPullback.{u, w', w''} g
          ((inverseImage f).obj (ConstantFinite.coefficient A X)) q
          (cohomologyPullback.{u, w, w'} f (ConstantFinite.coefficient A X) q c))) :=
      congrArg (fun a => Sheaf.H.map ψ q (Sheaf.H.map ((inverseImage g).map φ) q a)) hc
    _ = Sheaf.H.map ψ q (cohomologyPullback.{u, w', w''} g
        (ConstantFinite.coefficient A S) q
        (Sheaf.H.map φ q (cohomologyPullback.{u, w, w'} f
          (ConstantFinite.coefficient A X) q c))) :=
      congrArg (Sheaf.H.map ψ q) hn.symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite

universe u e

attribute [local instance] hasSheafifyLarge

variable (A : Type u) [AddCommGroup A]

private theorem constantTriangle_inv_all {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ X) (a : T ⟶ S) (h : a ≫ f = g) :
    (pullbackTriangleIso g f a h).inv.app (coefficient A X) ≫
        ((inverseImageConstantIso g).app (value A)).hom =
      (inverseImage a).map ((inverseImageConstantIso f).app (value A)).hom ≫
        ((inverseImageConstantIso a).app (value A)).hom := by
  subst g
  have hc : (inverseImageComp f a).inv.app (coefficient A X) ≫
      ((inverseImageConstantIso (a ≫ f)).app (value A)).hom =
    (inverseImage a).map ((inverseImageConstantIso f).app (value A)).hom ≫
      ((inverseImageConstantIso a).app (value A)).hom := by
    apply (cancel_epi ((inverseImageComp f a).hom.app (coefficient A X))).mp
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    exact (inverseImageComp_constant f a (value A)).symm
  simpa only [pullbackTriangleIso, Iso.trans_inv, NatTrans.comp_app, eqToIso.inv,
    eqToHom_app, eqToHom_refl, Category.comp_id] using hc

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
  change Sheaf.H.map ((inverseImageConstantIso g).app (value A)).hom q
      (Sheaf.H.map ((pullbackTriangleIso g f a h).inv.app (coefficient A X)) q
        (cohomologyPullback a ((inverseImage f).obj (coefficient A X)) q c)) =
    Sheaf.H.map ((inverseImageConstantIso a).app (value A)).hom q
      (cohomologyPullback a (coefficient A S) q
        (Sheaf.H.map ((inverseImageConstantIso f).app (value A)).hom q c))
  rw [cohomologyPullback_coefficientMap]
  let z := cohomologyPullback a ((inverseImage f).obj (coefficient A X)) q c
  let φ := ((inverseImageConstantIso f).app (value A)).hom
  let ψ := ((inverseImageConstantIso g).app (value A)).hom
  let η := ((inverseImageConstantIso a).app (value A)).hom
  let θ := (pullbackTriangleIso g f a h).inv.app (coefficient A X)
  change Sheaf.H.map ψ q (Sheaf.H.map θ q z) =
    Sheaf.H.map η q (Sheaf.H.map ((inverseImage a).map φ) q z)
  calc
    Sheaf.H.map ψ q (Sheaf.H.map θ q z) = Sheaf.H.map (θ ≫ ψ) q z :=
      (Sheaf.H.map_comp_apply θ ψ z).symm
    _ = Sheaf.H.map ((inverseImage a).map φ ≫ η) q z :=
      congrArg (fun r => Sheaf.H.map r q z) (constantTriangle_inv_all A f g a h)
    _ = Sheaf.H.map η q (Sheaf.H.map ((inverseImage a).map φ) q z) :=
      Sheaf.H.map_comp_apply ((inverseImage a).map φ) η z

end AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite
