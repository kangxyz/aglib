/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ModulePullbackComposition

/-! # Original cohomology of the coefficient triangle

The native sheaf-arrow triangle is first normalized by the original invertible
étale coefficient arrows. Its cohomology consequence uses only original
coefficient naturality and functoriality of `Sheaf.H.map`, with independent Ext
ranges on the two charts.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules

universe u eS eT

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

attribute [local instance] hasSheafifyLarge

variable {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S) (a : T ⟶ X)
  (h : g ≫ f = a) [Etale f] [Etale g] [Etale a]
  (M : X.Modules) [M.IsQuasicoherent]

/-- The actual inverse coefficient square for an étale transition of charts. -/
theorem additiveCoefficientPullback_triangle_inv :
    additiveCoefficientPullback g ((pullback f).obj M) ≫
      additiveCoefficientMap T (F := (pullback g).obj ((pullback f).obj M))
          (G := (pullback a).obj M)
        ((Scheme.Modules.pullbackTriangleIso g f a h).hom.app M) ≫
      inv (additiveCoefficientPullback a M) =
    (inverseImage g).map (inv (additiveCoefficientPullback f M)) ≫
      (EtaleCohomology.pullbackTriangleIso a f g h).inv.app (additiveCoefficient X M) := by
  let c : additiveCoefficient T ((pullback g).obj ((pullback f).obj M)) ⟶
      additiveCoefficient T ((pullback a).obj M) :=
    additiveCoefficientMap T (F := (pullback g).obj ((pullback f).obj M))
          (G := (pullback a).obj M)
    ((Scheme.Modules.pullbackTriangleIso g f a h).hom.app M)
  let t := (EtaleCohomology.pullbackTriangleIso a f g h).inv.app (additiveCoefficient X M)
  let p := (inverseImage g).mapIso (asIso (additiveCoefficientPullback f M))
  let q := asIso (additiveCoefficientPullback a M)
  have hc : p.hom ≫ additiveCoefficientPullback g ((pullback f).obj M) ≫ c =
      t ≫ q.hom := additiveCoefficientPullback_triangle f g M a h
  change additiveCoefficientPullback g ((pullback f).obj M) ≫ c ≫ q.inv = p.inv ≫ t
  apply (cancel_epi p.hom).mp
  rw [reassoc_of% hc, q.hom_inv_id, Category.comp_id, p.hom_inv_id_assoc]

variable [HasExt.{eS} (AbelianSheaf.{u, u + 1} S)]
  [HasExt.{eT} (AbelianSheaf.{u, u + 1} T)]

/-- The actual chart transition on module coefficient cohomology becomes the
original étale triangle transition, in every degree and independent Ext worlds. -/
theorem additiveCoefficientCohomologyPullback_triangle_inv (n : ℕ)
    (x : Sheaf.H.{eS} (additiveCoefficient S ((pullback f).obj M)) n) :
    Sheaf.H.map (inv (additiveCoefficientPullback a M)) n
      (Sheaf.H.map
        (additiveCoefficientMap T (F := (pullback g).obj ((pullback f).obj M))
          (G := (pullback a).obj M)
          ((Scheme.Modules.pullbackTriangleIso g f a h).hom.app M)) n
        (additiveCoefficientCohomologyPullback.{u, eS, eT} g ((pullback f).obj M) n x)) =
    Sheaf.H.map
      ((EtaleCohomology.pullbackTriangleIso a f g h).inv.app (additiveCoefficient X M)) n
      (cohomologyPullback.{u, eS, eT} g
        ((inverseImage f).obj (additiveCoefficient X M)) n
        (Sheaf.H.map (inv (additiveCoefficientPullback f M)) n x)) := by
  change Sheaf.H.map (inv (additiveCoefficientPullback a M)) n
    (Sheaf.H.map
      (additiveCoefficientMap T (F := (pullback g).obj ((pullback f).obj M))
          (G := (pullback a).obj M) ((Scheme.Modules.pullbackTriangleIso g f a h).hom.app M)) n
      (Sheaf.H.map (additiveCoefficientPullback g ((pullback f).obj M)) n
        (cohomologyPullback g (additiveCoefficient S ((pullback f).obj M)) n x))) = _
  rw [cohomologyPullback_coefficientMap]
  simp only [← Sheaf.H.map_comp_apply]
  rw [Category.assoc, additiveCoefficientPullback_triangle_inv]
  exact Sheaf.H.map_comp_apply _ _ _

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
