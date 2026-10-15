/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.Geometric
public import Aglib.Topology.Sheaves.FreeAbelianPullback.Composition

/-! # Composition of the original geometric open-cohomology maps

Successive original inverse-image Ext maps compose to the original map for
the composite morphism, with its actual composite coefficient arrow. The
comparison of inverse-image functors is the native adjunction comparison;
the actual inverse-image opens agree definitionally.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y Z : Scheme.{u}} (p : Y ⟶ X) (q : Z ⟶ Y)

/-- The native inverse-image composition comparison, with the original adjunction units. -/
abbrev zariskiPullbackCompIso :
    zariskiPullback p ⋙ zariskiPullback q ≅ zariskiPullback (q ≫ p) :=
  TopCat.Sheaf.abelianPullbackCompIso p.base q.base

/-- The actual open-cohomology map uses the original native inverse-image Ext map. -/
theorem zariskiCohomologyOpenMap_app_apply
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (B : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (a : (zariskiPullback p).obj A ⟶ B) (n : ℕ) (U : X.Opensᵒᵖ)
    (x : Ext.{u + 1} ((additiveOpenFreeFunctor X).obj U.unop) A n) :
    (zariskiCohomologyOpenMap p A B a n).app U x =
      ((Ext.mk₀ ((additiveOpenPullbackIso p).inv.app U.unop)).comp
        (x.mapExactFunctor (zariskiPullback p)) (Nat.zero_add n)).comp
          (Ext.mk₀ a) (Nat.add_zero n) := rfl

/-- Successive original geometric maps on an open are the original composite map,
with the actual inverse-image composite coefficient. -/
theorem zariskiCohomologyOpenMap_comp_app
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (B : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (C : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
    (a : (zariskiPullback p).obj A ⟶ B)
    (b : (zariskiPullback q).obj B ⟶ C) (n : ℕ) (U : X.Opensᵒᵖ) :
    (zariskiCohomologyOpenMap p A B a n).app U ≫
        (zariskiCohomologyOpenMap q B C b n).app ((Opens.map p.base).op.obj U) =
      (zariskiCohomologyOpenMap (q ≫ p) A C
        ((zariskiPullbackCompIso p q).inv.app A ≫ (zariskiPullback q).map a ≫ b) n).app U := by
  ext x
  change Ext.{u + 1} ((additiveOpenFreeFunctor X).obj U.unop) A n at x
  change (zariskiCohomologyOpenMap q B C b n).app ((Opens.map p.base).op.obj U)
      ((zariskiCohomologyOpenMap p A B a n).app U x) = _
  erw [zariskiCohomologyOpenMap_app_apply, zariskiCohomologyOpenMap_app_apply,
    zariskiCohomologyOpenMap_app_apply]
  change (_ : Ext.{u + 1}
    ((additiveOpenFreeFunctor Z).obj (q ⁻¹ᵁ (p ⁻¹ᵁ U.unop))) C n) = _
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀]
  rw [← Ext.comp_assoc_of_third_deg_zero, ← Ext.comp_assoc_of_second_deg_zero,
    Ext.mk₀_comp_mk₀]
  have h := TopCat.Sheaf.openFreeAbelianPullbackIso_comp_inv p.base q.base U.unop
  change (additiveOpenPullbackIso q).inv.app (p ⁻¹ᵁ U.unop) ≫
      (zariskiPullback q).map ((additiveOpenPullbackIso p).inv.app U.unop) =
    (additiveOpenPullbackIso (q ≫ p)).inv.app U.unop ≫
      (zariskiPullbackCompIso p q).inv.app ((additiveOpenFreeFunctor X).obj U.unop) at h
  erw [h, ← Ext.mk₀_comp_mk₀, ← Ext.comp_mapExactFunctor]
  erw [Ext.comp_assoc_of_second_deg_zero
    (Ext.mk₀ ((additiveOpenPullbackIso (q ≫ p)).inv.app U.unop))
    (Ext.mk₀ ((zariskiPullbackCompIso p q).inv.app ((additiveOpenFreeFunctor X).obj U.unop)))
    (x.mapExactFunctor (zariskiPullback p ⋙ zariskiPullback q)) (Nat.zero_add n)]
  erw [← Ext.mapExactFunctor_comp_mk₀_natTransApp x (zariskiPullbackCompIso p q).inv]
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Category.assoc]

/-- The original geometric open-cohomology transformation respects composition. -/
theorem zariskiCohomologyOpenMap_comp
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (B : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (C : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
    (a : (zariskiPullback p).obj A ⟶ B)
    (b : (zariskiPullback q).obj B ⟶ C) (n : ℕ) :
    zariskiCohomologyOpenMap p A B a n ≫
        Functor.whiskerLeft (Opens.map p.base).op (zariskiCohomologyOpenMap q B C b n) =
      zariskiCohomologyOpenMap (q ≫ p) A C
        ((zariskiPullbackCompIso p q).inv.app A ≫ (zariskiPullback q).map a ≫ b) n := by
  apply NatTrans.ext
  funext U
  exact zariskiCohomologyOpenMap_comp_app p q A B C a b n U

end AlgebraicGeometry.Scheme.Cohomology
