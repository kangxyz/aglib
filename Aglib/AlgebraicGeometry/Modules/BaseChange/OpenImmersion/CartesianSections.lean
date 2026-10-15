/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Cartesian

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/CartesianOpenBaseChangeSections.lean` at LOCAL
Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 62]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Sections of cartesian open base change

Compute the original cartesian open base-change map on sections as literal
presheaf transport along the cartesian equality of opens.
-/

@[expose] public section
noncomputable section

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
open Scheme.Modules
variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j] (h : IsPullback a b f j)
/-- The original base-change component is its literal restriction-adjunction mate. -/
theorem cartesianOpenBaseChange_hom_app_mate (M : U.Modules) :
    (cartesianOpenBaseChange a b f j h).hom.app M =
      (restrictFunctor j).map
        ((pushforward f).map ((restrictAdjunction a).unit.app M) ≫
          (cartesianPushforwardSquare a b f j h).hom.app ((restrictFunctor a).obj M)) ≫
        (restrictAdjunction j).counit.app ((pushforward b).obj ((restrictFunctor a).obj M)) := by
  rw [cartesianOpenBaseChange_hom_mate]
  rfl
/-- Actual open restriction retains the original module map on the image open. -/
theorem restrictFunctor_map_app {M N : X.Modules} (g : M ⟶ N) (T : V.Opens) :
    ((restrictFunctor j).map g).app T = g.app (j ''ᵁ T) := rfl
omit [IsOpenImmersion a] [IsOpenImmersion j] in
/-- The original pushforward square only transports sections along its actual open equality. -/
theorem cartesianPushforwardSquare_hom_app (M : W.Modules) (T : X.Opens) :
    ((cartesianPushforwardSquare a b f j h).hom.app M).app T =
      M.presheaf.map (eqToHom (show b ⁻¹ᵁ (j ⁻¹ᵁ T) = a ⁻¹ᵁ (f ⁻¹ᵁ T) from
        congrArg (fun k => k ⁻¹ᵁ T) h.w.symm)).op := by
  simp only [cartesianPushforwardSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app, Scheme.Modules.pushforwardCongr_hom_app_app,
    Category.id_comp, Category.comp_id]
/-- The actual cartesian open base-change arrow is the original section restriction. -/
theorem cartesianOpenBaseChange_hom_app (M : U.Modules) (T : V.Opens) :
    ((cartesianOpenBaseChange a b f j h).hom.app M).app T =
      M.presheaf.map (eqToHom
        (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback h.flip T)).op := by
  rw [cartesianOpenBaseChange_hom_app_mate, Scheme.Modules.Hom.comp_app,
    restrictFunctor_map_app, Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.restrictAdjunction_unit_app_app, cartesianPushforwardSquare_hom_app,
    Scheme.Modules.restrictAdjunction_counit_app_app]
  change M.presheaf.map _ ≫ M.presheaf.map _ ≫ M.presheaf.map _ = M.presheaf.map _
  simp only [← Functor.map_comp]
  congr 1
end AlgebraicGeometry.Scheme.Modules
end
