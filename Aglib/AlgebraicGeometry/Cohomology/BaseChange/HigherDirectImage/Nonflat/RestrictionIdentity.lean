/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Native open restriction along an identity refinement

The original congruence and composition comparisons for an identity
refinement agree with the inverse native identity comparison. This is an
equality of the actual restricted arrows, with arbitrary module coefficients.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules.Nonflat

/-- The native comparison for an identity refinement is the inverse original
identity-restriction comparison, including the specified morphism equalities. -/
theorem restrictFunctor_identity_refinement_hom
    {V X : Scheme.{u}} (v : V ⟶ X) [IsOpenImmersion v]
    (r : V ⟶ V) (er : r = 𝟙 V) (h : r ≫ v = v) (M : X.Modules) :
    letI : IsOpenImmersion r := by rw [er]; infer_instance
    (restrictFunctorCongr h.symm).hom.app M ≫ (restrictFunctorComp r v).hom.app M =
      ((restrictFunctorCongr er) ≪≫ (restrictFunctorId (X := V))).inv.app (M.restrict v) := by
  subst r
  apply Scheme.Modules.hom_ext
  intro U
  simp only [Iso.trans_inv, NatTrans.comp_app, Hom.comp_app,
    restrictFunctorCongr_hom_app_app, restrictFunctorComp_hom_app_app,
    restrictFunctorId_inv_app_app, restrictFunctorCongr_inv_app_app]
  simp only [restrict_map]
  change M.presheaf.map _ ≫ M.presheaf.map _ =
    M.presheaf.map _ ≫ M.presheaf.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

end AlgebraicGeometry.Scheme.Modules.Nonflat
