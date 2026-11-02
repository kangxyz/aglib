/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleScalarRestriction
public import Aglib.CategoryTheory.Adjunction.UnderlyingMate

/-! # The original slice-equivalence scalar comparison is an actual mate -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
  {Λ Γ : Type (u + 1)} [Ring Λ] [Ring Γ] (φ : Λ →+* Γ)

/-- The already defined forward slice comparison is the inverse mate of the literal
inverse-equivalence scalar comparison, not an independently selected isomorphism. -/
theorem moduleEtaleSliceScalarRestrictionIso_inv_mate :
    ((mateEquiv (moduleEtaleSliceSheafEquivalence j Γ).toAdjunction
      (moduleEtaleSliceSheafEquivalence j Λ).toAdjunction).symm
      (TwoSquare.mk _ _ _ _
        (moduleEtaleSliceInverseScalarRestrictionIso j φ).inv)).natTrans =
    (moduleEtaleSliceScalarRestrictionIso j φ).inv := by
  let E := moduleEtaleSliceSheafEquivalence j Γ
  let F := moduleEtaleSliceSheafEquivalence j Λ
  let V := moduleValuedRestrictScalars U φ
  let W := sheafCompose ((Scheme.smallEtaleTopology X).over (Scheme.Etale.mk j))
    (ModuleCat.restrictScalars.{u + 1} φ)
  change (Functor.leftUnitor (V ⋙ F.functor)).inv ≫
    Functor.whiskerRight E.unitIso.hom (V ⋙ F.functor) ≫
    (Functor.associator (E.functor ⋙ E.inverse) V F.functor).inv ≫
    Functor.whiskerRight (Functor.associator E.functor E.inverse V).hom F.functor ≫
    Functor.whiskerRight (Functor.whiskerLeft E.functor
      (moduleEtaleSliceInverseScalarRestrictionIso j φ).inv) F.functor ≫
    Functor.whiskerRight (Functor.associator E.functor W F.inverse).inv F.functor ≫
    (Functor.associator (E.functor ⋙ W) F.inverse F.functor).hom ≫
    Functor.whiskerLeft (E.functor ⋙ W) F.counitIso.hom ≫
    (Functor.rightUnitor (E.functor ⋙ W)).hom = _
  apply NatTrans.ext
  funext M
  dsimp only [E, F, V, W]
  simp only [moduleEtaleSliceScalarRestrictionIso_eq_original, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_map, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.assoc]
  rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
