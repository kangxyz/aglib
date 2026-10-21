/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.CoproductSections
public import Mathlib.Algebra.Category.ModuleCat.Products

/-!
# Actual affine sections of a quasicoherent coproduct

This concrete form of the affine section cocone comparison preserves the
original coefficient inclusions and the specified structural scalar action.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite DirectSum

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

variable {X : Scheme.{max u v}} {δ : Type v} (M : δ → X.Modules) (U : X.affineOpens)

/-- The original section maps induced by ambient coproduct inclusions. -/
def affineOpenSectionsCoproductCofan :
    Cofan (fun i => (M i).val.obj (op U.val)) :=
  Cofan.mk ((∐ M).val.obj (op U.val))
    (fun i => (Sigma.ι M i).val.app (op U.val))

/-- On an affine open these original section maps exhibit the coproduct. -/
def affineOpenSectionsCoproductIsColimit [∀ i, (M i).IsQuasicoherent] :
    IsColimit (affineOpenSectionsCoproductCofan M U) := by
  let T := Scheme.Modules.toPresheafOfModules X ⋙
    PresheafOfModules.evaluation X.ringCatSheaf.obj (op U.val)
  let e : Discrete.functor (fun i => (M i).val.obj (op U.val)) ≅
      Discrete.functor M ⋙ T := Discrete.natIso (fun _ => Iso.refl _)
  have h := (IsColimit.precomposeHomEquiv e _).symm
    (affineOpenSectionsIsColimit U
      (fun i => inferInstanceAs (M i.as).IsQuasicoherent) (coproductIsCoproduct M))
  apply IsColimit.ofIsoColimit h
  refine Cocone.ext (Iso.refl _) ?_
  intro i
  simp only [e, T, affineOpenSectionsCoproductCofan]
  rfl

/-- Actual affine sections of the ambient coproduct are the direct sum of sections. -/
def affineOpenSectionsCoproductIso [DecidableEq δ] [∀ i, (M i).IsQuasicoherent] :
    (∐ M).val.obj (op U.val) ≅
      ModuleCat.of Γ(X, U.val) (⨁ i, (M i).val.obj (op U.val)) :=
  (affineOpenSectionsCoproductIsColimit M U).coconePointUniqueUpToIso
    (ModuleCat.coproductCoconeIsColimit _)

/-- The section comparison sends each original coefficient inclusion to `DirectSum.lof`. -/
@[reassoc]
theorem affineOpenSectionsCoproductIso_ι [DecidableEq δ] [∀ i, (M i).IsQuasicoherent] (i : δ) :
    (Sigma.ι M i).val.app (op U.val) ≫
        (affineOpenSectionsCoproductIso M U).hom =
      ModuleCat.ofHom (DirectSum.lof Γ(X, U.val) δ
        (fun i => (M i).val.obj (op U.val)) i) :=
  (affineOpenSectionsCoproductIsColimit M U).comp_coconePointUniqueUpToIso_hom
    (ModuleCat.coproductCoconeIsColimit _) (Discrete.mk i)

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
