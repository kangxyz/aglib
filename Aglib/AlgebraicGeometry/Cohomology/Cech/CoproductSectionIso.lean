/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.CoproductSections
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

namespace AlgebraicGeometry.Scheme.Cohomology

variable {R : Type (max u v)} [CommRing R] (X : Scheme.{max u v}) (α : R →+* Γ(X, ⊤))
  {δ : Type v} (M : δ → X.Modules) (U : X.Opens)

/-- The original section maps induced by ambient coproduct inclusions. -/
def moduleSectionsCoproductCofan :
    Cofan (fun i => (moduleSectionsPresheaf X α (M i)).obj (op U)) :=
  Cofan.mk ((moduleSectionsPresheaf X α (∐ M)).obj (op U))
    (fun i => ((moduleSectionsPresheafFunctor X α).map (Sigma.ι M i)).app (op U))

/-- On an affine open these original section maps exhibit the coproduct. -/
def moduleAffineSectionsCoproductIsColimit (hU : IsAffineOpen U)
    [∀ i, (M i).IsQuasicoherent] :
    IsColimit (moduleSectionsCoproductCofan X α M U) := by
  let T := moduleSectionsPresheafFunctor X α ⋙ (evaluation _ _).obj (op U)
  let e : Discrete.functor (fun i => (moduleSectionsPresheaf X α (M i)).obj (op U)) ≅
      Discrete.functor M ⋙ T := Discrete.natIso (fun _ => Iso.refl _)
  have h := (IsColimit.precomposeHomEquiv e _).symm
    (moduleAffineSectionsIsColimit X α U hU
      (fun i => inferInstanceAs (M i.as).IsQuasicoherent) (coproductIsCoproduct M))
  apply IsColimit.ofIsoColimit h
  refine Cocone.ext (Iso.refl _) ?_
  intro i
  simp [e, T, moduleSectionsCoproductCofan]

/-- Actual affine sections of the ambient coproduct are the direct sum of sections. -/
def moduleAffineSectionsCoproductIso [DecidableEq δ] (hU : IsAffineOpen U)
    [∀ i, (M i).IsQuasicoherent] :
    (moduleSectionsPresheaf X α (∐ M)).obj (op U) ≅
      ModuleCat.of R (⨁ i, (moduleSectionsPresheaf X α (M i)).obj (op U)) :=
  (moduleAffineSectionsCoproductIsColimit X α M U hU).coconePointUniqueUpToIso
    (ModuleCat.coproductCoconeIsColimit _)

/-- The section comparison sends each original coefficient inclusion to `DirectSum.lof`. -/
@[reassoc]
theorem moduleAffineSectionsCoproductIso_ι [DecidableEq δ] (hU : IsAffineOpen U)
    [∀ i, (M i).IsQuasicoherent] (i : δ) :
    ((moduleSectionsPresheafFunctor X α).map (Sigma.ι M i)).app (op U) ≫
        (moduleAffineSectionsCoproductIso X α M U hU).hom =
      ModuleCat.ofHom (DirectSum.lof R δ
        (fun i => (moduleSectionsPresheaf X α (M i)).obj (op U)) i) :=
  (moduleAffineSectionsCoproductIsColimit X α M U hU).comp_coconePointUniqueUpToIso_hom
    (ModuleCat.coproductCoconeIsColimit _) (Discrete.mk i)

end AlgebraicGeometry.Scheme.Cohomology
