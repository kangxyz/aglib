/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.CoproductSections
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Sections

/-!
# Structural-ring sections of quasicoherent coproducts

The original structural-ring section functor preserves colimits of
quasicoherent coefficients when evaluated on an affine open. The statements
retain the original cocone maps and do not assert finite generation.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

variable {R : Type (max u v)} [CommRing R] (X : Scheme.{max u v}) (α : R →+* Γ(X, ⊤))

/-- Evaluation of structural-ring sections is literal scalar restriction of open sections. -/
def moduleSectionsEvaluationIso {R : Type u} [CommRing R]
    (X : Scheme.{u}) (α : R →+* Γ(X, ⊤)) (U : X.Opens) :
    (Scheme.Modules.toPresheafOfModules X ⋙
      PresheafOfModules.evaluation X.ringCatSheaf.obj (op U)) ⋙
        ModuleCat.restrictScalars ((X.presheaf.map (homOfLE le_top).op).hom.comp α) ≅
    moduleSectionsPresheafFunctor X α ⋙ (evaluation _ _).obj (op U) :=
  NatIso.ofComponents (fun M => ModuleCat.restrictScalarsComp'App α
    (X.presheaf.map (homOfLE le_top).op).hom _ rfl (M.val.obj (op U)))
    (fun _ => by ext x; rfl)

/-- Affine sections of a quasicoherent colimiting cocone remain colimiting
with the specified original structural-ring action. -/
def moduleAffineSectionsIsColimit (U : X.Opens) (hU : IsAffineOpen U)
    {J : Type v} [Category.{v} J] {F : J ⥤ X.Modules}
    (hF : ∀ j, (F.obj j).IsQuasicoherent) {c : Cocone F} (hc : IsColimit c) :
    IsColimit ((moduleSectionsPresheafFunctor X α ⋙
      (evaluation _ _).obj (op U)).mapCocone c) :=
  IsColimit.mapCoconeEquiv (moduleSectionsEvaluationIso X α U)
    (isColimitOfPreserves (ModuleCat.restrictScalars
      ((X.presheaf.map (homOfLE le_top).op).hom.comp α))
      (Scheme.Modules.QuasiCoherent.affineOpenSectionsIsColimit ⟨U, hU⟩ hF hc))

end AlgebraicGeometry.Scheme.Cohomology
