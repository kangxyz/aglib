/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.Open
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Sections

/-!
# Actual module-resolution sections on every open

Evaluation of the original structural-ring module section presheaf gives
the actual section complex of a supplied module injective resolution.
Its maps across opens are the original restriction maps, and coefficient
maps use the original supplied resolution lifts.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry TopologicalSpace Opposite HomologicalComplex

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R : Type u} [CommRing R] (X : Scheme.{u}) (α : R →+* Γ(X, ⊤)) (U : X.Opens)

/-- Evaluation of the sole original structural-ring section presheaf on the indicated open. -/
def moduleOpenSectionsFunctorOfHom : X.Modules ⥤ ModuleCat.{u} R :=
  moduleSectionsPresheafFunctor X α ⋙
    (CategoryTheory.evaluation X.Opensᵒᵖ (ModuleCat.{u} R)).obj (op U)

instance moduleOpenSectionsFunctorOfHom_additive :
    (moduleOpenSectionsFunctorOfHom X α U).Additive where
  map_add := by intros; ext x; rfl

/-- The actual integer-indexed module resolution evaluated on the indicated open. -/
abbrev moduleResolutionOpenSectionComplex {M : X.Modules} (I : InjectiveResolution M) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  ((moduleOpenSectionsFunctorOfHom X α U).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex

/-- Native kernel cycles in the original open-section complex. -/
abbrev moduleResolutionOpenSectionCycles {M : X.Modules} (I : InjectiveResolution M) (n : ℤ) :=
  LinearMap.ker ((moduleResolutionOpenSectionComplex X α U I).d n (n + 1)).hom

variable {U} {V : X.Opens} (i : U ⟶ V)

/-- The original presheaf restriction, functorially in its actual module coefficient. -/
def moduleOpenSectionsRestriction :
    moduleOpenSectionsFunctorOfHom X α V ⟶ moduleOpenSectionsFunctorOfHom X α U :=
  Functor.whiskerLeft (moduleSectionsPresheafFunctor X α)
    ((CategoryTheory.evaluation X.Opensᵒᵖ (ModuleCat.{u} R)).map i.op)

/-- The original open restriction on the actual supplied resolution section complex. -/
def moduleResolutionOpenSectionRestriction {M : X.Modules} (I : InjectiveResolution M) :
    moduleResolutionOpenSectionComplex X α V I ⟶ moduleResolutionOpenSectionComplex X α U I :=
  (NatTrans.mapHomologicalComplex (moduleOpenSectionsRestriction X α i) (.up ℤ)).app
    I.cochainComplex

theorem moduleResolutionOpenSectionRestriction_f_apply {M : X.Modules}
    (I : InjectiveResolution M) (n : ℤ)
    (s : (moduleResolutionOpenSectionComplex X α V I).X n) :
    (moduleResolutionOpenSectionRestriction X α i I).f n s =
      (I.cochainComplex.X n).presheaf.map i.op s := rfl

end AlgebraicGeometry.Scheme.Cohomology
