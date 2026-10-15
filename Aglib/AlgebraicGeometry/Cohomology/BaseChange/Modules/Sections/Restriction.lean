/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Sections
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars
public import Aglib.AlgebraicGeometry.Modules.Restriction.Sections

/-!
# Structural-ring sections under open restriction

The original restricted-section isomorphism is linear over an arbitrary
specified structural ring. Its scalar-forgetting forward map is literally the
inverse of the existing `Scheme.Modules.restrictedSectionsIso`; no chosen
replacement section comparison is introduced.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The actual open-chart ring map sends restricted global functions to their geometric pullback. -/
theorem appIso_globalRestriction_top (a : Γ(X, ⊤)) :
    (j.appIso ⊤).hom (globalRestriction X (j ''ᵁ ⊤) a) = j.appTop a := by
  change (X.presheaf.map (homOfLE le_top).op ≫ (j.appIso ⊤).hom) a = _
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
  change (j.appTop ≫ U.presheaf.map (𝟙 (op ⊤))) a = j.appTop a
  rw [U.presheaf.map_id, CategoryTheory.Category.comp_id]

/-- The canonical open-restriction section comparison with its specified structural ring. -/
def moduleSectionsRestrictionIso {A : Type u} [CommRing A]
    (α : A →+* Γ(X, ⊤)) (M : X.Modules) :
    (moduleSectionsPresheaf X α M).obj (op j.opensRange) ≅
      (moduleSectionsPresheaf U (j.appTop.hom.comp α) (M.restrict j)).obj (op ⊤) := by
  refine ModuleCat.isoMk (((Scheme.Modules.restrictedSectionsIso j).app M).symm) ?_
  intro r
  ext m
  symm
  change M.val.obj (op j.opensRange) at m
  change M.val.map (eqToHom j.image_top_eq_opensRange).op
      (globalRestriction X j.opensRange (α r) • m) =
    (j.appIso ⊤).inv (globalRestriction U ⊤ (j.appTop (α r))) •
      M.val.map (eqToHom j.image_top_eq_opensRange).op m
  rw [M.val.map_smul]
  congr 1
  change X.presheaf.map (eqToHom j.image_top_eq_opensRange).op
      (globalRestriction X j.opensRange (α r)) =
    (j.appIso ⊤).inv (globalRestriction U ⊤ (j.appTop (α r)))
  rw [map_globalRestriction, globalRestriction_top_apply]
  rw [← appIso_globalRestriction_top j (α r)]
  exact (ConcreteCategory.congr_hom (j.appIso ⊤).hom_inv_id _).symm

/-- Forgetting structural scalars gives the original restricted-section inverse map. -/
theorem moduleSectionsRestrictionIso_hom_forget {A : Type u} [CommRing A]
    (α : A →+* Γ(X, ⊤)) (M : X.Modules) :
    (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).map
        (moduleSectionsRestrictionIso j α M).hom =
      ((Scheme.Modules.restrictedSectionsIso j).app M).inv := rfl

end AlgebraicGeometry.Scheme.Cohomology
