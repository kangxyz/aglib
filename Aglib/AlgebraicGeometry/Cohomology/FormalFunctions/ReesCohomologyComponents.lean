/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ReesCohomologySections

/-! # Typed original coefficient components before geometric specialization -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] (X : Scheme.{u}) (α : A →+* Γ(X, ⊤))
  {M N P : X.Modules}

/-- Original coefficient inclusion followed by a section comparison is the
unchanged composite on actual cohomology. The coefficient modules are variables. -/
theorem moduleSectionsCohomology_coefficient_comp (φ : M ⟶ N)
    (e : moduleSectionsPresheaf X α N ⟶ moduleSectionsPresheaf X α P)
    (q : ℕ) (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) q) :
    Sheaf.H.map (moduleSectionsAddSheafMap X α
      ((moduleSectionsPresheafFunctor X α).map φ ≫ e)) q x =
    Sheaf.H.map (moduleSectionsAddSheafMap X α e) q
      (moduleCohomologyMapOfHom X α φ q x) := by
  have h : moduleSectionsAddSheafMap X α
      ((moduleSectionsPresheafFunctor X α).map φ ≫ e) =
      (SheafOfModules.toSheaf X.ringCatSheaf).map φ ≫
        moduleSectionsAddSheafMap X α e := rfl
  rw [h, Sheaf.H.map_comp_apply]
  rfl

end AlgebraicGeometry.Scheme.Cohomology
