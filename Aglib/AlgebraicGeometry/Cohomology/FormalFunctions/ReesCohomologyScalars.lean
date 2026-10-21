/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars
public import Mathlib.Algebra.Algebra.Tower

/-! # Compatible structural scalar towers on original cohomology -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  (X : Scheme.{u}) (α : A →+* Γ(X, ⊤)) (β : B →+* Γ(X, ⊤))

/-- Compatible maps to global functions give compatible actions on the original
cohomology. Scalar normalization is proved before specializing the coefficient. -/
theorem moduleCohomology_isScalarTower_ofHom (h : α = β.comp (algebraMap A B))
    (M : X.Modules) (q : ℕ) :
    letI := moduleCohomologyModuleOfHom X α M q
    letI := moduleCohomologyModuleOfHom X β M q
    IsScalarTower A B (Sheaf.H.{u + 1} (moduleAddSheaf X M) q) := by
  let := moduleCohomologyModuleOfHom X α M q
  let := moduleCohomologyModuleOfHom X β M q
  apply IsScalarTower.of_algebraMap_smul
  intro a x
  change Sheaf.H.map (moduleScalarOfGlobal X M (β (algebraMap A B a))) q x =
    Sheaf.H.map (moduleScalarOfGlobal X M (α a)) q x
  rw [h]
  rfl

end AlgebraicGeometry.Scheme.Cohomology
