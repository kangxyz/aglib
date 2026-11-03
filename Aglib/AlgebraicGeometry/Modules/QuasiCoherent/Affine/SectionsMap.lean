/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ScalarAdjunction


/-!
# Maps supplied by the original affine quasicoherent equivalence

This is the preimage under the inverse of Mathlib's sole tildeEquiv, not a
second affine equivalence or a new choice of module presentation. The exact
original global-section arrow is retained.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} {M N : (Spec R).Modules}
  [M.IsQuasicoherent] [N.IsQuasicoherent]

/-- The original affine equivalence produces the sheaf map with these exact sections. -/
def affineSectionsMap (g : moduleSpecΓFunctor.obj M ⟶ moduleSpecΓFunctor.obj N) : M ⟶ N :=
  let X : (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory :=
    ⟨M, inferInstance⟩
  let Y : (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory :=
    ⟨N, inferInstance⟩
  let q : (tildeEquiv (R := R)).inverse.obj X ⟶ (tildeEquiv (R := R)).inverse.obj Y := g
  ((tildeEquiv (R := R)).inverse.preimage q).hom

/-- Its original global-section map is exactly the supplied module map. -/
theorem affineSectionsMap_sections
    (g : moduleSpecΓFunctor.obj M ⟶ moduleSpecΓFunctor.obj N) :
    moduleSpecΓFunctor.map (affineSectionsMap g) = g := by
  let X : (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory :=
    ⟨M, inferInstance⟩
  let Y : (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory :=
    ⟨N, inferInstance⟩
  let q : (tildeEquiv (R := R)).inverse.obj X ⟶ (tildeEquiv (R := R)).inverse.obj Y := g
  exact (tildeEquiv (R := R)).inverse.map_preimage q

/-- No alternative map with the same original section values is selected. -/
theorem affineSectionsMap_unique
    (g : moduleSpecΓFunctor.obj M ⟶ moduleSpecΓFunctor.obj N)
    (f : M ⟶ N) (hf : moduleSpecΓFunctor.map f = g) : f = affineSectionsMap g :=
  hom_eq_of_globalSections_eq f _ (hf.trans (affineSectionsMap_sections g).symm)

end AlgebraicGeometry.Scheme.Modules
