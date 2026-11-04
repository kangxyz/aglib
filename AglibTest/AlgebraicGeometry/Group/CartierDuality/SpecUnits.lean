/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.SpecUnits

/-! Native affine unit coordinates over an arbitrary commutative base ring. -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Group
open CartierDuality

universe u

variable {R : Type u} [CommRing R] (A : CommAlgCat.{u} R)

example : (((AlgebraicGeometry.algSpec (CommRingCat.of R)).obj (op A)) ⟶
    MultiplicativeGroup.scheme (Spec (CommRingCat.of R))) ≃ Aˣ := specUnitsEquiv A

example (u : Aˣ) : (specUnitsEquiv A).symm u = specUnitMap A u :=
  specUnitsEquiv_symm_apply A u

example (T : Over (Spec (CommRingCat.of R)))
    (p : T ⟶ (AlgebraicGeometry.algSpec (CommRingCat.of R)).obj (op A)) (u : Aˣ) :
    MultiplicativeGroup.sectionsUnitsEquiv (Spec (CommRingCat.of R)) T (p ≫ specUnitMap A u) =
      Units.map (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.left.appTop).hom.toMonoidHom) u :=
  specUnitMap_comp_units A u T p
