/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleLowerShriekValuedUnit
public import Aglib.CategoryTheory.Adjunction.UnderlyingEquivalence
public import Aglib.CategoryTheory.Adjunction.UnderlyingMate

/-! # The original native lower-shriek adjunction under its coefficient equivalence -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
  (R : Type (u + 1)) [Ring R]

/-- The original native and module-valued lower-shriek adjunctions have their
specified comparison square on the actual units. -/
@[reassoc]
theorem moduleLowerShriekValuedIso_unit (M : ModuleSheaf U R) :
    (moduleSheafEquivalence U R).inverse.map ((moduleLowerShriekAdjunction j R).unit.app M) ≫
      (moduleInverseImageValuedIso R j).hom.app ((moduleLowerShriek j R).obj M) ≫
      (moduleValuedInverseImage j R).map ((moduleLowerShriekValuedIso j R).hom.app M) =
    (moduleValuedLowerShriekAdjunction j R).unit.app
      ((moduleSheafEquivalence U R).inverse.obj M) := by
  rw [moduleLowerShriekAdjunction_unit, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (moduleLowerShriekRightIso_hom_valuedCancellation j R
    ((moduleLowerShriek j R).obj M)), moduleLowerShriekValuedIso_hom_component]
  let EU := moduleSheafEquivalence U R
  let EX := moduleSheafEquivalence X R
  let L := moduleValuedInverseImage j R
  let P := (moduleValuedLowerShriek j R).obj (EU.inverse.obj M)
  let a := (moduleValuedLowerShriekAdjunction j R).unit.app (EU.inverse.obj M)
  let b := L.map (EX.unitIso.hom.app P)
  let k := L.map (EX.unitIso.inv.app P)
  have hk : b ≫ k = 𝟙 _ := (L.mapIso (EX.unitIso.app P)).hom_inv_id
  have hn := NatIso.inv_map_map_hom_comp EU.unitIso.symm a b k hk
  change EU.inverse.map ((EU.counitIso.inv.app M ≫ EU.functor.map a) ≫
      EU.functor.map b) ≫
    EU.unitIso.inv.app (L.obj (EX.inverse.obj (EX.functor.obj P))) ≫ k = a
  rw [Functor.map_comp, Functor.map_comp, ← EU.unit_app_inverse]
  simp only [Iso.symm_hom, Iso.symm_inv, Functor.comp_map,
    CategoryTheory.Functor.id_map] at hn
  change EU.unitIso.hom.app (EU.inverse.obj M) ≫
    EU.inverse.map (EU.functor.map a) ≫ EU.inverse.map (EU.functor.map b) ≫
      EU.unitIso.inv.app (L.obj (EX.inverse.obj (EX.functor.obj P))) ≫ k = a
  exact hn

/-- The original lower-shriek realization and original pullback realization are mates. -/
theorem mate_moduleLowerShriekValuedIso_inv :
    (mateEquiv (moduleLowerShriekAdjunction j R) (moduleValuedLowerShriekAdjunction j R)
      (TwoSquare.mk _ _ _ _ (moduleLowerShriekValuedIso j R).inv)).natTrans =
    (moduleInverseImageValuedIso R j).hom :=
  mateEquiv_inv_natTrans_eq_of_unit _ _ _ _ (moduleLowerShriekValuedIso_unit j R)

end AlgebraicGeometry.Scheme.EtaleCohomology
