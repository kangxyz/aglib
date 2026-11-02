/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleScalarRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleAdjunctionCompatibility

/-! # Original lower-shriek coefficient-equivalence unit comparisons -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
  (R : Type (u + 1)) [Ring R]

omit [Etale j] in
/-- The old native right-adjoint identification cancels against the old native-to-valued
pullback comparison, leaving exactly the coefficient-equivalence inverse unit. -/
theorem moduleLowerShriekRightIso_hom_valuedCancellation (N : ModuleSheaf X R) :
    (moduleSheafEquivalence U R).inverse.map ((moduleLowerShriekRightIso j R).hom.app N) ≫
      (moduleInverseImageValuedIso R j).hom.app N =
    (moduleSheafEquivalence U R).unitIso.inv.app
      ((moduleValuedInverseImage j R).obj ((moduleSheafEquivalence X R).inverse.obj N)) := by
  simp only [moduleLowerShriekRightIso, moduleInverseImageValuedIso,
    Equivalence.coefficientRightIso, ValuedComparison.inverseValuedIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.rightUnitor_hom_app,
    Category.id_comp,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  exact (congrArg (fun k => k ≫ (moduleSheafEquivalence U R).unitIso.inv.app
    ((moduleValuedInverseImage j R).obj ((moduleSheafEquivalence X R).inverse.obj N)))
      ((moduleSheafEquivalence U R).inverse.map_id _)).trans (Category.id_comp _)

/-- The existing lower-shriek realization has the actual inverse equivalence unit as component. -/
theorem moduleLowerShriekValuedIso_hom_component (M : ModuleSheaf U R) :
    (moduleLowerShriekValuedIso j R).hom.app M =
    (moduleSheafEquivalence X R).unitIso.inv.app
      ((moduleValuedLowerShriek j R).obj ((moduleSheafEquivalence U R).inverse.obj M)) := by
  change 𝟙 _ ≫ (moduleSheafEquivalence X R).unitIso.inv.app
      ((moduleValuedLowerShriek j R).obj ((moduleSheafEquivalence U R).inverse.obj M)) ≫ 𝟙 _ = _
  exact (Category.id_comp _).trans (Category.comp_id _)

end AlgebraicGeometry.Scheme.EtaleCohomology
