/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.InternalExtSource

/-! # Original-map and standard-axiom guards -/

/-- info: 'SheafOfModules.InternalHom.liftedUnitCoyonedaIso_precompose' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.liftedUnitCoyonedaIso_precompose

/-- info: 'SheafOfModules.InternalHom.evaluationSheaf_naturality' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.evaluationSheaf_naturality

/-- info: 'SheafOfModules.InternalHom.unitHomAddEquiv_evaluation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.unitHomAddEquiv_evaluation

/-- info: 'SheafOfModules.InternalHom.evaluationSheaf_map_tmul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.evaluationSheaf_map_tmul

/-- info: 'SheafOfModules.InternalHom.unitSourceHomIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.unitSourceHomIso

/-- info: 'SheafOfModules.InternalHom.unitSourceHomIso_evaluation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.unitSourceHomIso_evaluation

/-- info: 'SheafOfModules.InternalHom.liftedUnitSourceHomIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.liftedUnitSourceHomIso

/-- info: 'CategoryTheory.Functor.internalExtReverse_resolution' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.internalExtReverse_resolution


/-- info: 'CategoryTheory.Sheaf.InternalExt.moduleExtReverse_precompose' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Sheaf.InternalExt.moduleExtReverse_precompose

/-- info: 'CategoryTheory.Sheaf.InternalExt.cohomologyExtReverse_precompose' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Sheaf.InternalExt.cohomologyExtReverse_precompose

/-- info: 'SheafOfModules.InternalHom.unitSourceHomIso_globalHom' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.unitSourceHomIso_globalHom

/-- info: 'SheafOfModules.InternalHom.liftedUnitSourceHomIso_coyoneda' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.liftedUnitSourceHomIso_coyoneda

/-- info: 'CategoryTheory.Sheaf.InternalExt.moduleExtReverse_unit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Sheaf.InternalExt.moduleExtReverse_unit

/-- info: 'CategoryTheory.Sheaf.InternalExt.cohomologyExtReverse_unit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Sheaf.InternalExt.cohomologyExtReverse_unit
