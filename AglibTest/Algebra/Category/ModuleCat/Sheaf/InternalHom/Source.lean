/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.Source

/-! # Original source internal-Hom maps and exactness axiom guards -/

/-- info: 'SheafOfModules.InternalHom.sourceFunctor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.sourceFunctor

/-- info: 'SheafOfModules.InternalHom.sourceFunctor_obj' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.sourceFunctor_obj

/-- info: 'SheafOfModules.InternalHom.sourceFunctor_map' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.sourceFunctor_map

/-- info: 'SheafOfModules.InternalHom.sourceFunctor_postcompose_app' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.sourceFunctor_postcompose_app

/-- info: 'SheafOfModules.InternalHom.sourceFunctor_additive' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.sourceFunctor_additive

/-- info: 'SheafOfModules.InternalHom.bifunctor_flip_additive' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.bifunctor_flip_additive

/-- info: 'SheafOfModules.InternalHom.sectionHomSourceNatIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.sectionHomSourceNatIso

/-- info: 'SheafOfModules.InternalHom.sectionHomSourceNatIso_hom_app_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.sectionHomSourceNatIso_hom_app_apply

/-- info: 'SheafOfModules.InternalHom.sourceFunctor_preservesFiniteLimits' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.sourceFunctor_preservesFiniteLimits

/-- info: 'SheafOfModules.InternalHom.sourceFunctor_preservesEpimorphisms' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.sourceFunctor_preservesEpimorphisms

/-- info: 'SheafOfModules.InternalHom.sourceFunctor_preservesHomology' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.sourceFunctor_preservesHomology

/-- info: 'SheafOfModules.InternalHom.shortExact_source' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.shortExact_source

/-- info: 'SheafOfModules.InternalHom.sourceComplexFunctor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.sourceComplexFunctor

/-- info: 'SheafOfModules.InternalHom.sourceComplexFunctor_shortComplex_eval' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.sourceComplexFunctor_shortComplex_eval

/-- info: 'SheafOfModules.InternalHom.shortExact_sourceComplex' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.shortExact_sourceComplex

/-- info: 'SheafOfModules.InternalHom.sourceComplexFunctor_additive' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.sourceComplexFunctor_additive
