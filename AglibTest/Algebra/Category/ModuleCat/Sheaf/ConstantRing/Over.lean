/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Over

/-!
# Original internal-Hom provider axiom guards

Every public declaration retains the standard three-axiom predicate.
-/

/-- info: 'ModuleCat.Sheaf.ConstantRing.constantRingMap_over_isIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.constantRingMap_over_isIso

/-- info: 'ModuleCat.Sheaf.ConstantRing.overRingIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.overRingIso

/-- info: 'ModuleCat.Sheaf.ConstantRing.overRingIso_hom' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.overRingIso_hom

/-- info: 'ModuleCat.Sheaf.ConstantRing.overRingIso_unit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.overRingIso_unit

/-- info: 'ModuleCat.Sheaf.ConstantRing.overFunctorRestrictScalarsIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.overFunctorRestrictScalarsIso

/-- info: 'ModuleCat.Sheaf.ConstantRing.overFunctorRestrictScalarsIso_hom_app' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.overFunctorRestrictScalarsIso_hom_app
