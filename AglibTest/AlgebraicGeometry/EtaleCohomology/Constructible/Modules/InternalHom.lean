/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.InternalHom

/-! Actual finite-presentation charts for the original native internal Hom. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

attribute [local instance] hasSheafifyLarge hasSheafifyModules ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

set_option backward.isDefEq.respectTransparency false in
example {X : Scheme.{u}} (R : Type (u + 1)) [CommRing R] [Finite R]
    [(forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).Full]
    (F G : ModuleSheaf X R)
    (hF : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence X R).inverse.obj F))
    (hG : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence X R).inverse.obj G)) :
    Constructible.Modules.IsFiniteTypeLocallyConstant ((moduleSheafEquivalence X R).inverse.obj
      (SheafOfModules.InternalHom.sheaf
        (ModuleCat.Sheaf.ConstantRing.commutativeSheaf X.smallEtaleTopology R) F G)) :=
  Constructible.Modules.isFiniteTypeLocallyConstant_nativeInternalHom R F G hF hG

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules.nativeInternalHomConstantSliceIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules.nativeInternalHomConstantSliceIso

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules.isFiniteTypeLocallyConstant_nativeInternalHom' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules.isFiniteTypeLocallyConstant_nativeInternalHom
