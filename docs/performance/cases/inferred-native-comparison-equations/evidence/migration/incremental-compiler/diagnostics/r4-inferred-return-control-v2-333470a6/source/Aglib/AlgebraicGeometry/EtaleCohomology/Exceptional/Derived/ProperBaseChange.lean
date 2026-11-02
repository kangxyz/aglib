/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnderlyingBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnderlyingTorsion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.BaseChange
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Conservative

/-!
# Frozen original cube application with inferred return type

The complete declaration context, eight derived data and K type are the same
as the namespace-corrected source-typed control. The actual original proof
application is checked against its own inferred proposition, with no explicit
return type, unused proof value, kernel skip or additional mathematical premise.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.R4PointwiseCube

open Coefficients

universe u wMX wMS wMX' wMS' wAX wAS wAX' wAS'

attribute [local instance] hasSheafifyLarge

variable (Λ : Type (u + 1)) [Ring Λ] {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wMX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wMS'} (ModuleSheaf S' Λ)]
  [HasDerivedCategory.{wAX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{wAX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{wAS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

attribute [local instance] CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

/-- Check the literal original application against its own inferred proposition. -/
theorem inferredPointwise (K : DerivedCategory.Plus (ModuleSheaf X Λ)) : _ :=
  moduleDerivedBaseChangeMap_underlying Λ f f' g g' sq.w.symm K

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.R4PointwiseCube
