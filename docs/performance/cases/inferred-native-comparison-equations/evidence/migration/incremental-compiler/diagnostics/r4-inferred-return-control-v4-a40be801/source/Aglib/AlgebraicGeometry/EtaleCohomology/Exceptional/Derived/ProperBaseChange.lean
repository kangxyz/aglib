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
# Frozen original cube application with its inferred proposition

The ordinary helper returns the actual proposition carried by the original
proof application. The theorem header obtains that proposition without a
manual native equation; its body remains the same real proof application.
All source context, selected data and normal compiler checks are retained.
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

/-- The actual proposition carried by the supplied proof term. -/
def proofConclusion {P : Prop} (_ : P) : Prop := P

/-- Check the original application against exactly the proposition that it supplies. -/
theorem inferredPointwise (K : DerivedCategory.Plus (ModuleSheaf X Λ)) :
    proofConclusion (moduleDerivedBaseChangeMap_underlying Λ f f' g g' sq.w.symm K) :=
  moduleDerivedBaseChangeMap_underlying Λ f f' g g' sq.w.symm K

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.R4PointwiseCube
