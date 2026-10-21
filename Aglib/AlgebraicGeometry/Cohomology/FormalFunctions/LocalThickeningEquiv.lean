/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.LocalQuotientEquiv
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ThickeningSections
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Stalk
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.LocalSpectrum
public import Mathlib.AlgebraicGeometry.Noetherian
public import Aglib.RingTheory.AdicCompletion.EquivTransport

/-!
# Formal functions for the original higher-direct-image stalk

Flat localization identifies the original stalk with cohomology on the actual
local-spectrum base change. Formal functions then applies to its actual
ideal-power quotient coefficient tower. This construction does not interchange
stalks and inverse limits, and does not assert nonflat base change is invertible.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsProper f]
  (F : X.Modules) (hF : affineLocallyFiniteType X F) (y : Y)
  (I : Ideal (Y.presheaf.stalk y)) (p : ℕ)

/-- Classical local formal functions: completion of the original higher-image
stalk is the limit of original cohomology on the actual infinitesimal fibres.
The ideal can be arbitrary; taking the maximal ideal gives the usual local form. -/
def moduleHigherDirectImageStalkFormalFunctionsEquiv :
    let a := Limits.pullback.fst f (Y.fromSpecStalk y)
    let b := Limits.pullback.snd f (Y.fromSpecStalk y)
    let N := (Scheme.Modules.pullback a).obj F
    AdicCompletion I ((moduleStalk Y y).obj
      (((Scheme.Modules.pushforward f).rightDerived p).obj F)) ≃ₗ[Y.presheaf.stalk y]
        ModuleCat.sectionsSubmodule (properIdealThickeningCohomologyTower
          (A := Y.presheaf.stalk y) b N
          (affineLocallyFiniteType_fromSpecStalkPullback f F hF y) I p) := by
  let a := Limits.pullback.fst f (Y.fromSpecStalk y)
  let b := Limits.pullback.snd f (Y.fromSpecStalk y)
  let N := (Scheme.Modules.pullback a).obj F
  let α := b.appTop.hom.comp (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv.hom
  refine (show AdicCompletion I ((moduleStalk Y y).obj
    (((Scheme.Modules.pushforward f).rightDerived p).obj F)) ≃ₗ[Y.presheaf.stalk y]
      ModuleCat.sectionsSubmodule (idealPowerQuotientCohomology _ α N I p) from ?_) ≪≫ₗ ?_
  · exact moduleHigherDirectImageStalkFormalFunctionsQuotientEquiv f F hF y I p
  · exact properIdealQuotientThickeningSectionsEquiv (Y.presheaf.stalk y) b N
      (affineLocallyFiniteType_fromSpecStalkPullback f F hF y) I p

end AlgebraicGeometry.Scheme.Cohomology
