/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ThickeningSectionsReduction
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.LocalQuotientEquiv
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.LocalThickeningEquiv

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

/-- On a genuine stalk class, every coordinate is its original localized
cohomology class followed by the actual coefficient reduction. -/
theorem moduleHigherDirectImageStalkFormalFunctionsQuotientEquiv_of
    (s : (moduleStalk Y y).obj (((Scheme.Modules.pushforward f).rightDerived p).obj F))
    (n : ℕ) :
    let a := Limits.pullback.fst f (Y.fromSpecStalk y)
    let b := Limits.pullback.snd f (Y.fromSpecStalk y)
    let N := (Scheme.Modules.pullback a).obj F
    let α := b.appTop.hom.comp (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv.hom
    letI : F.IsQuasicoherent := quasicoherent_of_affineCharts F (fun R j _ => (hF R j).1)
    (moduleHigherDirectImageStalkFormalFunctionsQuotientEquiv f F hF y I p
      (AdicCompletion.of I _ s)).val (op n) =
      moduleCohomologyMapOfHom _ α (idealQuotientπ _ α N (I ^ n)) p
        (moduleHigherDirectImageStalkLinearEquiv f F y p s) := by
  let : F.IsQuasicoherent := quasicoherent_of_affineCharts F (fun R j _ => (hF R j).1)
  dsimp only [moduleHigherDirectImageStalkFormalFunctionsQuotientEquiv]
  rw [AdicCompletion.equivOfCongr_of]
  exact moduleCohomologyFormalFunctionsEquiv_of (A := Y.presheaf.stalk y) I
    (Limits.pullback.snd f (Y.fromSpecStalk y))
    ((Scheme.Modules.pullback (Limits.pullback.fst f (Y.fromSpecStalk y))).obj F)
    (affineLocallyFiniteType_fromSpecStalkPullback f F hF y) p
    (moduleHigherDirectImageStalkLinearEquiv f F y p s) n

/-- The local completion comparison sends a genuine stalk class to its actual
localized cohomology class restricted geometrically to every infinitesimal fibre. -/
theorem moduleHigherDirectImageStalkFormalFunctionsEquiv_of
    (s : (moduleStalk Y y).obj (((Scheme.Modules.pushforward f).rightDerived p).obj F))
    (n : ℕ) :
    let a := Limits.pullback.fst f (Y.fromSpecStalk y)
    let b := Limits.pullback.snd f (Y.fromSpecStalk y)
    let N := (Scheme.Modules.pullback a).obj F
    letI : F.IsQuasicoherent := quasicoherent_of_affineCharts F (fun R j _ => (hF R j).1)
    (moduleHigherDirectImageStalkFormalFunctionsEquiv f F hF y I p
      (AdicCompletion.of I _ s)).val (op n) =
      moduleCohomologyPullback (idealThickeningι b (I ^ n)) N p
        (moduleHigherDirectImageStalkLinearEquiv f F y p s) := by
  let : F.IsQuasicoherent := quasicoherent_of_affineCharts F (fun R j _ => (hF R j).1)
  let a := Limits.pullback.fst f (Y.fromSpecStalk y)
  let b := Limits.pullback.snd f (Y.fromSpecStalk y)
  let N := (Scheme.Modules.pullback a).obj F
  change (properIdealQuotientThickeningSectionsEquiv (Y.presheaf.stalk y) b N
    (affineLocallyFiniteType_fromSpecStalkPullback f F hF y) I p
      (moduleHigherDirectImageStalkFormalFunctionsQuotientEquiv f F hF y I p
        (AdicCompletion.of I _ s))).val (op n) = _
  refine properIdealQuotientThickeningSectionsEquiv_reduction
    (Y.presheaf.stalk y) b N (affineLocallyFiniteType_fromSpecStalkPullback f F hF y) I p
    (moduleHigherDirectImageStalkFormalFunctionsQuotientEquiv f F hF y I p
      (AdicCompletion.of I _ s)) (moduleHigherDirectImageStalkLinearEquiv f F y p s) n ?_
  exact moduleHigherDirectImageStalkFormalFunctionsQuotientEquiv_of f F hF y I p s n

end AlgebraicGeometry.Scheme.Cohomology
