/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FullFaithful
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ClosedImmersionReduction.QuotientUnit

/-! # Proper completion detects annihilation by a closed-embedding ideal

The comparison uses the original geometric quotient unit. No supplied ideal
annihilation of the algebraization or effectivity conclusion is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  (I : Ideal A) [IsAdicComplete I A] {X Y : Scheme.{u}}
  [IsLocallyNoetherian Y] (i : X ⟶ Y) [IsClosedImmersion i]
  (f : Y ⟶ Spec (CommRingCat.of A)) [IsProper f]

/-- If every actual completion quotient is killed by the embedding ideal,
then so is the original coherent coefficient on the proper ambient scheme. -/
theorem killedByIdealSheaf_of_completion (G : Y.CoherentSheaf)
    (h : ∀ n : ℕ, killedByIdealSheaf i.ker
      ((idealSheafQuotientFunctor Y (idealThickeningIdealSheaf f I ^ n)).obj G.obj)) :
    killedByIdealSheaf i.ker G.obj := by
  let H : Y.CoherentSheaf := ⟨(pushforward i).obj ((pullback i).obj G.obj),
    QuasiCoherent.FiniteMorphism.affineLocallyFiniteType_pushforward i
      (QuasiCoherent.affineLocallyFiniteType_pullback i G.property)⟩
  let φ : G ⟶ H := ObjectProperty.homMk
    ((pullbackPushforwardAdjunction i).unit.app G.obj)
  let C := completionFunctor Y (idealThickeningIdealSheaf f I)
  let D := adicSystemToDiagram Y (idealThickeningIdealSheaf f I)
  have hiso : IsIso (D.map (C.map φ)) := by
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro n
    exact quotient_closedUnit_isIso i (idealThickeningIdealSheaf f I ^ n.unop)
      G.obj (h n.unop)
  let : IsIso (C.map φ) := isIso_of_reflects_iso (C.map φ) D
  let : IsIso φ := (completionFunctorFullyFaithful I f).isIso_of_isIso_map φ
  have : IsIso ((pullbackPushforwardAdjunction i).unit.app G.obj) :=
    (QuasiCoherent.finiteTypeSheavesToModules Y).map_isIso φ
  exact (pullbackPushforwardUnit_isIso_iff_killedByIdealSheaf i G.obj).mp this

/-- In particular, an ambient algebraization whose completed terms are
isomorphic to actual closed pushforwards is annihilated by the defining ideal. -/
theorem killedByIdealSheaf_of_completion_pushforward (G : Y.CoherentSheaf)
    (F : ℕ → X.Modules)
    (e : ∀ n : ℕ,
      (idealSheafQuotientFunctor Y (idealThickeningIdealSheaf f I ^ n)).obj G.obj ≅
        (pushforward i).obj (F n)) : killedByIdealSheaf i.ker G.obj :=
  killedByIdealSheaf_of_completion I i f G (fun n =>
    killedByIdealSheaf_of_iso i.ker (e n).symm
      (killedByIdealSheaf_pushforward_ker i (F n)))

end AlgebraicGeometry.Scheme.Cohomology
