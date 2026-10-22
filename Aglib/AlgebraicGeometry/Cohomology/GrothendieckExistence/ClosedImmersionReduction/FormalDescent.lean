/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FormalPullback
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ClosedImmersionReduction.Pushforward
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.QuotientSystem

/-! # Descent of original base-adic systems to an independent closed subscheme

Descent uses the actual ordinary pullback at every stage. The original units
provide the comparison, without choices of unrelated inverse equivalences.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {A : Type u} [CommRing A] {X Y : Scheme.{u}}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (i : X ⟶ Y) [IsClosedImmersion i]
  (f : Y ⟶ Spec (CommRingCat.of A)) (I : Ideal A)

local notation "KY" => idealThickeningIdealSheaf f I

/-- Stagewise annihilation descends the entire original formal diagram,
with the actual geometric units as comparison components. -/
def closedFormalDescentDiagramIso (F : AdicSystem Y KY)
    (hF : ∀ n : ℕ, killedByIdealSheaf i.ker (F.obj.obj (op n))) :
    F.obj ≅ ((baseIdealPullbackFunctor i f I).obj F).obj ⋙ pushforward i :=
  NatIso.ofComponents
    (fun n => (closedImmersionDescentIso i (F.obj.obj n) (hF n.unop)).symm)
    (by
      intro m n g
      exact (pullbackPushforwardAdjunction i).unit.naturality (F.obj.map g))

/-- The descended coefficient is the original formal pullback, and pushing
it forward recovers the original native formal system. -/
def closedFormalDescentIso (F : AdicSystem Y KY)
    (hF : ∀ n : ℕ, killedByIdealSheaf i.ker (F.obj.obj (op n))) :
    F ≅ closedPushforwardAdicSystem i f I ((baseIdealPullbackFunctor i f I).obj F) :=
  ObjectProperty.isoMk _ (closedFormalDescentDiagramIso i f I F hF)

@[simp]
theorem closedFormalDescentIso_hom_app (F : AdicSystem Y KY)
    (hF : ∀ n : ℕ, killedByIdealSheaf i.ker (F.obj.obj (op n))) (n : ℕ) :
    (closedFormalDescentIso i f I F hF).hom.hom.app (op n) =
      (pullbackPushforwardAdjunction i).unit.app (F.obj.obj (op n)) := rfl

/-- Quotient by the independent closed ideal supplies exactly the
annihilation needed for actual formal descent. -/
def closedQuotientFormalDescentIso (F : AdicSystem Y KY) :
    AdicSystem.quotient Y KY i.ker F ≅
      closedPushforwardAdicSystem i f I ((baseIdealPullbackFunctor i f I).obj
        (AdicSystem.quotient Y KY i.ker F)) :=
  closedFormalDescentIso i f I _ (fun n => AdicSystem.quotient_killed Y KY i.ker F n)

end AlgebraicGeometry.Scheme.Cohomology
