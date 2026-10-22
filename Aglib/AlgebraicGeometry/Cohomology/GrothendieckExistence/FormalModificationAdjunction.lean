/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FormalPullback
public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-! # The original adjunction family for a formal modification

The pushforward target is only an ambient inverse diagram. In particular,
no adic compatibility or levelwise quotient/pushforward isomorphism is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u
variable {A : Type u} [CommRing A] {X Y : Scheme.{u}}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (p : Y ⟶ X) (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)

/-- Adjunction applied to the actual formal comparison, retaining its entire
original compatible family rather than assuming a compatible pushforward. -/
def formalModificationAdjoint
    (F : AdicSystem X (idealThickeningIdealSheaf f I))
    (G : AdicSystem Y (idealThickeningIdealSheaf (p ≫ f) I))
    (e : (baseIdealPullbackFunctor p f I).obj F ⟶ G) :
    F.obj ⟶ G.obj ⋙ pushforward p :=
  ((pullbackPushforwardAdjunction p).whiskerRight ℕᵒᵖ).homEquiv F.obj G.obj e.hom

/-- Every component is the original geometric adjunction map. -/
theorem formalModificationAdjoint_app
    (F : AdicSystem X (idealThickeningIdealSheaf f I))
    (G : AdicSystem Y (idealThickeningIdealSheaf (p ≫ f) I))
    (e : (baseIdealPullbackFunctor p f I).obj F ⟶ G) (n : ℕ) :
    (formalModificationAdjoint p f I F G e).app (op n) =
      (pullbackPushforwardAdjunction p).unit.app (F.obj.obj (op n)) ≫
        (pushforward p).map (e.hom.app (op n)) := by
  change (((pullbackPushforwardAdjunction p).whiskerRight ℕᵒᵖ).unit.app F.obj).app
    (op n) ≫ (pushforward p).map (e.hom.app (op n)) = _
  rw [Adjunction.whiskerRight_unit_app_app]

end AlgebraicGeometry.Scheme.Modules.Coherent
