/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.TwoIdeal.Recovery

/-! # The original target map retained by two-ideal recovery -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  (I : Ideal A) [IsAdicComplete I A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] (K : X.IdealSheafData)
  (h : ClosedThickeningCompletionEssSurj f I K)
  (F : AdicSystem X (idealThickeningIdealSheaf f I)) {G H : X.CoherentSheaf}
local notation "J" => idealThickeningIdealSheaf f I
local notation "C" => completionFunctor X K
variable (φ : F ⟶ (completionFunctor X (idealThickeningIdealSheaf f I)).obj H) (t : ℕ)
  (hφ : AdicSystem.DefectsKilled K t φ) (a : G ⟶ H)
  (β : (completionFunctor X K).obj G ≅ twoIdealCoefficientSystem I f K h F)
  (hβ : β.hom ≫ twoIdealCoefficientMap I f K h F φ = (completionFunctor X K).map a)
  (s : ℕ) (hk : killedByIdealSheaf (K ^ s) (kernel a.hom))
  (hc : killedByIdealSheaf (K ^ s) (cokernel a.hom))

/-- The recovered original I-system retains the specified original target map. -/
theorem twoIdealRecoveryIso_map :
    (twoIdealRecoveryIso I f K h F φ t hφ a β hβ s hk hc).hom ≫ φ =
      (completionFunctor X J).map a := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext n
  exact congrArg (fun z => z.hom)
    (twoIdealStageAlgebraizationIso_map I f K h F φ t hφ a β hβ s hk hc n.unop)

end AlgebraicGeometry.Scheme.Cohomology
