/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.AlgebraicGeometry.PullbackCarrier
/-! # Actual overlap maps for base-changed finite covering families -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleAffineBasis
universe u
variable {S T U V : Scheme.{u}} (τ : T ⟶ S) (f : U ⟶ S) (g : V ⟶ S)

/-- The first projection from the base change of an overlap. -/
def overlapBaseChangeLeft :
    pullback τ (pullback.fst f g ≫ f) ⟶ pullback τ f :=
  pullback.lift (pullback.fst τ (pullback.fst f g ≫ f))
    (pullback.snd τ (pullback.fst f g ≫ f) ≫ pullback.fst f g)
    ((pullback.condition).trans (Category.assoc _ _ _).symm)

/-- The second projection from the base change of an overlap. -/
def overlapBaseChangeRight :
    pullback τ (pullback.fst f g ≫ f) ⟶ pullback τ g :=
  pullback.lift (pullback.fst τ (pullback.fst f g ≫ f))
    (pullback.snd τ (pullback.fst f g ≫ f) ≫ pullback.snd f g)
    (pullback.condition.trans
      ((congrArg (fun z ↦ pullback.snd τ (pullback.fst f g ≫ f) ≫ z)
        pullback.condition).trans (Category.assoc _ _ _).symm))

/-- The overlap of the two base-changed charts maps to the base-changed overlap. -/
def overlapBaseChangePair :
    pullback (pullback.fst τ f) (pullback.fst τ g) ⟶
      pullback τ (pullback.fst f g ≫ f) := by
  let a := pullback.fst (pullback.fst τ f) (pullback.fst τ g)
  let b := pullback.snd (pullback.fst τ f) (pullback.fst τ g)
  have hab : (a ≫ pullback.snd τ f) ≫ f = (b ≫ pullback.snd τ g) ≫ g := by
    calc
      _ = a ≫ (pullback.snd τ f ≫ f) := Category.assoc _ _ _
      _ = a ≫ (pullback.fst τ f ≫ τ) :=
        congrArg (fun z ↦ a ≫ z) (pullback.condition (f := τ) (g := f)).symm
      _ = (a ≫ pullback.fst τ f) ≫ τ := (Category.assoc _ _ _).symm
      _ = (b ≫ pullback.fst τ g) ≫ τ :=
        congrArg (fun z ↦ z ≫ τ) pullback.condition
      _ = b ≫ (pullback.fst τ g ≫ τ) := Category.assoc _ _ _
      _ = b ≫ (pullback.snd τ g ≫ g) :=
        congrArg (fun z ↦ b ≫ z) pullback.condition
      _ = _ := (Category.assoc _ _ _).symm
  let q := pullback.lift (a ≫ pullback.snd τ f) (b ≫ pullback.snd τ g) hab
  exact pullback.lift (a ≫ pullback.fst τ f) q (by
    calc
      _ = a ≫ (pullback.fst τ f ≫ τ) := Category.assoc _ _ _
      _ = a ≫ (pullback.snd τ f ≫ f) :=
        congrArg (fun z ↦ a ≫ z) pullback.condition
      _ = (a ≫ pullback.snd τ f) ≫ f := (Category.assoc _ _ _).symm
      _ = (q ≫ pullback.fst f g) ≫ f :=
        congrArg (fun z ↦ z ≫ f) (pullback.lift_fst _ _ _).symm
      _ = _ := Category.assoc _ _ _)

/-- The map to the first original chart is the literal first projection. -/
lemma overlapBaseChangePair_left :
    overlapBaseChangePair τ f g ≫ pullback.snd τ (pullback.fst f g ≫ f) ≫
        pullback.fst f g =
      pullback.fst (pullback.fst τ f) (pullback.fst τ g) ≫ pullback.snd τ f := by
  simp only [overlapBaseChangePair, pullback.lift_snd_assoc, pullback.lift_fst]

/-- The map to the second original chart is the literal second projection. -/
lemma overlapBaseChangePair_right :
    overlapBaseChangePair τ f g ≫ pullback.snd τ (pullback.fst f g ≫ f) ≫
        pullback.snd f g =
      pullback.snd (pullback.fst τ f) (pullback.fst τ g) ≫ pullback.snd τ g := by
  simp only [overlapBaseChangePair, pullback.lift_snd_assoc, pullback.lift_snd]
end AlgebraicGeometry.Scheme.EtaleAffineBasis
