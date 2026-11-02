/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.CompositeExchange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.LowerShriekBaseChange
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperBaseChangeTheorem

/-! # The actual unbounded compactified Cartesian exchange

This is the original proper exchange followed by the localized original open
comparison. Its invertibility uses the proved unbounded proper base-change theorem
for a torsion coefficient ring, not a bounded-below comparison. Neither base is
assumed quasi-compact and all six native derived models are independent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wY wS wX' wY' wT

variable {X Y S X' Y' T : Scheme.{u}}
  (j : X ⟶ Y) (p : Y ⟶ S) (j' : X' ⟶ Y') (p' : Y' ⟶ T)
  (a : X' ⟶ X) (c : Y' ⟶ Y) (b : T ⟶ S)
  [IsOpenImmersion j] [IsOpenImmersion j']
  (hj : IsPullback a j' j c) (hp : IsPullback c p' p b)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wY'} (ModuleSheaf Y' Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]

/-- Paste the actual unbounded proper exchange with the original exact open comparison. -/
def moduleUnboundedCompactifiedBaseChangeMap :
    (moduleUnboundedDerivedLowerShriek j Λ ⋙ moduleUnboundedDerivedDirectImage Λ p) ⋙
        moduleUnboundedDerivedInverseImage Λ b ⟶
      moduleUnboundedDerivedInverseImage Λ a ⋙
        (moduleUnboundedDerivedLowerShriek j' Λ ⋙ moduleUnboundedDerivedDirectImage Λ p') :=
  compositeExchange (moduleUnboundedDerivedBaseChangeMap Λ p p' b c hp.w.symm)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a j' j c hj Λ)

/-- The exact component is the unchanged proper exchange followed by open base change. -/
theorem moduleUnboundedCompactifiedBaseChangeMap_app
    (K : DerivedCategory (ModuleSheaf X Λ)) :
    (moduleUnboundedCompactifiedBaseChangeMap j p j' p' a c b hj hp Λ).app K =
      (moduleUnboundedDerivedBaseChangeMap Λ p p' b c hp.w.symm).app
          ((moduleUnboundedDerivedLowerShriek j Λ).obj K) ≫
        (moduleUnboundedDerivedDirectImage Λ p').map
          ((moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a j' j c hj Λ).hom.app K) :=
  compositeExchange_app _ _ K

/-- Actual unbounded proper base change makes this same natural transformation invertible. -/
theorem moduleUnboundedCompactifiedBaseChangeMap_isIso [IsProper p]
    (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0) :
    IsIso (moduleUnboundedCompactifiedBaseChangeMap j p j' p' a c b hj hp Λ) := by
  let := Proper.properModuleUnboundedDerivedBaseChange_isIso Λ p p' b c hp N hN hΛ
  have hK (K : DerivedCategory (ModuleSheaf X Λ)) :
      IsIso ((moduleUnboundedCompactifiedBaseChangeMap j p j' p' a c b hj hp Λ).app K) := by
    rw [moduleUnboundedCompactifiedBaseChangeMap_app]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The isomorphism has precisely the original compactified exchange as its forward map. -/
def moduleUnboundedCompactifiedBaseChangeIso [IsProper p]
    (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0) :
    (moduleUnboundedDerivedLowerShriek j Λ ⋙ moduleUnboundedDerivedDirectImage Λ p) ⋙
        moduleUnboundedDerivedInverseImage Λ b ≅
      moduleUnboundedDerivedInverseImage Λ a ⋙
        (moduleUnboundedDerivedLowerShriek j' Λ ⋙ moduleUnboundedDerivedDirectImage Λ p') := by
  letI := moduleUnboundedCompactifiedBaseChangeMap_isIso j p j' p' a c b hj hp Λ N hN hΛ
  exact asIso (moduleUnboundedCompactifiedBaseChangeMap j p j' p' a c b hj hp Λ)

/-- No alternative map is introduced by the invertibility proof. -/
theorem moduleUnboundedCompactifiedBaseChangeIso_hom [IsProper p]
    (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0) :
    (moduleUnboundedCompactifiedBaseChangeIso j p j' p' a c b hj hp Λ N hN hΛ).hom =
      moduleUnboundedCompactifiedBaseChangeMap j p j' p' a c b hj hp Λ := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
