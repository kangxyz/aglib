/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.MixedMatePastingCube
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperOpenMate
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenComparisonPasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.InverseImageSquareComparison

/-! # Genuine unbounded arbitrary base change of the original proper/open mate

The left cube is proved from the two original open-comparison pasting laws and
actual equality transport. Taking original mates then gives the proper/open
base-change cube. No properness or invertibility of a right exchange is needed.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wU wV wX wY wU' wV' wX' wY'

section Transport

variable {U V X Y : Scheme.{u}} (j : U ⟶ X) (i : V ⟶ Y)
  [Etale j] [Etale i] (g g' : V ⟶ U) (f f' : Y ⟶ X)
  (hg : g' = g) (hf : f' = f)
  (h : IsPullback g i j f) (h' : IsPullback g' i j f')
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wV} (ModuleSheaf V Λ)]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]

/-- Actual equality of the two total geometric routes transports their original
open comparison, including both independent inverse-image equality maps. -/
theorem moduleUnboundedOpenComparison_totalTransport :
    MixedMateTotalTransport
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso g i j f h Λ)
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso g' i j f' h' Λ)
      (eqToIso (congrArg (fun k => moduleUnboundedDerivedInverseImage Λ k) hg))
      (eqToIso (congrArg (fun k => moduleUnboundedDerivedInverseImage Λ k) hf)) := by
  subst g'
  subst f'
  intro K
  simp

end Transport

variable {U V X Y U' V' X' Y' : Scheme.{u}}
  (j : U ⟶ X) (i : V ⟶ Y) (g : V ⟶ U) (f : Y ⟶ X)
  (j' : U' ⟶ X') (i' : V' ⟶ Y') (g' : V' ⟶ U') (f' : Y' ⟶ X')
  (a : U' ⟶ U) (c : V' ⟶ V) (b : X' ⟶ X) (d : Y' ⟶ Y)
  [Etale j] [Etale i] [Etale j'] [Etale i']
  (h : IsPullback g i j f) (h' : IsPullback g' i' j' f')
  (hj : IsPullback a j' j b) (hi : IsPullback c i' i d)
  (hg : g' ≫ a = c ≫ g) (hf : f' ≫ b = d ≫ f)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wV} (ModuleSheaf V Λ)]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wU'} (ModuleSheaf U' Λ)]
  [HasDerivedCategory.{wV'} (ModuleSheaf V' Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wY'} (ModuleSheaf Y' Λ)]

/-- The left cube follows from proved original pasting, not from an assumed
proper/open base-change equation. -/
theorem moduleUnboundedOpenComparison_baseChange_leftCube :
    MixedMateLeftCube
      (moduleUnboundedDerivedInverseImageSquareIso Λ g g' a c hg).hom
      (moduleUnboundedDerivedInverseImageSquareIso Λ f f' b d hf).hom
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso g i j f h Λ).hom
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso g' i' j' f' h' Λ).hom
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a j' j b hj Λ)
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso c i' i d hi Λ) := by
  exact mixedMateLeftCube_of_pasting
    (moduleUnboundedDerivedInverseImageSquareIso Λ g g' a c hg)
    (moduleUnboundedDerivedInverseImageSquareIso Λ f f' b d hf)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso g i j f h Λ).hom
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso g' i' j' f' h' Λ).hom
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a j' j b hj Λ)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso c i' i d hi Λ)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso (c ≫ g) i' j (d ≫ f)
      (hi.paste_horiz h) Λ)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso (g' ≫ a) i' j (f' ≫ b)
      (h'.paste_horiz hj) Λ)
    (moduleUnboundedDerivedInverseImageCompIso Λ g c)
    (moduleUnboundedDerivedInverseImageCompIso Λ a g')
    (moduleUnboundedDerivedInverseImageCompIso Λ f d)
    (moduleUnboundedDerivedInverseImageCompIso Λ b f')
    (eqToIso (congrArg (fun k => moduleUnboundedDerivedInverseImage Λ k) hg))
    (eqToIso (congrArg (fun k => moduleUnboundedDerivedInverseImage Λ k) hf))
    (moduleUnboundedDerivedInverseImageSquareIso_eq_comp Λ g g' a c hg)
    (moduleUnboundedDerivedInverseImageSquareIso_eq_comp Λ f f' b d hf)
    (moduleUnboundedDerivedOpenComparison_pasting j i i' g c f d h hi (hi.paste_horiz h) Λ)
    (moduleUnboundedDerivedOpenComparison_pasting j j' i' a g' b f' hj h'
      (h'.paste_horiz hj) Λ)
    (moduleUnboundedOpenComparison_totalTransport j i' (c ≫ g) (g' ≫ a) (d ≫ f) (f' ≫ b)
      hg hf (hi.paste_horiz h) (h'.paste_horiz hj) Λ)

/-- Arbitrary base change commutes with the original global proper/open mate.
The two vertical exchanges remain the original derived base-change maps. -/
theorem moduleUnboundedProperOpenMate_baseChange :
    MixedMateBaseChangeEquation
      (moduleUnboundedDerivedBaseChangeMap Λ g g' a c hg)
      (moduleUnboundedDerivedBaseChangeMap Λ f f' b d hf)
      (moduleUnboundedProperOpenMate g i j f h Λ)
      (moduleUnboundedProperOpenMate g' i' j' f' h' Λ)
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a j' j b hj Λ)
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso c i' i d hi Λ) := by
  exact mixedMateBaseChange_of_leftCube
    (moduleUnboundedDerivedAdjunction Λ g) (moduleUnboundedDerivedAdjunction Λ f)
    (moduleUnboundedDerivedAdjunction Λ g') (moduleUnboundedDerivedAdjunction Λ f')
    (moduleUnboundedDerivedInverseImageSquareIso Λ g g' a c hg).hom
    (moduleUnboundedDerivedInverseImageSquareIso Λ f f' b d hf).hom
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso g i j f h Λ).hom
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso g' i' j' f' h' Λ).hom
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a j' j b hj Λ)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso c i' i d hi Λ)
    (moduleUnboundedDerivedBaseChangeMap Λ g g' a c hg)
    (moduleUnboundedDerivedBaseChangeMap Λ f f' b d hf)
    (moduleUnboundedProperOpenMate g i j f h Λ)
    (moduleUnboundedProperOpenMate g' i' j' f' h' Λ) rfl rfl rfl rfl
    (moduleUnboundedOpenComparison_baseChange_leftCube j i g f j' i' g' f' a c b d
      h h' hj hi hg hf Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
