/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.MixedMatePastingCube
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.Mate
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.OpenComparisonCube

/-! # Arbitrary base change of the original proper/open mate

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
theorem moduleOpenComparison_totalTransport :
    MixedMateTotalTransport
      (moduleDerivedLowerShriekCartesianBaseChangeIso g i j f h Λ)
      (moduleDerivedLowerShriekCartesianBaseChangeIso g' i j f' h' Λ)
      (eqToIso (congrArg (fun k => moduleDerivedInverseImage Λ k) hg))
      (eqToIso (congrArg (fun k => moduleDerivedInverseImage Λ k) hf)) := by
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
theorem moduleOpenComparison_baseChange_leftCube :
    MixedMateLeftCube
      (moduleDerivedInverseImageSquareIso Λ g g' a c hg).hom
      (moduleDerivedInverseImageSquareIso Λ f f' b d hf).hom
      (moduleDerivedLowerShriekCartesianBaseChangeIso g i j f h Λ).hom
      (moduleDerivedLowerShriekCartesianBaseChangeIso g' i' j' f' h' Λ).hom
      (moduleDerivedLowerShriekCartesianBaseChangeIso a j' j b hj Λ)
      (moduleDerivedLowerShriekCartesianBaseChangeIso c i' i d hi Λ) := by
  exact mixedMateLeftCube_of_pasting
    (moduleDerivedInverseImageSquareIso Λ g g' a c hg)
    (moduleDerivedInverseImageSquareIso Λ f f' b d hf)
    (moduleDerivedLowerShriekCartesianBaseChangeIso g i j f h Λ).hom
    (moduleDerivedLowerShriekCartesianBaseChangeIso g' i' j' f' h' Λ).hom
    (moduleDerivedLowerShriekCartesianBaseChangeIso a j' j b hj Λ)
    (moduleDerivedLowerShriekCartesianBaseChangeIso c i' i d hi Λ)
    (moduleDerivedLowerShriekCartesianBaseChangeIso (c ≫ g) i' j (d ≫ f)
      (hi.paste_horiz h) Λ)
    (moduleDerivedLowerShriekCartesianBaseChangeIso (g' ≫ a) i' j (f' ≫ b)
      (h'.paste_horiz hj) Λ)
    (moduleDerivedInverseImageCompIso Λ g c)
    (moduleDerivedInverseImageCompIso Λ a g')
    (moduleDerivedInverseImageCompIso Λ f d)
    (moduleDerivedInverseImageCompIso Λ b f')
    (eqToIso (congrArg (fun k => moduleDerivedInverseImage Λ k) hg))
    (eqToIso (congrArg (fun k => moduleDerivedInverseImage Λ k) hf)) rfl rfl
    (moduleDerivedOpenComparison_pasting j i i' g c f d h hi (hi.paste_horiz h) Λ)
    (moduleDerivedOpenComparison_pasting j j' i' a g' b f' hj h'
      (h'.paste_horiz hj) Λ)
    (moduleOpenComparison_totalTransport j i' (c ≫ g) (g' ≫ a) (d ≫ f) (f' ≫ b)
      hg hf (hi.paste_horiz h) (h'.paste_horiz hj) Λ)

/-- Arbitrary base change commutes with the original global proper/open mate.
The two vertical exchanges remain the original derived base-change maps. -/
theorem moduleProperOpenMate_baseChange :
    MixedMateBaseChangeEquation
      (moduleDerivedBaseChangeMap Λ g g' a c hg)
      (moduleDerivedBaseChangeMap Λ f f' b d hf)
      (moduleProperOpenMate Λ j i g f h)
      (moduleProperOpenMate Λ j' i' g' f' h')
      (moduleDerivedLowerShriekCartesianBaseChangeIso a j' j b hj Λ)
      (moduleDerivedLowerShriekCartesianBaseChangeIso c i' i d hi Λ) := by
  exact mixedMateBaseChange_of_leftCube
    (moduleDerivedAdjunction Λ g) (moduleDerivedAdjunction Λ f)
    (moduleDerivedAdjunction Λ g') (moduleDerivedAdjunction Λ f')
    (moduleDerivedInverseImageSquareIso Λ g g' a c hg).hom
    (moduleDerivedInverseImageSquareIso Λ f f' b d hf).hom
    (moduleDerivedLowerShriekCartesianBaseChangeIso g i j f h Λ).hom
    (moduleDerivedLowerShriekCartesianBaseChangeIso g' i' j' f' h' Λ).hom
    (moduleDerivedLowerShriekCartesianBaseChangeIso a j' j b hj Λ)
    (moduleDerivedLowerShriekCartesianBaseChangeIso c i' i d hi Λ)
    (moduleDerivedBaseChangeMap Λ g g' a c hg)
    (moduleDerivedBaseChangeMap Λ f f' b d hf)
    (moduleProperOpenMate Λ j i g f h)
    (moduleProperOpenMate Λ j' i' g' f' h') rfl rfl rfl rfl
    (moduleOpenComparison_baseChange_leftCube j i g f j' i' g' f' a c b d
      h h' hj hi hg hf Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
