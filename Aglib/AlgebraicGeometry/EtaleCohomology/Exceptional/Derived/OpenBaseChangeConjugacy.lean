/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.OpenBaseChange
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.DerivedConjugacy
public import Aglib.CategoryTheory.Adjunction.LeftAdjointComparison

/-!
# The original derived Cartesian exchange and its lower-shriek mate

Both comparisons are derived from the original ordinary maps. Their conjugacy
uses the generic compatibility of deriving with composite adjunctions, not a
new choice of a right exchange or a replacement lower-shriek comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wV wU wY wX

variable {V U Y X : Scheme.{u}} (g : V ⟶ U) (i : V ⟶ Y) (j : U ⟶ X) (f : Y ⟶ X)
  [Etale i] [Etale j] (h : IsPullback g i j f) (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wV} (ModuleSheaf V Λ)]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]

local instance : (moduleInverseImage i Λ).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (moduleLowerShriekAdjunction i Λ)

/-- Native deriving of the original Cartesian right-adjoint exchange. -/
def moduleDerivedCartesianExchangeIso :
    moduleDerivedDirectImage Λ f ⋙ moduleDerivedInverseImage Λ j ≅
      moduleDerivedInverseImage Λ i ⋙ moduleDerivedDirectImage Λ g :=
  (Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives
      (moduleDirectImage f Λ) (moduleInverseImage j Λ)).symm ≪≫
    (moduleDirectImage f Λ ⋙ moduleInverseImage j Λ).rightDerivedFunctorPlusIso
      (moduleCartesianExchangeIso g i j f h Λ) ≪≫
    Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives
      (moduleInverseImage i Λ) (moduleDirectImage g Λ)

/-- The independently derived original exchanges remain conjugate under the
installed composite adjunctions. -/
theorem conjugateEquiv_moduleDerivedLowerShriekCartesianBaseChangeIso_hom :
    conjugateEquiv
        ((moduleDerivedAdjunction Λ g).comp (moduleDerivedLowerShriekAdjunction i Λ))
        ((moduleDerivedLowerShriekAdjunction j Λ).comp (moduleDerivedAdjunction Λ f))
        (moduleDerivedLowerShriekCartesianBaseChangeIso g i j f h Λ).hom =
      (moduleDerivedCartesianExchangeIso g i j f h Λ).inv := by
  let adj₀ := (moduleLowerShriekAdjunction j Λ).comp (moduleInverseImageAdjunction f Λ)
  let c := Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology
    (moduleLowerShriek j Λ) (moduleInverseImage f Λ)
  let d := Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives
    (moduleDirectImage f Λ) (moduleInverseImage j Λ)
  have hs : conjugateEquiv
      ((moduleDerivedLowerShriekAdjunction j Λ).comp (moduleDerivedAdjunction Λ f))
      adj₀.rightDerivedFunctorPlus c.hom = d.inv := by
    dsimp only [moduleDerivedLowerShriekAdjunction, moduleDerivedAdjunction, c, d]
    simpa only [Iso.refl_symm, Functor.rightDerivedFunctorPlusIso_refl, Iso.refl_trans] using
      Adjunction.rightDerivedFunctorPlus_conjugate_comp
        (moduleLowerShriekAdjunction j Λ) (moduleInverseImageAdjunction f Λ) adj₀
        (Iso.refl _) (Iso.refl _)
        (conjugateEquiv_id adj₀)
  have ho : conjugateEquiv
      ((moduleInverseImageAdjunction g Λ).comp (moduleLowerShriekAdjunction i Λ)) adj₀
      (moduleLowerShriekCartesianBaseChangeIso g i j f h Λ).hom =
      (moduleCartesianExchangeIso g i j f h Λ).inv :=
    conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom adj₀
      ((moduleInverseImageAdjunction g Λ).comp (moduleLowerShriekAdjunction i Λ))
      (moduleCartesianExchangeIso g i j f h Λ)
  have ht := Adjunction.rightDerivedFunctorPlus_conjugate_comp
    (moduleInverseImageAdjunction g Λ) (moduleLowerShriekAdjunction i Λ) adj₀
    (moduleLowerShriekCartesianBaseChangeIso g i j f h Λ)
    (moduleCartesianExchangeIso g i j f h Λ).symm ho
  simp only [Iso.trans_hom] at ht
  apply (cancel_mono d.inv).mp
  rw [← hs, conjugateEquiv_comp]
  have hc := congrArg Iso.hom
    (moduleDerivedLowerShriekCartesianBaseChangeIso_fac g i j f h Λ)
  simp only [Iso.trans_hom] at hc
  rw [hc]
  simp only [moduleDerivedAdjunction, moduleDerivedLowerShriekAdjunction] at hs ⊢
  rw [ht, hs]
  simp only [moduleDerivedCartesianExchangeIso, Iso.trans_inv, Iso.symm_inv,
    Iso.symm_symm_eq, Category.assoc, d, Iso.hom_inv_id, Category.comp_id]

/-- The derived Cartesian comparison retains the original composite-adjunction unit. -/
@[reassoc]
theorem moduleDerivedLowerShriekCartesianBaseChangeIso_adjunction_unit
    (K : DerivedCategory.Plus (ModuleSheaf U Λ)) :
    ((moduleDerivedLowerShriekAdjunction j Λ).comp (moduleDerivedAdjunction Λ f)).unit.app K ≫
        (moduleDerivedInverseImage Λ j).map ((moduleDerivedDirectImage Λ f).map
          ((moduleDerivedLowerShriekCartesianBaseChangeIso g i j f h Λ).hom.app K)) ≫
        (moduleDerivedCartesianExchangeIso g i j f h Λ).hom.app
          ((moduleDerivedLowerShriek i Λ).obj ((moduleDerivedInverseImage Λ g).obj K)) =
      ((moduleDerivedAdjunction Λ g).comp (moduleDerivedLowerShriekAdjunction i Λ)).unit.app K := by
  have hu := unit_conjugateEquiv
    ((moduleDerivedAdjunction Λ g).comp (moduleDerivedLowerShriekAdjunction i Λ))
    ((moduleDerivedLowerShriekAdjunction j Λ).comp (moduleDerivedAdjunction Λ f))
    (moduleDerivedLowerShriekCartesianBaseChangeIso g i j f h Λ).hom K
  rw [conjugateEquiv_moduleDerivedLowerShriekCartesianBaseChangeIso_hom] at hu
  simpa only [Functor.comp_obj, Functor.comp_map, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id] using
    (congrArg (fun a => a ≫ (moduleDerivedCartesianExchangeIso g i j f h Λ).hom.app
      ((moduleDerivedLowerShriek i Λ).obj ((moduleDerivedInverseImage Λ g).obj K))) hu).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
