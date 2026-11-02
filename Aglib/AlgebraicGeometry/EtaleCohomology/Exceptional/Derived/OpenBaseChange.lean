/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Open
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleCartesianBaseChange
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Comparison

/-!
# General Cartesian base change for the original derived module lower shriek

The comparison is the native derived image of the original ordinary Cartesian
comparison, transported through the installed exact composition isomorphisms.
It applies to etale maps, hence in particular to open immersions, with arbitrary
coefficient rings and independent derived models at all four corners.
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

/-- The original Cartesian lower-shriek comparison on the installed bounded-below
module derived categories. -/
def moduleDerivedLowerShriekCartesianBaseChangeIso :
    moduleDerivedLowerShriek j Λ ⋙ moduleDerivedInverseImage Λ f ≅
      moduleDerivedInverseImage Λ g ⋙ moduleDerivedLowerShriek i Λ :=
  (Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology
      (moduleLowerShriek j Λ) (moduleInverseImage f Λ)).symm ≪≫
    (moduleLowerShriek j Λ ⋙ moduleInverseImage f Λ).rightDerivedFunctorPlusIso
      (moduleLowerShriekCartesianBaseChangeIso g i j f h Λ) ≪≫
    Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology
      (moduleInverseImage g Λ) (moduleLowerShriek i Λ)

/-- After the installed source comparison, the derived Cartesian map is exactly
the native derived image of the original ordinary adjunction-mate comparison. -/
theorem moduleDerivedLowerShriekCartesianBaseChangeIso_fac :
    Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology
        (moduleLowerShriek j Λ) (moduleInverseImage f Λ) ≪≫
      moduleDerivedLowerShriekCartesianBaseChangeIso g i j f h Λ =
    (moduleLowerShriek j Λ ⋙ moduleInverseImage f Λ).rightDerivedFunctorPlusIso
        (moduleLowerShriekCartesianBaseChangeIso g i j f h Λ) ≪≫
      Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology
        (moduleInverseImage g Λ) (moduleLowerShriek i Λ) := by
  simp only [moduleDerivedLowerShriekCartesianBaseChangeIso, Iso.self_symm_id_assoc]

/-- The comparison retains the actual ordinary Cartesian map on complexes through
the original right-derived units, rather than an independently chosen isomorphism. -/
@[reassoc]
theorem moduleDerivedLowerShriekCartesianBaseChangeIso_unit_fac
    (K : CochainComplex.Plus (ModuleSheaf U Λ)) :
    (moduleLowerShriek j Λ ⋙ moduleInverseImage f Λ).rightDerivedFunctorPlusUnit.app K ≫
        (Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology
          (moduleLowerShriek j Λ) (moduleInverseImage f Λ)).hom.app
            (DerivedCategory.Plus.Q.obj K) ≫
        (moduleDerivedLowerShriekCartesianBaseChangeIso g i j f h Λ).hom.app
          (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
          ((NatIso.mapCochainComplexPlus
            (moduleLowerShriekCartesianBaseChangeIso g i j f h Λ)).hom.app K) ≫
        (moduleInverseImage g Λ ⋙ moduleLowerShriek i Λ).rightDerivedFunctorPlusUnit.app K ≫
        (Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology
          (moduleInverseImage g Λ) (moduleLowerShriek i Λ)).hom.app
            (DerivedCategory.Plus.Q.obj K) := by
  have hf := congrArg (fun e => e.hom.app (DerivedCategory.Plus.Q.obj K))
    (moduleDerivedLowerShriekCartesianBaseChangeIso_fac g i j f h Λ)
  simp only [Iso.trans_hom, NatTrans.comp_app] at hf
  rw [hf, ← Category.assoc, Functor.rightDerivedFunctorPlusIso_hom_app, Category.assoc]

end AlgebraicGeometry.Scheme.EtaleCohomology
