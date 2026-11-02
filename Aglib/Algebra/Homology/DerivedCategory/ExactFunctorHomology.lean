/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Original exact localization commutes with unbounded homology -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor
universe u v u' v' dA dB
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{dA} A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{dB} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Termwise mapping uses the original homology comparison of short complexes. -/
def mapCochainComplexHomologyIso (n : ℤ) :
    F.mapHomologicalComplex (.up ℤ) ⋙ HomologicalComplex.homologyFunctor B (.up ℤ) n ≅
      HomologicalComplex.homologyFunctor A (.up ℤ) n ⋙ F :=
  NatIso.ofComponents (fun K => (K.sc n).mapHomologyIso F) (fun f => by
    exact (ShortComplex.homologyFunctorIso F).hom.naturality
      ((HomologicalComplex.shortComplexFunctor A (.up ℤ) n).map f))

/-- The native exact functor on unbounded derived categories retains the original
localization factor and the original homology comparison. -/
def mapDerivedCategoryHomologyIso (n : ℤ) :
    F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor B n ≅
      DerivedCategory.homologyFunctor A n ⋙ F := by
  apply (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) B).preimageIso
  exact (associator _ _ _).symm ≪≫
    isoWhiskerRight F.mapDerivedCategoryFactors _ ≪≫
    associator _ _ _ ≪≫
    isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors B n) ≪≫
    F.mapCochainComplexHomologyIso n ≪≫
    isoWhiskerRight (DerivedCategory.homologyFunctorFactors A n).symm F ≪≫
    associator _ _ _

end CategoryTheory.Functor
