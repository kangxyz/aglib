/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Homology of the derived functor of an exact functor

Source:
`Quillen/Algebra/Homology/DerivedCategory/ExactFunctorHomology.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`681d9171b7050b81d1ec930f729923d7345fc605b8709f07d276f09618b543df`.
Selected declarations: homologyFunctorFactors, mapCochainComplexPlusHomologyIso,
  rightDerivedFunctorPlusHomologyIso, rightDerivedFunctorPlusHomologyIso_unit.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
universe u v u' v'
namespace DerivedCategory.Plus
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory B]
/-- The original bounded-below homology comparison with the localization. -/
def homologyFunctorFactors (n : ℤ) :
    DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.homologyFunctor A n ≅
      CochainComplex.Plus.ι A ⋙ HomologicalComplex.homologyFunctor A (.up ℤ) n :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (DerivedCategory.Plus.QCompιIso A) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors A n)
end DerivedCategory.Plus

namespace CategoryTheory.Functor
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
/-- Exact termwise mapping retains the original homology maps of bounded-below complexes. -/
def mapCochainComplexPlusHomologyIso (n : ℤ) :
    F.mapCochainComplexPlus ⋙
        (CochainComplex.Plus.ι B ⋙ HomologicalComplex.homologyFunctor B (.up ℤ) n) ≅
      (CochainComplex.Plus.ι A ⋙ HomologicalComplex.homologyFunctor A (.up ℤ) n) ⋙ F :=
  NatIso.ofComponents (fun K => (K.obj.sc n).mapHomologyIso F) (fun f => by
    exact (ShortComplex.homologyFunctorIso F).hom.naturality
      ((HomologicalComplex.shortComplexFunctor A (.up ℤ) n).map f.hom))
variable [EnoughInjectives A]
/-- The actual derived functor of an exact functor retains its installed homology comparison. -/
def rightDerivedFunctorPlusHomologyIso (n : ℤ) :
    F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor B n ≅
      DerivedCategory.Plus.homologyFunctor A n ⋙ F := by
  let := F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  apply (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso A) B).preimageIso
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso F.rightDerivedFunctorPlusUnit).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.Plus.homologyFunctorFactors (A := B) n) ≪≫
    mapCochainComplexPlusHomologyIso F n ≪≫
    Functor.isoWhiskerRight (DerivedCategory.Plus.homologyFunctorFactors (A := A) n).symm F ≪≫
    Functor.associator _ _ _

/-- The homology comparison retains the literal installed unit and complex homology maps. -/
theorem rightDerivedFunctorPlusHomologyIso_unit (n : ℤ) (K : CochainComplex.Plus A) :
    (DerivedCategory.Plus.homologyFunctor B n).map (F.rightDerivedFunctorPlusUnit.app K) ≫
        (rightDerivedFunctorPlusHomologyIso F n).hom.app (DerivedCategory.Plus.Q.obj K) ≫
        F.map ((DerivedCategory.Plus.homologyFunctorFactors (A := A) n).hom.app K) =
      (DerivedCategory.Plus.homologyFunctorFactors (A := B) n).hom.app
          (F.mapCochainComplexPlus.obj K) ≫
        (mapCochainComplexPlusHomologyIso F n).hom.app K := by
  let := F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  let e : DerivedCategory.Plus.Q ⋙
        (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor B n) ≅
      DerivedCategory.Plus.Q ⋙ (DerivedCategory.Plus.homologyFunctor A n ⋙ F) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (asIso F.rightDerivedFunctorPlusUnit).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.Plus.homologyFunctorFactors (A := B) n) ≪≫
      mapCochainComplexPlusHomologyIso F n ≪≫
      Functor.isoWhiskerRight (DerivedCategory.Plus.homologyFunctorFactors (A := A) n).symm F ≪≫
      Functor.associator _ _ _
  have he := congrArg (fun t => t.app K)
    ((Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Plus.Q
      (CochainComplex.Plus.quasiIso A) B).map_preimage e.hom)
  change (rightDerivedFunctorPlusHomologyIso F n).hom.app
    (DerivedCategory.Plus.Q.obj K) = e.hom.app K at he
  rw [he]
  dsimp [e]
  simp only [Category.id_comp, Category.comp_id, Category.assoc,
    ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id, NatIso.isIso_inv_app]
  erw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    IsIso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
end CategoryTheory.Functor
