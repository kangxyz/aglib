/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.InjectiveResolution
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Homology
public import Aglib.CategoryTheory.Abelian.RightDerived.Cochain

/-!
# Native higher derived functors and homology of the derived single

The original natural-degree right-derived functor is the homology of the
installed bounded-below right-derived functor on the original degree-zero
single. The comparison retains the supplied native resolution, original
localization/homology factorization and installed derived unit. It is
independent of the supplied resolution and natural in the original coefficient.
The additional degree-zero comparison with the original functor retains
preservation of finite limits.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v u' v' w w'

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [EnoughInjectives A] {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w'} B] (F : A ⥤ B) [F.Additive]

namespace InjectiveResolution

variable {M N : A}

/-- The native supplied resolution computes homology of the installed right-derived single. -/
def isoRightDerivedSingleHomology (I : InjectiveResolution M) (n : ℕ) :
    (F.rightDerived n).obj M ≅
      (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).obj
        (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj M)) :=
  isoRightDerivedObjCochain F I n ≪≫
    ((DerivedCategory.Plus.homologyFunctorFactors (A := B) (n : ℤ)).app
      (F.mapCochainComplexPlus.obj I.cochainComplexPlus)).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).mapIso (I.rightDerivedFunctorPlusIso F)

/-- The comparison consists of the original resolution homology comparison, inverse native
localization factorization, and homology of the original derived-unit comparison. -/
theorem isoRightDerivedSingleHomology_hom (I : InjectiveResolution M) (n : ℕ) :
    (isoRightDerivedSingleHomology F I n).hom =
      (isoRightDerivedObjCochain F I n).hom ≫
        (DerivedCategory.Plus.homologyFunctorFactors (A := B) (n : ℤ)).inv.app
          (F.mapCochainComplexPlus.obj I.cochainComplexPlus) ≫
        (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).map
          (I.rightDerivedFunctorPlusIso F).hom := rfl

/-- Every original native resolution lift computes the actual coefficient map under this
comparison, including its original localization and derived-unit factors. -/
@[reassoc]
theorem isoRightDerivedSingleHomology_hom_naturality
    {I : InjectiveResolution M} {J : InjectiveResolution N} {f : M ⟶ N}
    (φ : InjectiveResolution.Hom I J f) (n : ℕ) :
    (F.rightDerived n).map f ≫ (isoRightDerivedSingleHomology F J n).hom =
      (isoRightDerivedSingleHomology F I n).hom ≫
        (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).map
          (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor A 0).map f)) := by
  let P₀ := (DerivedCategory.Plus.homologyFunctorFactors (A := B) (n : ℤ)).app
    (F.mapCochainComplexPlus.obj I.cochainComplexPlus)
  let P₁ := (DerivedCategory.Plus.homologyFunctorFactors (A := B) (n : ℤ)).app
    (F.mapCochainComplexPlus.obj J.cochainComplexPlus)
  let q := (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).map
    (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φ.mapPlus))
  let t := homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ.hom') (n : ℤ)
  have hP := (DerivedCategory.Plus.homologyFunctorFactors (A := B) (n : ℤ)).hom.naturality
    (F.mapCochainComplexPlus.map φ.mapPlus)
  change q ≫ P₁.hom = P₀.hom ≫ t at hP
  have hP' : t ≫ P₁.inv = P₀.inv ≫ q := by
    apply (cancel_mono P₁.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hP]
    simp only [Iso.inv_hom_id_assoc]
  have hR := congrArg ((DerivedCategory.Plus.homologyFunctor B (n : ℤ)).map)
    (I.rightDerivedFunctorPlusIso_naturality F φ)
  simp only [Functor.map_comp] at hR
  change q ≫ (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).map
      (J.rightDerivedFunctorPlusIso F).hom =
    (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).map
      (I.rightDerivedFunctorPlusIso F).hom ≫
    (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).map
      (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor A 0).map f)) at hR
  simp only [isoRightDerivedSingleHomology_hom, Category.assoc]
  rw [← Category.assoc, isoRightDerivedObjCochain_hom_naturality F φ n]
  simp only [Category.assoc]
  change (isoRightDerivedObjCochain F I n).hom ≫ t ≫ P₁.inv ≫
      (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).map
        (J.rightDerivedFunctorPlusIso F).hom = _
  rw [← Category.assoc t, hP']
  simp only [Category.assoc]
  rw [hR]
  rfl

end InjectiveResolution

namespace Functor

/-- The original higher right-derived functor is homology of the installed bounded-below
right-derived functor at the native degree-zero single. -/
def rightDerivedSingleHomologyIso (n : ℕ) :
    F.rightDerived n ≅ DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor B (n : ℤ) :=
  NatIso.ofComponents
    (fun M => InjectiveResolution.isoRightDerivedSingleHomology F (injectiveResolution M) n)
    (by
      intro M N f
      let φ : InjectiveResolution.Hom (injectiveResolution M) (injectiveResolution N) f :=
        ⟨InjectiveResolution.desc f _ _, by
          simpa only [CochainComplex.single₀_map_f_zero] using
            InjectiveResolution.desc_commutes_zero f (injectiveResolution N)
              (injectiveResolution M)⟩
      exact InjectiveResolution.isoRightDerivedSingleHomology_hom_naturality F φ n)

/-- Every supplied resolution gives exactly the component of the same native functor iso. -/
theorem rightDerivedSingleHomologyIso_hom_app {M : A} (I : InjectiveResolution M) (n : ℕ) :
    (rightDerivedSingleHomologyIso F n).hom.app M =
      (InjectiveResolution.isoRightDerivedSingleHomology F I n).hom := by
  let φ : InjectiveResolution.Hom (injectiveResolution M) I (𝟙 M) :=
    ⟨InjectiveResolution.desc (𝟙 M) _ _, by
      simpa only [CochainComplex.single₀_map_f_zero] using
        InjectiveResolution.desc_commutes_zero (𝟙 M) I (injectiveResolution M)⟩
  change (InjectiveResolution.isoRightDerivedSingleHomology F (injectiveResolution M) n).hom = _
  have h := InjectiveResolution.isoRightDerivedSingleHomology_hom_naturality F φ n
  simpa only [Functor.map_id, Category.id_comp, Category.comp_id] using h.symm

section Exact

variable [F.PreservesHomology]

/-- The installed derived functor of an exact functor carries the native single to the
native single of its image, through its original derived unit and actual single-complex map. -/
def rightDerivedFunctorPlusSingleIso (i : ℤ) :
    DerivedCategory.Plus.singleFunctor A i ⋙ F.rightDerivedFunctorPlus ≅
      F ⋙ DerivedCategory.Plus.singleFunctor B i := by
  letI : IsIso F.rightDerivedFunctorPlusUnit :=
    F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  let E : CochainComplex.singleFunctorPlus A i ⋙ F.mapCochainComplexPlus ≅
      F ⋙ CochainComplex.singleFunctorPlus B i :=
    NatIso.ofComponents
      (fun M => (CochainComplex.plus B).isoMk
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) i).app M))
      (by
        intro M N f
        apply ObjectProperty.hom_ext
        exact (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) i).hom.naturality f)
  exact (Functor.isoWhiskerLeft (CochainComplex.singleFunctorPlus A i)
      (asIso F.rightDerivedFunctorPlusUnit)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight E DerivedCategory.Plus.Q ≪≫ Functor.associator _ _ _

/-- The exact-single comparison retains the original installed derived unit and original
single-complex comparison, with no independently chosen derived-functor isomorphism. -/
@[reassoc]
theorem rightDerivedFunctorPlusSingleIso_unit (i : ℤ) (M : A) :
    F.rightDerivedFunctorPlusUnit.app ((CochainComplex.singleFunctorPlus A i).obj M) ≫
        (rightDerivedFunctorPlusSingleIso F i).hom.app M =
      DerivedCategory.Plus.Q.map
        (show F.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus A i).obj M) ⟶
            (CochainComplex.singleFunctorPlus B i).obj (F.obj M) from
          ObjectProperty.homMk
            ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) i).hom.app M)) := by
  let : IsIso F.rightDerivedFunctorPlusUnit :=
    F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  simp only [rightDerivedFunctorPlusSingleIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id, ← Category.assoc]
  change ((asIso F.rightDerivedFunctorPlusUnit).hom.app _ ≫
    (asIso F.rightDerivedFunctorPlusUnit).inv.app _) ≫ _ = _
  rw [Iso.hom_inv_id_app, Category.id_comp]
  rfl

end Exact

variable [PreservesFiniteLimits F]

/-- For a left exact original functor, the native derived single's degree-zero homology is
that original functor, using its original right-derived-zero comparison. -/
def rightDerivedSingleHomologyZeroIso :
    DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor B 0 ≅ F :=
  (rightDerivedSingleHomologyIso F 0).symm ≪≫ F.rightDerivedZeroIsoSelf

/-- The degree-zero comparison retains the original native right-derived-zero isomorphism. -/
@[reassoc]
theorem rightDerivedSingleHomologyZeroIso_hom_comp :
    (rightDerivedSingleHomologyIso F 0).hom ≫ (rightDerivedSingleHomologyZeroIso F).hom =
      F.rightDerivedZeroIsoSelf.hom := by
  simp only [rightDerivedSingleHomologyZeroIso, Iso.trans_hom, Iso.symm_hom,
    ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The inverse retains the original natural transformation from the original functor to R0. -/
theorem rightDerivedSingleHomologyZeroIso_inv :
    (rightDerivedSingleHomologyZeroIso F).inv =
      F.toRightDerivedZero ≫ (rightDerivedSingleHomologyIso F 0).hom := rfl

end Functor

end CategoryTheory
