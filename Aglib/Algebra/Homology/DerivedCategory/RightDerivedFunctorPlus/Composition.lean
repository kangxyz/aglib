/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Aglib.Algebra.Homology.CochainComplexPlus.Functoriality
public import Mathlib.Algebra.Homology.FullSubcategory
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
/-! # Composition comparisons for the original bounded-below right-derived units -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe v u v' u' v'' u''
namespace CategoryTheory.Functor
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory A] [EnoughInjectives A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory B]
  (F : A ⥤ B) [F.Additive]

omit [HasDerivedCategory A] [EnoughInjectives A] in
/-- A functor preserving homology inverts the original quasi-isomorphisms after localization. -/
theorem mapCochainComplexPlus_inverts [F.PreservesHomology] :
    (CochainComplex.Plus.quasiIso A).IsInvertedBy
      (F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q) := by
  intro K L f hf
  let : QuasiIso f.hom := hf
  exact Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso B)
    (F.mapCochainComplexPlus.map f) (show QuasiIso ((F.mapHomologicalComplex _).map f.hom) from
      inferInstance)

/-- Homology preservation makes the original bounded-below derived unit invertible everywhere. -/
theorem isIso_rightDerivedFunctorPlusUnit_of_preservesHomology [F.PreservesHomology] :
    IsIso F.rightDerivedFunctorPlusUnit :=
  isIso_of_isRightDerivedFunctor_of_inverts F.rightDerivedFunctorPlus
    F.rightDerivedFunctorPlusUnit (mapCochainComplexPlus_inverts F)

/-- The original derived unit is invertible on any actual termwise-injective bounded-below complex.
-/
theorem isIso_rightDerivedFunctorPlusUnit_of_injective (K : CochainComplex.Plus A)
    (hK : ∀ n, Injective (K.obj.X n)) : IsIso (F.rightDerivedFunctorPlusUnit.app K) := by
  let J : CochainComplex (InjectiveObject A) ℤ := K.obj.liftObjectProperty (isInjective A) hK
  obtain ⟨n, hn⟩ := K.property
  have hJ : J.IsStrictlyGE n := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero]
    apply ObjectProperty.hom_ext
    exact (CochainComplex.isZero_of_isStrictlyGE K.obj n i hi).eq_of_src _ _
  let Jplus : CochainComplex.Plus (InjectiveObject A) := ⟨J, n, hJ⟩
  exact inferInstanceAs (IsIso (F.rightDerivedFunctorPlusUnit.app
    ((InjectiveObject.ι A).mapCochainComplexPlus.obj Jplus)))

/-- An original additive-functor isomorphism induces the canonical isomorphism of its actual
bounded-below right-derived functors. -/
def rightDerivedFunctorPlusIso {F' : A ⥤ B} [F'.Additive] (e : F ≅ F') :
    F.rightDerivedFunctorPlus ≅ F'.rightDerivedFunctorPlus :=
  rightDerivedNatIso _ _ F.rightDerivedFunctorPlusUnit F'.rightDerivedFunctorPlusUnit
    (CochainComplex.Plus.quasiIso A)
    (isoWhiskerRight (NatIso.mapCochainComplexPlus e) DerivedCategory.Plus.Q)

/-- The derived functor-isomorphism comparison retains the original unit square. -/
lemma rightDerivedFunctorPlusIso_hom_app {F' : A ⥤ B} [F'.Additive]
    (e : F ≅ F') (K : CochainComplex.Plus A) :
    F.rightDerivedFunctorPlusUnit.app K ≫
        (rightDerivedFunctorPlusIso F e).hom.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map ((NatIso.mapCochainComplexPlus e).hom.app K) ≫
        F'.rightDerivedFunctorPlusUnit.app K :=
  rightDerivedNatTrans_app F.rightDerivedFunctorPlus F'.rightDerivedFunctorPlus
    F.rightDerivedFunctorPlusUnit F'.rightDerivedFunctorPlusUnit
    (CochainComplex.Plus.quasiIso A)
    (isoWhiskerRight (NatIso.mapCochainComplexPlus e) DerivedCategory.Plus.Q).hom K

variable {C : Type u''} [Category.{v''} C] [Abelian C] [HasDerivedCategory C]
  [EnoughInjectives B] (G : B ⥤ C) [G.Additive]

/-- The comparison unit for composing the original two bounded-below derived functors. -/
def rightDerivedFunctorPlusCompUnit :
    (F ⋙ G).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶
      DerivedCategory.Plus.Q ⋙ (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus) :=
  whiskerRight (mapCochainComplexPlusCompIso F G).hom _ ≫
    (associator _ _ _).hom ≫ whiskerLeft _ G.rightDerivedFunctorPlusUnit ≫
    (associator _ _ _).inv ≫ whiskerRight F.rightDerivedFunctorPlusUnit _ ≫
    (associator _ _ _).hom

/-- The composite unit retains the actual unit of each functor in its original order. -/
lemma rightDerivedFunctorPlusCompUnit_app (K : CochainComplex.Plus A) :
    (rightDerivedFunctorPlusCompUnit F G).app K =
      G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K) := by
  simp [rightDerivedFunctorPlusCompUnit, mapCochainComplexPlusCompIso]

/-- Composition computes the original derived composite when the first functor preserves
injective objects. -/
theorem isRightDerivedFunctor_comp_of_preservesInjectiveObjects [F.PreservesInjectiveObjects] :
    (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus).IsRightDerivedFunctor
      (rightDerivedFunctorPlusCompUnit F G) (CochainComplex.Plus.quasiIso A) := by
  apply (CochainComplex.Plus.localizerMorphism_derives_mapCochainComplexPlus
    (F ⋙ G)).isRightDerivedFunctor_of_isIso
  intro J
  rw [rightDerivedFunctorPlusCompUnit_app]
  change IsIso (G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj
    ((InjectiveObject.ι A).mapCochainComplexPlus.obj J)) ≫
    G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app
      ((InjectiveObject.ι A).mapCochainComplexPlus.obj J)))
  have : IsIso (G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj
      ((InjectiveObject.ι A).mapCochainComplexPlus.obj J))) := by
    apply isIso_rightDerivedFunctorPlusUnit_of_injective
    intro n
    change Injective (F.obj ((InjectiveObject.ι A).obj (J.obj.X n)))
    infer_instance
  infer_instance

/-- Composition computes the original derived composite when the second functor preserves
homology. -/
theorem isRightDerivedFunctor_comp_of_preservesHomology [G.PreservesHomology] :
    (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus).IsRightDerivedFunctor
      (rightDerivedFunctorPlusCompUnit F G) (CochainComplex.Plus.quasiIso A) := by
  apply (CochainComplex.Plus.localizerMorphism_derives_mapCochainComplexPlus
    (F ⋙ G)).isRightDerivedFunctor_of_isIso
  intro J
  rw [rightDerivedFunctorPlusCompUnit_app]
  change IsIso (G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj
    ((InjectiveObject.ι A).mapCochainComplexPlus.obj J)) ≫
    G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app
      ((InjectiveObject.ι A).mapCochainComplexPlus.obj J)))
  let := isIso_rightDerivedFunctorPlusUnit_of_preservesHomology G
  infer_instance

/-- The canonical derived composition comparison when the first functor preserves injectives. -/
def rightDerivedFunctorPlusCompIsoOfPreservesInjectives [F.PreservesInjectiveObjects] :
    (F ⋙ G).rightDerivedFunctorPlus ≅ F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus := by
  let := isRightDerivedFunctor_comp_of_preservesInjectiveObjects F G
  exact rightDerivedUnique _ _ (F ⋙ G).rightDerivedFunctorPlusUnit
    (rightDerivedFunctorPlusCompUnit F G) (CochainComplex.Plus.quasiIso A)

/-- The canonical derived composition comparison when the second functor preserves homology. -/
def rightDerivedFunctorPlusCompIsoOfPreservesHomology [G.PreservesHomology] :
    (F ⋙ G).rightDerivedFunctorPlus ≅ F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus := by
  let := isRightDerivedFunctor_comp_of_preservesHomology F G
  exact rightDerivedUnique _ _ (F ⋙ G).rightDerivedFunctorPlusUnit
    (rightDerivedFunctorPlusCompUnit F G) (CochainComplex.Plus.quasiIso A)

/-- The injective-preservation comparison satisfies the original composite-unit equation. -/
lemma rightDerivedFunctorPlusCompIsoOfPreservesInjectives_hom_app
    [F.PreservesInjectiveObjects] (K : CochainComplex.Plus A) :
    (F ⋙ G).rightDerivedFunctorPlusUnit.app K ≫
        (rightDerivedFunctorPlusCompIsoOfPreservesInjectives F G).hom.app
          (DerivedCategory.Plus.Q.obj K) =
      G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K) := by
  let := isRightDerivedFunctor_comp_of_preservesInjectiveObjects F G
  simpa only [rightDerivedFunctorPlusCompIsoOfPreservesInjectives, rightDerivedUnique,
    rightDerivedNatIso_hom,
    Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    rightDerivedFunctorPlusCompUnit_app] using
    rightDerivedNatTrans_app (F ⋙ G).rightDerivedFunctorPlus
      (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus)
      (F ⋙ G).rightDerivedFunctorPlusUnit (rightDerivedFunctorPlusCompUnit F G)
      (CochainComplex.Plus.quasiIso A) (𝟙 _) K

/-- The homology-preservation comparison satisfies the original composite-unit equation. -/
lemma rightDerivedFunctorPlusCompIsoOfPreservesHomology_hom_app
    [G.PreservesHomology] (K : CochainComplex.Plus A) :
    (F ⋙ G).rightDerivedFunctorPlusUnit.app K ≫
        (rightDerivedFunctorPlusCompIsoOfPreservesHomology F G).hom.app
          (DerivedCategory.Plus.Q.obj K) =
      G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K) := by
  let := isRightDerivedFunctor_comp_of_preservesHomology F G
  simpa only [rightDerivedFunctorPlusCompIsoOfPreservesHomology, rightDerivedUnique,
    rightDerivedNatIso_hom,
    Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    rightDerivedFunctorPlusCompUnit_app] using
    rightDerivedNatTrans_app (F ⋙ G).rightDerivedFunctorPlus
      (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus)
      (F ⋙ G).rightDerivedFunctorPlusUnit (rightDerivedFunctorPlusCompUnit F G)
      (CochainComplex.Plus.quasiIso A) (𝟙 _) K

end CategoryTheory.Functor
