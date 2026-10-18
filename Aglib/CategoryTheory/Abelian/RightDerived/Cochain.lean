/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Embedding.MapExtend
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# Original right-derived objects and integer injective-resolution homology

The native natural-degree right-derived functor is computed using the
supplied original injective resolution, extended by zero to integer
cochains. The comparison retains the original right-derived comparison,
original extension homology isomorphism and actual functor/extension
complex isomorphism. It is natural for every actual resolution lift.
No derived-category structure is required.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CategoryTheory.InjectiveResolution

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  {D : Type u'} [Category.{v'} D] [Abelian D] (F : C ⥤ D) [F.Additive]
  {M N : C}

/-- The original natural-degree right-derived object is actual homology of the termwise
image of the supplied integer injective-resolution complex. -/
def isoRightDerivedObjCochain (I : InjectiveResolution M) (n : ℕ) :
    (F.rightDerived n).obj M ≅
      (((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).homology (n : ℤ)) :=
  I.isoRightDerivedObj F n ≪≫
    ((((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl).symm) ≪≫
    (homologyFunctor D (.up ℤ) (n : ℤ)).mapIso
      (I.cocomplex.mapExtendIso F ComplexShape.embeddingUpNat).symm

/-- The comparison retains the original three native factors in their actual orientations. -/
theorem isoRightDerivedObjCochain_hom (I : InjectiveResolution M) (n : ℕ) :
    (isoRightDerivedObjCochain F I n).hom =
      (I.isoRightDerivedObj F n).hom ≫
        (((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
          ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl).inv ≫
        homologyMap (I.cocomplex.mapExtendIso F ComplexShape.embeddingUpNat).inv (n : ℤ) := rfl

/-- Every actual native resolution lift gives the original coefficient map on integer
resolution homology under the original right-derived comparison. -/
@[reassoc]
theorem isoRightDerivedObjCochain_hom_naturality
    {I : InjectiveResolution M} {J : InjectiveResolution N} {f : M ⟶ N}
    (φ : InjectiveResolution.Hom I J f) (n : ℕ) :
    (F.rightDerived n).map f ≫ (isoRightDerivedObjCochain F J n).hom =
      (isoRightDerivedObjCochain F I n).hom ≫
        homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ.hom') (n : ℤ) := by
  let E₀ := ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl
  let E₁ := ((F.mapHomologicalComplex (.up ℕ)).obj J.cocomplex).extendHomologyIso
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl
  let D₀ := (homologyFunctor D (.up ℤ) (n : ℤ)).mapIso
    (I.cocomplex.mapExtendIso F ComplexShape.embeddingUpNat)
  let D₁ := (homologyFunctor D (.up ℤ) (n : ℤ)).mapIso
    (J.cocomplex.mapExtendIso F ComplexShape.embeddingUpNat)
  have hδ := congrArg ((homologyFunctor D (.up ℤ) (n : ℤ)).map)
    (I.cocomplex.mapExtendIso_hom_naturality F ComplexShape.embeddingUpNat φ.hom)
  simp only [Functor.map_comp] at hδ
  change homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ.hom') (n : ℤ) ≫ D₁.hom =
    D₀.hom ≫ homologyMap
      (HomologicalComplex.extendMap ((F.mapHomologicalComplex (.up ℕ)).map φ.hom)
        ComplexShape.embeddingUpNat) (n : ℤ) at hδ
  have hE := HomologicalComplex.extendHomologyIso_hom_naturality
    ((F.mapHomologicalComplex (.up ℕ)).map φ.hom) ComplexShape.embeddingUpNat
      (j := n) (j' := (n : ℤ)) rfl
  change homologyMap
      (HomologicalComplex.extendMap ((F.mapHomologicalComplex (.up ℕ)).map φ.hom)
        ComplexShape.embeddingUpNat) (n : ℤ) ≫ E₁.hom =
    E₀.hom ≫ homologyMap ((F.mapHomologicalComplex (.up ℕ)).map φ.hom) n at hE
  have hc : I.ι.f 0 ≫ φ.hom.f 0 = f ≫ J.ι.f 0 := by
    simpa only [CochainComplex.single₀_map_f_zero] using φ.ι_f_zero_comp_hom_f_zero
  apply (cancel_mono D₁.hom).mp
  simp only [isoRightDerivedObjCochain_hom, Category.assoc]
  change (F.rightDerived n).map f ≫ (J.isoRightDerivedObj F n).hom ≫
      E₁.inv ≫ D₁.inv ≫ D₁.hom =
    (I.isoRightDerivedObj F n).hom ≫ E₀.inv ≫ D₀.inv ≫
      homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ.hom') (n : ℤ) ≫ D₁.hom
  rw [hδ]
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_mono E₁.hom).mp
  simp only [Category.assoc]
  rw [hE]
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  exact InjectiveResolution.isoRightDerivedObj_hom_naturality f I J φ.hom hc F n

omit [EnoughInjectives C] in
/-- The original resolution's zero cycles after mapping and extending by zero to integer
cochains. A supplied resolution suffices; no global enough-injectives assumption is used. -/
def toRightDerivedZeroCochainCycles (I : InjectiveResolution M) : F.obj M ⟶
    (((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).cycles 0) :=
  I.toRightDerivedZero' F ≫
    ((((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendCyclesIso
      ComplexShape.embeddingUpNat (j := 0) (j' := 0) rfl).inv) ≫
    cyclesMap (I.cocomplex.mapExtendIso F ComplexShape.embeddingUpNat).inv 0

omit [EnoughInjectives C] in
/-- The zero-cycle arrow retains the original augmentation and integer-term comparison. -/
@[reassoc]
theorem toRightDerivedZeroCochainCycles_comp_iCycles (I : InjectiveResolution M) :
    toRightDerivedZeroCochainCycles F I ≫
        ((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).iCycles 0 =
      F.map (I.ι.f 0) ≫ F.map (I.cochainComplexXIso 0 0 rfl).inv := by
  dsimp only [toRightDerivedZeroCochainCycles]
  simp only [Category.assoc]
  erw [cyclesMap_i, extendCyclesIso_inv_iCycles_assoc,
    InjectiveResolution.toRightDerivedZero'_comp_iCycles_assoc]
  let e := I.cocomplex.mapExtendIso F ComplexShape.embeddingUpNat
  have he := I.cocomplex.mapExtendIso_hom_f_extendXIso F ComplexShape.embeddingUpNat
    (i := 0) (j := 0) rfl
  have hi := congrArg (fun k => k.f 0) e.inv_hom_id
  change e.inv.f 0 ≫ e.hom.f 0 = 𝟙 _ at hi
  have hc : e.inv.f 0 ≫ F.map (I.cochainComplexXIso 0 0 rfl).hom =
      (((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendXIso
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).hom := by
    erw [← he, ← Category.assoc, hi, Category.id_comp]
  have h :
      (((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendXIso
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫ e.inv.f 0 =
      F.map (I.cochainComplexXIso 0 0 rfl).inv := by
    apply (cancel_mono (F.map (I.cochainComplexXIso 0 0 rfl).hom)).mp
    rw [Category.assoc, hc, Iso.inv_hom_id, ← F.map_comp, Iso.inv_hom_id, F.map_id]
    rfl
  rw [h]

/-- The original transformation to the zeroth right-derived object becomes the original
zero-cycle projection under the same integer-cochain comparison. -/
@[reassoc]
theorem toRightDerivedZero_comp_isoRightDerivedObjCochain (I : InjectiveResolution M) :
    F.toRightDerivedZero.app M ≫ (I.isoRightDerivedObjCochain F 0).hom =
      toRightDerivedZeroCochainCycles F I ≫
        ((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).homologyπ 0 := by
  rw [I.toRightDerivedZero_eq F, InjectiveResolution.isoRightDerivedObjCochain_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change I.toRightDerivedZero' F ≫
      ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homologyπ 0 ≫
        (((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
          ComplexShape.embeddingUpNat (j := 0) (j' := 0) rfl).inv ≫
        homologyMap (I.cocomplex.mapExtendIso F ComplexShape.embeddingUpNat).inv 0 = _
  rw [homologyπ_extendHomologyIso_inv_assoc, homologyπ_naturality]
  simp only [toRightDerivedZeroCochainCycles, Category.assoc]
  rfl

end CategoryTheory.InjectiveResolution
