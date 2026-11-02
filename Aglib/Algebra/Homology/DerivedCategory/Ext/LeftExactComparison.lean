/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.RightDerived.Represented
public import Aglib.Algebra.Homology.RightDerived.Zero
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.Algebra.Category.Grp.Zero
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition.Acyclic
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ZeroComparison

/-!
# Original Ext through a left exact functor at an acyclic coefficient

Let `L : C ⥤ D` be additive and left exact. An actual natural isomorphism
`L ⋙ Hom(A,-) ≅ Hom(X,-)`, acyclicity of the images of injectives for `Hom(A,-)`,
and acyclicity of the specified coefficient under `L` give the original Ext
comparison. The construction uses the installed whole derived-composition
comparison and its original unit, then the actual acyclic-single comparison.
It assumes neither exactness of `L` nor an exact left adjoint.

The raw additive-Hom natural isomorphism uses a common Hom universe; the
category-object universes and the two Ext universes remain independent.
The derived-category implementation is fixed internally to the native standard
realization of each actual category. No model or resolution is a public input.
These are conditional categorical suppliers: native applications must prove
both acyclicity conditions, not assume the desired comparison itself.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u u' v w w'

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  {D : Type u'} [Category.{v} D] [Abelian D] [EnoughInjectives D] [HasExt.{w'} D]
  (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] (A : D)

-- One native derived realization per actual category is used only inside this comparison.
attribute [local instance] HasDerivedCategory.standard

/-- The original whole composition comparison followed by the actual acyclic-single comparison. -/
def leftExactDerivedObjIso
    (hI : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} A (L.obj I) (n + 1)))
    (B : C) (hB : ∀ n : ℕ, IsZero ((L.rightDerived (n + 1)).obj B)) :
    (L ⋙ preadditiveCoyoneda.obj (op A)).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor C 0).obj B) ≅
      (preadditiveCoyoneda.obj (op A)).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor D 0).obj (L.obj B)) := by
  have hI' : ∀ (I : C) [Injective I] (n : ℕ),
      IsZero (((preadditiveCoyoneda.obj (op A)).rightDerived (n + 1)).obj (L.obj I)) := by
    intro I _ n
    let : Subsingleton (Ext.{w'} A (L.obj I) (n + 1)) := hI I n
    let E := extRightDerivedRepresentedAddEquiv A (L.obj I) (n + 1)
    let : Subsingleton (((preadditiveCoyoneda.obj (op A)).rightDerived (n + 1)).obj
        (L.obj I)) := E.symm.injective.subsingleton
    exact AddCommGrpCat.isZero_of_subsingleton _
  exact ((rightDerivedFunctorPlusCompIsoOfAcyclic L (preadditiveCoyoneda.obj (op A)) hI').app
      ((DerivedCategory.Plus.singleFunctor C 0).obj B)) ≪≫
    (preadditiveCoyoneda.obj (op A)).rightDerivedFunctorPlus.mapIso
      (rightDerivedFunctorPlusSingleIsoOfAcyclic L B hB)

/-- The forward arrow is the original composition comparison followed by the actual single map. -/
theorem leftExactDerivedObjIso_hom
    (hI : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} A (L.obj I) (n + 1)))
    (B : C) (hB : ∀ n : ℕ, IsZero ((L.rightDerived (n + 1)).obj B)) :
    (leftExactDerivedObjIso L A hI B hB).hom =
      (rightDerivedFunctorPlusCompComparison L (preadditiveCoyoneda.obj (op A))).app
          ((DerivedCategory.Plus.singleFunctor C 0).obj B) ≫
        (preadditiveCoyoneda.obj (op A)).rightDerivedFunctorPlus.map
          (rightDerivedFunctorPlusSingleIsoOfAcyclic L B hB).hom := rfl

-- Identify native quotient-of-single objects with their original derived single objects.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Before homology evaluation, the comparison retains the original two derived units. -/
theorem leftExactDerivedObjIso_unit
    (hI : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} A (L.obj I) (n + 1)))
    (B : C) (hB : ∀ n : ℕ, IsZero ((L.rightDerived (n + 1)).obj B)) :
    (L ⋙ preadditiveCoyoneda.obj (op A)).rightDerivedFunctorPlusUnit.app
        ((CochainComplex.singleFunctorPlus C 0).obj B) ≫
        (leftExactDerivedObjIso L A hI B hB).hom =
      (preadditiveCoyoneda.obj (op A)).rightDerivedFunctorPlusUnit.app
          (L.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus C 0).obj B)) ≫
        (preadditiveCoyoneda.obj (op A)).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map
            (show L.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus C 0).obj B) ⟶
                (CochainComplex.singleFunctorPlus D 0).obj (L.obj B) from
              ObjectProperty.homMk
                ((HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).hom.app B))) := by
  let K := (CochainComplex.singleFunctorPlus C 0).obj B
  let G := preadditiveCoyoneda.obj (op A)
  have hu := rightDerivedFunctorPlusCompComparison_app L G K
  have hs := rightDerivedFunctorPlusSingleIsoOfAcyclic_unit L B hB
  rw [leftExactDerivedObjIso_hom]
  change (L ⋙ G).rightDerivedFunctorPlusUnit.app K ≫
      (rightDerivedFunctorPlusCompComparison L G).app (DerivedCategory.Plus.Q.obj K) ≫
        G.rightDerivedFunctorPlus.map (rightDerivedFunctorPlusSingleIsoOfAcyclic L B hB).hom = _
  rw [← Category.assoc, hu, Category.assoc, ← G.rightDerivedFunctorPlus.map_comp, hs]

-- Identify native quotient-of-single objects with their original derived single objects.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same comparison preserves the original normalized single units. -/
theorem leftExactDerivedObjIso_singleUnit
    (hI : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} A (L.obj I) (n + 1)))
    (B : C) (hB : ∀ n : ℕ, IsZero ((L.rightDerived (n + 1)).obj B)) :
    (L ⋙ preadditiveCoyoneda.obj (op A)).rightDerivedSingleUnit B ≫
        (leftExactDerivedObjIso L A hI B hB).hom =
      (preadditiveCoyoneda.obj (op A)).rightDerivedSingleUnit (L.obj B) := by
  let G := preadditiveCoyoneda.obj (op A)
  let K := (CochainComplex.singleFunctorPlus C 0).obj B
  let S := (CochainComplex.singleFunctorPlus D 0).obj (L.obj B)
  let T := L.mapCochainComplexPlus.obj K
  let Q := DerivedCategory.Plus.Q (C := AddCommGrpCat.{v})
  let QD := DerivedCategory.Plus.Q (C := D)
  let a : S ⟶ T := ObjectProperty.homMk
    ((HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).inv.app B)
  let b : T ⟶ S := ObjectProperty.homMk
    ((HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).hom.app B)
  let τ : (CochainComplex.singleFunctorPlus AddCommGrpCat 0).obj (G.obj (L.obj B)) ⟶
      G.mapCochainComplexPlus.obj S := ObjectProperty.homMk
    ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).inv.app (L.obj B))
  let σ : (CochainComplex.singleFunctorPlus AddCommGrpCat 0).obj (G.obj (L.obj B)) ⟶
      (L ⋙ G).mapCochainComplexPlus.obj K := ObjectProperty.homMk
    ((HomologicalComplex.singleMapHomologicalComplex (L ⋙ G) (.up ℤ) 0).inv.app B)
  have hσ : σ = τ ≫ G.mapCochainComplexPlus.map a := by
    apply ObjectProperty.hom_ext
    exact HomologicalComplex.singleMapHomologicalComplex_comp_inv_app L G (.up ℤ) 0 B
  have hab : a ≫ b = 𝟙 S := by
    apply ObjectProperty.hom_ext
    exact (HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).inv_hom_id_app B
  have hn := G.rightDerivedFunctorPlusUnit.naturality a
  change Q.map (G.mapCochainComplexPlus.map a) ≫ G.rightDerivedFunctorPlusUnit.app T =
    G.rightDerivedFunctorPlusUnit.app S ≫ G.rightDerivedFunctorPlus.map (QD.map a) at hn
  change (Q.map σ ≫ (L ⋙ G).rightDerivedFunctorPlusUnit.app K) ≫
      (leftExactDerivedObjIso L A hI B hB).hom = Q.map τ ≫ G.rightDerivedFunctorPlusUnit.app S
  rw [Category.assoc, leftExactDerivedObjIso_unit]
  change Q.map σ ≫ G.rightDerivedFunctorPlusUnit.app T ≫
      G.rightDerivedFunctorPlus.map (QD.map b) = Q.map τ ≫ G.rightDerivedFunctorPlusUnit.app S
  rw [hσ, Q.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hn, ← Functor.map_comp, ← Functor.map_comp, hab,
    Functor.map_id, Functor.map_id, Category.comp_id]

private theorem leftExactDerivedObjIso_naturality
    (hI : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} A (L.obj I) (n + 1)))
    {B B' : C} (f : B ⟶ B')
    (hB : ∀ n : ℕ, IsZero ((L.rightDerived (n + 1)).obj B))
    (hB' : ∀ n : ℕ, IsZero ((L.rightDerived (n + 1)).obj B')) :
    (L ⋙ preadditiveCoyoneda.obj (op A)).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor C 0).map f) ≫
        (leftExactDerivedObjIso L A hI B' hB').hom =
      (leftExactDerivedObjIso L A hI B hB).hom ≫
        (preadditiveCoyoneda.obj (op A)).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor D 0).map (L.map f)) := by
  dsimp only [leftExactDerivedObjIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [← Category.assoc, NatTrans.naturality, Functor.comp_map, Category.assoc,
    ← Functor.map_comp,
    rightDerivedFunctorPlusSingleIsoOfAcyclic_hom_naturality,
    Functor.map_comp, ← Category.assoc]

/-- The natural-degree Hom comparison evaluates the original whole derived comparisons. -/
def rightDerivedHomIsoOfAcyclic {X : C}
    (e : L ⋙ preadditiveCoyoneda.obj (op A) ≅ preadditiveCoyoneda.obj (op X))
    (hI : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} A (L.obj I) (n + 1)))
    (B : C) (hB : ∀ n : ℕ, IsZero ((L.rightDerived (n + 1)).obj B)) (n : ℕ) :
    ((preadditiveCoyoneda.obj (op X)).rightDerived n).obj B ≅
      ((preadditiveCoyoneda.obj (op A)).rightDerived n).obj (L.obj B) :=
  ((rightDerivedNatIsoOfAdditive e n).app B).symm ≪≫
    ((L ⋙ preadditiveCoyoneda.obj (op A)).rightDerivedSingleHomologyIso n).app B ≪≫
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat (n : ℤ)).mapIso
      (leftExactDerivedObjIso L A hI B hB) ≪≫
    (((preadditiveCoyoneda.obj (op A)).rightDerivedSingleHomologyIso n).app (L.obj B)).symm

/-- The evaluated comparison is natural on actual coefficient arrows between acyclic objects. -/
theorem rightDerivedHomIsoOfAcyclic_naturality {X : C}
    (e : L ⋙ preadditiveCoyoneda.obj (op A) ≅ preadditiveCoyoneda.obj (op X))
    (hI : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} A (L.obj I) (n + 1)))
    {B B' : C} (f : B ⟶ B')
    (hB : ∀ n : ℕ, IsZero ((L.rightDerived (n + 1)).obj B))
    (hB' : ∀ n : ℕ, IsZero ((L.rightDerived (n + 1)).obj B')) (n : ℕ) :
    ((preadditiveCoyoneda.obj (op X)).rightDerived n).map f ≫
        (rightDerivedHomIsoOfAcyclic L A e hI B' hB' n).hom =
      (rightDerivedHomIsoOfAcyclic L A e hI B hB n).hom ≫
        ((preadditiveCoyoneda.obj (op A)).rightDerived n).map (L.map f) := by
  let G := preadditiveCoyoneda.obj (op A)
  let H := DerivedCategory.Plus.homologyFunctor AddCommGrpCat (n : ℤ)
  have h₀ := (rightDerivedNatIsoOfAdditive e n).inv.naturality f
  have h₁ := ((L ⋙ G).rightDerivedSingleHomologyIso n).hom.naturality f
  have h₂ := congrArg H.map (leftExactDerivedObjIso_naturality L A hI f hB hB')
  have h₃ := (G.rightDerivedSingleHomologyIso n).inv.naturality (L.map f)
  simp only [Functor.map_comp] at h₂
  dsimp only [Functor.comp_map, G, H] at h₃
  dsimp only [rightDerivedHomIsoOfAcyclic, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom]
  simp only [Category.assoc]
  rw [reassoc_of% h₀, reassoc_of% h₁, reassoc_of% h₂, h₃]

-- Identify native quotient-of-single objects with their original derived single objects.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Degree-zero evaluation preserves the original unit and the supplied original Hom arrow. -/
theorem rightDerivedHomIsoOfAcyclic_zero_unit {X : C}
    (e : L ⋙ preadditiveCoyoneda.obj (op A) ≅ preadditiveCoyoneda.obj (op X))
    (hI : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} A (L.obj I) (n + 1)))
    (B : C) (hB : ∀ n : ℕ, IsZero ((L.rightDerived (n + 1)).obj B)) :
    (preadditiveCoyoneda.obj (op X)).toRightDerivedZero.app B ≫
        (rightDerivedHomIsoOfAcyclic L A e hI B hB 0).hom =
      e.inv.app B ≫ (preadditiveCoyoneda.obj (op A)).toRightDerivedZero.app (L.obj B) := by
  let G := preadditiveCoyoneda.obj (op A)
  let P := L ⋙ G
  let H := DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} 0
  let EP := P.rightDerivedSingleHomologyIso 0
  let EG := G.rightDerivedSingleHomologyIso 0
  let d := (DerivedCategory.singleFunctorCompHomologyFunctorIso AddCommGrpCat.{v} 0).app
    (G.obj (L.obj B))
  have hθ := congrArg H.map (leftExactDerivedObjIso_singleUnit L A hI B hB)
  simp only [CategoryTheory.Functor.map_comp] at hθ
  have hP := P.rightDerivedSingleUnit_homology B
  change d.inv ≫ H.map (P.rightDerivedSingleUnit B) =
    P.toRightDerivedZero.app B ≫ EP.hom.app B at hP
  have hG := G.rightDerivedSingleUnit_homology (L.obj B)
  change d.inv ≫ H.map (G.rightDerivedSingleUnit (L.obj B)) =
    G.toRightDerivedZero.app (L.obj B) ≫ EG.hom.app (L.obj B) at hG
  have hcomp : P.toRightDerivedZero.app B ≫ EP.hom.app B ≫
      H.map (leftExactDerivedObjIso L A hI B hB).hom =
      G.toRightDerivedZero.app (L.obj B) ≫ EG.hom.app (L.obj B) := by
    rw [← Category.assoc, ← hP, Category.assoc, hθ, hG]
  have hα : (preadditiveCoyoneda.obj (op X)).toRightDerivedZero.app B ≫
      (rightDerivedNatIsoOfAdditive e 0).inv.app B = e.inv.app B ≫ P.toRightDerivedZero.app B :=
    toRightDerivedZero_naturality e.inv B
  change (preadditiveCoyoneda.obj (op X)).toRightDerivedZero.app B ≫
      (rightDerivedNatIsoOfAdditive e 0).inv.app B ≫ EP.hom.app B ≫
        H.map (leftExactDerivedObjIso L A hI B hB).hom ≫ EG.inv.app (L.obj B) =
    e.inv.app B ≫ G.toRightDerivedZero.app (L.obj B)
  rw [reassoc_of% hα, reassoc_of% hcomp]
  simp only [Iso.hom_inv_id_app, Category.comp_id]

variable [HasExt.{w} C]

/-- Original Ext computes the image coefficient through the same chosen native comparisons. -/
def extAddEquivOfLeftExactAcyclic {X : C}
    (e : L ⋙ preadditiveCoyoneda.obj (op A) ≅ preadditiveCoyoneda.obj (op X))
    (hI : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} A (L.obj I) (n + 1)))
    (B : C) (hB : ∀ n : ℕ, IsZero ((L.rightDerived (n + 1)).obj B)) (n : ℕ) :
    Ext.{w} X B n ≃+ Ext.{w'} A (L.obj B) n :=
  (extRightDerivedRepresentedAddEquiv X B n).trans
    (((rightDerivedHomIsoOfAcyclic L A e hI B hB n).addCommGroupIsoToAddEquiv).trans
      (extRightDerivedRepresentedAddEquiv A (L.obj B) n).symm)

/-- The forward map retains the original Ext/right-derived maps and whole-comparison component. -/
theorem extAddEquivOfLeftExactAcyclic_apply {X : C}
    (e : L ⋙ preadditiveCoyoneda.obj (op A) ≅ preadditiveCoyoneda.obj (op X))
    (hI : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} A (L.obj I) (n + 1)))
    (B : C) (hB : ∀ n : ℕ, IsZero ((L.rightDerived (n + 1)).obj B)) (n : ℕ)
    (x : Ext.{w} X B n) :
    extAddEquivOfLeftExactAcyclic L A e hI B hB n x =
      (extRightDerivedRepresentedAddEquiv A (L.obj B) n).symm
        ((rightDerivedHomIsoOfAcyclic L A e hI B hB n).hom
          ((injectiveResolution B).extRightDerivedAddEquiv X n x)) := rfl

-- Keep the native represented-Hom carrier at the original degree-zero unit.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Degree zero is exactly the inverse of the original supplied Hom comparison. -/
theorem extAddEquivOfLeftExactAcyclic_mk₀ {X : C}
    (e : L ⋙ preadditiveCoyoneda.obj (op A) ≅ preadditiveCoyoneda.obj (op X))
    (hI : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} A (L.obj I) (n + 1)))
    (B : C) (hB : ∀ n : ℕ, IsZero ((L.rightDerived (n + 1)).obj B)) (f : X ⟶ B) :
    extAddEquivOfLeftExactAcyclic L A e hI B hB 0 (Ext.mk₀ f) = Ext.mk₀ (e.inv.app B f) := by
  apply (extRightDerivedRepresentedAddEquiv A (L.obj B) 0).injective
  rw [extAddEquivOfLeftExactAcyclic_apply, AddEquiv.apply_symm_apply,
    extRightDerivedRepresentedAddEquiv_mk₀, extRightDerivedRepresentedAddEquiv_mk₀]
  have h := congrArg
    (fun k : (preadditiveCoyoneda.obj (op X)).obj B ⟶
      ((preadditiveCoyoneda.obj (op A)).rightDerived 0).obj (L.obj B) => k f)
    (rightDerivedHomIsoOfAcyclic_zero_unit L A e hI B hB)
  exact h

/-- The original Ext comparison retains postcomposition by the actual coefficient morphism. -/
theorem extAddEquivOfLeftExactAcyclic_naturality {X : C}
    (e : L ⋙ preadditiveCoyoneda.obj (op A) ≅ preadditiveCoyoneda.obj (op X))
    (hI : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} A (L.obj I) (n + 1)))
    {B B' : C} (f : B ⟶ B')
    (hB : ∀ n : ℕ, IsZero ((L.rightDerived (n + 1)).obj B))
    (hB' : ∀ n : ℕ, IsZero ((L.rightDerived (n + 1)).obj B')) (n : ℕ)
    (x : Ext.{w} X B n) :
    extAddEquivOfLeftExactAcyclic L A e hI B' hB' n (x.comp (Ext.mk₀ f) (add_zero n)) =
      (extAddEquivOfLeftExactAcyclic L A e hI B hB n x).comp (Ext.mk₀ (L.map f))
        (add_zero n) := by
  apply (extRightDerivedRepresentedAddEquiv A (L.obj B') n).injective
  rw [extAddEquivOfLeftExactAcyclic_apply, AddEquiv.apply_symm_apply,
    extRightDerivedRepresentedAddEquiv_naturality,
    extRightDerivedRepresentedAddEquiv_naturality,
    extAddEquivOfLeftExactAcyclic_apply, AddEquiv.apply_symm_apply]
  exact ConcreteCategory.congr_hom
    (rightDerivedHomIsoOfAcyclic_naturality L A e hI f hB hB' n)
    ((injectiveResolution B).extRightDerivedAddEquiv X n x)

end CategoryTheory.Functor



universe v'

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [EnoughInjectives D] [HasExt.{w'} D]
  (L : C ⥤ D) [L.Additive] (A : D)

attribute [local instance] HasDerivedCategory.standard

omit [Abelian C] [EnoughInjectives C] [L.Additive] in
/-- Original positive Ext vanishing of injective images implies vanishing of their
represented right-derived objects. No additivity or exactness of the image functor is needed. -/
theorem representedDerivedImage_isZero_of_ext_subsingleton
    (hI : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} A (L.obj I) (n + 1)))
    (I : C) [Injective I] (n : ℕ) :
    IsZero (((preadditiveCoyoneda.obj (op A)).rightDerived (n + 1)).obj (L.obj I)) := by
  let : Subsingleton (Ext.{w'} A (L.obj I) (n + 1)) := hI I n
  let E := extRightDerivedRepresentedAddEquiv A (L.obj I) (n + 1)
  let : Subsingleton (((preadditiveCoyoneda.obj (op A)).rightDerived (n + 1)).obj
      (L.obj I)) := E.symm.injective.subsingleton
  exact AddCommGrpCat.isZero_of_subsingleton _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original normalized single units form a whole natural transformation for any
additive functor, before imposing exactness or coefficient acyclicity. -/
def rightDerivedSingleUnitNatTrans :
    L ⋙ DerivedCategory.Plus.singleFunctor D 0 ⟶
      DerivedCategory.Plus.singleFunctor C 0 ⋙ L.rightDerivedFunctorPlus := by
  let E : CochainComplex.singleFunctorPlus C 0 ⋙ L.mapCochainComplexPlus ≅
      L ⋙ CochainComplex.singleFunctorPlus D 0 :=
    NatIso.ofComponents
      (fun B => (CochainComplex.plus D).isoMk
        ((HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).app B))
      (by
        intro B B' f
        apply ObjectProperty.hom_ext
        exact (HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).hom.naturality f)
  exact (associator L (CochainComplex.singleFunctorPlus D 0) DerivedCategory.Plus.Q).inv ≫
    (isoWhiskerRight E DerivedCategory.Plus.Q).inv ≫
    (associator (CochainComplex.singleFunctorPlus C 0) L.mapCochainComplexPlus
      DerivedCategory.Plus.Q).hom ≫
    whiskerLeft (CochainComplex.singleFunctorPlus C 0) L.rightDerivedFunctorPlusUnit ≫
    (associator (CochainComplex.singleFunctorPlus C 0) DerivedCategory.Plus.Q
      L.rightDerivedFunctorPlus).inv

omit [EnoughInjectives D] [HasExt.{w'} D] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Each component is exactly the existing original normalized single-unit map. -/
theorem rightDerivedSingleUnitNatTrans_app (B : C) :
    (rightDerivedSingleUnitNatTrans L).app B = L.rightDerivedSingleUnit B := by
  let K := (CochainComplex.singleFunctorPlus C 0).obj B
  let a : (CochainComplex.singleFunctorPlus D 0).obj (L.obj B) ⟶
      L.mapCochainComplexPlus.obj K := ObjectProperty.homMk
    ((HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).inv.app B)
  change 𝟙 _ ≫ DerivedCategory.Plus.Q.map a ≫ 𝟙 _ ≫
      L.rightDerivedFunctorPlusUnit.app K ≫ 𝟙 _ =
    DerivedCategory.Plus.Q.map a ≫ L.rightDerivedFunctorPlusUnit.app K
  simp only [Category.id_comp, Category.comp_id]

/-- The canonical reverse comparison exists as a whole natural transformation without
acyclicity of the individual coefficient. It uses the original single unit followed by
the inverse original derived-composition comparison. -/
def leftExactDerivedReverse
    (hI : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} A (L.obj I) (n + 1))) :
    L ⋙ DerivedCategory.Plus.singleFunctor D 0 ⋙
        (preadditiveCoyoneda.obj (op A)).rightDerivedFunctorPlus ⟶
      DerivedCategory.Plus.singleFunctor C 0 ⋙
        (L ⋙ preadditiveCoyoneda.obj (op A)).rightDerivedFunctorPlus :=
  (associator L (DerivedCategory.Plus.singleFunctor D 0)
    (preadditiveCoyoneda.obj (op A)).rightDerivedFunctorPlus).inv ≫
    whiskerRight (rightDerivedSingleUnitNatTrans L)
      (preadditiveCoyoneda.obj (op A)).rightDerivedFunctorPlus ≫
    (associator (DerivedCategory.Plus.singleFunctor C 0) L.rightDerivedFunctorPlus
      (preadditiveCoyoneda.obj (op A)).rightDerivedFunctorPlus).hom ≫
    whiskerLeft (DerivedCategory.Plus.singleFunctor C 0)
      (rightDerivedFunctorPlusCompIsoOfAcyclic L (preadditiveCoyoneda.obj (op A))
        (representedDerivedImage_isZero_of_ext_subsingleton L A hI)).inv

private theorem leftExactDerivedReverse_app
    (hI : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} A (L.obj I) (n + 1)))
    (B : C) :
    (leftExactDerivedReverse L A hI).app B =
      (preadditiveCoyoneda.obj (op A)).rightDerivedFunctorPlus.map (L.rightDerivedSingleUnit B) ≫
        (rightDerivedFunctorPlusCompIsoOfAcyclic L (preadditiveCoyoneda.obj (op A))
          (representedDerivedImage_isZero_of_ext_subsingleton L A hI)).inv.app
            ((DerivedCategory.Plus.singleFunctor C 0).obj B) := by
  simp [leftExactDerivedReverse, rightDerivedSingleUnitNatTrans_app]

/-- The reverse arrow is characterized by the original derived unit and composition comparison. -/
@[reassoc]
theorem leftExactDerivedReverse_app_comp_comparison
    (hI : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} A (L.obj I) (n + 1)))
    (B : C) :
    (leftExactDerivedReverse L A hI).app B ≫
        (rightDerivedFunctorPlusCompComparison L (preadditiveCoyoneda.obj (op A))).app
          ((DerivedCategory.Plus.singleFunctor C 0).obj B) =
      (preadditiveCoyoneda.obj (op A)).rightDerivedFunctorPlus.map
        (L.rightDerivedSingleUnit B) := by
  rw [leftExactDerivedReverse_app, Category.assoc]
  let E := rightDerivedFunctorPlusCompIsoOfAcyclic L (preadditiveCoyoneda.obj (op A))
    (representedDerivedImage_isZero_of_ext_subsingleton L A hI)
  change _ ≫ E.inv.app _ ≫ E.hom.app _ = _
  rw [Iso.inv_hom_id_app, Category.comp_id]

/-- Naturality holds on every original coefficient arrow, without target acyclicity. -/
@[reassoc]
theorem leftExactDerivedReverse_naturality
    (hI : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} A (L.obj I) (n + 1)))
    {B B' : C} (f : B ⟶ B') :
    (preadditiveCoyoneda.obj (op A)).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor D 0).map (L.map f)) ≫
        (leftExactDerivedReverse L A hI).app B' =
      (leftExactDerivedReverse L A hI).app B ≫
        (L ⋙ preadditiveCoyoneda.obj (op A)).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor C 0).map f) :=
  (leftExactDerivedReverse L A hI).naturality f

/-- On the actual image of a termwise-injective complex, the represented derived unit is
invertible by the same original composition comparison and its unit equation. -/
theorem isIso_representedRightDerivedUnit_map_of_injective
    (hI : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} A (L.obj I) (n + 1)))
    (K : CochainComplex.Plus C) (hK : ∀ n, Injective (K.obj.X n)) :
    IsIso ((preadditiveCoyoneda.obj (op A)).rightDerivedFunctorPlusUnit.app
      (L.mapCochainComplexPlus.obj K)) := by
  let G := preadditiveCoyoneda.obj (op A)
  let : IsIso (L.rightDerivedFunctorPlusUnit.app K) :=
    L.isIso_rightDerivedFunctorPlusUnit_of_injective K hK
  let : IsIso ((L ⋙ G).rightDerivedFunctorPlusUnit.app K) :=
    (L ⋙ G).isIso_rightDerivedFunctorPlusUnit_of_injective K hK
  let : IsIso (rightDerivedFunctorPlusCompComparison L G) :=
    isIso_rightDerivedFunctorPlusCompComparison_of_acyclic L G
      (representedDerivedImage_isZero_of_ext_subsingleton L A hI)
  apply (isIso_comp_right_iff _
    (G.rightDerivedFunctorPlus.map (L.rightDerivedFunctorPlusUnit.app K))).mp
  rw [← rightDerivedFunctorPlusCompComparison_app]
  infer_instance

end CategoryTheory.Functor

namespace CategoryTheory.Functor

-- Only the existing raw-Hom forward comparison requires a common Hom universe.
variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  {D : Type u'} [Category.{v} D] [Abelian D] [EnoughInjectives D] [HasExt.{w'} D]
  (L : C ⥤ D) [L.Additive] (A : D)

attribute [local instance] HasDerivedCategory.standard

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Under actual target acyclicity, the canonical reverse map is the inverse of the
already constructed forward comparison, rather than a separately chosen equivalence. -/
theorem leftExactDerivedReverse_app_eq_inv [PreservesFiniteLimits L]
    (hI : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} A (L.obj I) (n + 1)))
    (B : C) (hB : ∀ n : ℕ, IsZero ((L.rightDerived (n + 1)).obj B)) :
    (leftExactDerivedReverse L A hI).app B = (leftExactDerivedObjIso L A hI B hB).inv := by
  rw [leftExactDerivedReverse_app]
  rfl

end CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  {D : Type u'} [Category.{v} D] [Abelian D] [EnoughInjectives D] [HasExt.{w'} D]
  (L : C ⥤ D) [L.Additive] (A : D)

attribute [local instance] HasDerivedCategory.standard

/-- Homology of the whole original reverse comparison, as a natural transformation on
every coefficient. Acyclicity of the individual coefficient is not assumed. -/
def rightDerivedRepresentedReverse
    (hI : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} A (L.obj I) (n + 1)))
    (n : ℕ) :
    L ⋙ (preadditiveCoyoneda.obj (op A)).rightDerived n ⟶
      (L ⋙ preadditiveCoyoneda.obj (op A)).rightDerived n where
  app B :=
    ((preadditiveCoyoneda.obj (op A)).rightDerivedSingleHomologyIso n).hom.app (L.obj B) ≫
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat (n : ℤ)).map
        ((leftExactDerivedReverse L A hI).app B) ≫
      ((L ⋙ preadditiveCoyoneda.obj (op A)).rightDerivedSingleHomologyIso n).inv.app B
  naturality B B' f := by
    let G := preadditiveCoyoneda.obj (op A)
    let H := DerivedCategory.Plus.homologyFunctor AddCommGrpCat (n : ℤ)
    have h₀ := (G.rightDerivedSingleHomologyIso n).hom.naturality (L.map f)
    have h₁ := congrArg H.map (leftExactDerivedReverse_naturality L A hI f)
    have h₂ := ((L ⋙ G).rightDerivedSingleHomologyIso n).inv.naturality f
    simp only [Functor.map_comp] at h₁
    dsimp only [Functor.comp_map] at h₀ h₂
    simp only [Functor.comp_map, Category.assoc]
    rw [reassoc_of% h₀, reassoc_of% h₁, h₂]

/-- The whole canonical reverse comparison in natural degree, with the actual original
Hom identification applied only after the derived-composition map. -/
def rightDerivedHomReverse {X : C}
    (e : L ⋙ preadditiveCoyoneda.obj (op A) ≅ preadditiveCoyoneda.obj (op X))
    (hI : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} A (L.obj I) (n + 1)))
    (n : ℕ) :
    L ⋙ (preadditiveCoyoneda.obj (op A)).rightDerived n ⟶
      (preadditiveCoyoneda.obj (op X)).rightDerived n :=
  rightDerivedRepresentedReverse L A hI n ≫ (rightDerivedNatIsoOfAdditive e n).hom

/-- Target acyclicity identifies this all-coefficient reverse component with the actual
inverse of the existing forward natural-degree comparison. -/
theorem rightDerivedHomReverse_app_eq_inv [PreservesFiniteLimits L] {X : C}
    (e : L ⋙ preadditiveCoyoneda.obj (op A) ≅ preadditiveCoyoneda.obj (op X))
    (hI : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} A (L.obj I) (n + 1)))
    (B : C) (hB : ∀ n : ℕ, IsZero ((L.rightDerived (n + 1)).obj B)) (n : ℕ) :
    (rightDerivedHomReverse L A e hI n).app B =
      (rightDerivedHomIsoOfAcyclic L A e hI B hB n).inv := by
  simp only [rightDerivedHomReverse, NatTrans.comp_app, rightDerivedRepresentedReverse,
    rightDerivedHomIsoOfAcyclic, Iso.trans_inv, Iso.symm_inv, Iso.app_inv, Iso.app_hom,
    Functor.mapIso_inv, Category.assoc]
  rw [leftExactDerivedReverse_app_eq_inv]

variable [HasExt.{w} C]

/-- The original natural-degree Ext reverse homomorphism is defined at every coefficient
from the canonical reverse derived map. Only injective-image acyclicity is required. -/
def extReverseOfLeftExact {X : C}
    (e : L ⋙ preadditiveCoyoneda.obj (op A) ≅ preadditiveCoyoneda.obj (op X))
    (hI : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} A (L.obj I) (n + 1)))
    (B : C) (n : ℕ) : Ext.{w'} A (L.obj B) n →+ Ext.{w} X B n :=
  (extRightDerivedRepresentedAddEquiv X B n).symm.toAddMonoidHom.comp
    (((rightDerivedHomReverse L A e hI n).app B).hom.comp
      (extRightDerivedRepresentedAddEquiv A (L.obj B) n).toAddMonoidHom)

/-- For an acyclic coefficient the all-coefficient reverse homomorphism is the original
forward equivalence's inverse, including its original Ext realization. -/
theorem extReverseOfLeftExact_eq_symm [PreservesFiniteLimits L] {X : C}
    (e : L ⋙ preadditiveCoyoneda.obj (op A) ≅ preadditiveCoyoneda.obj (op X))
    (hI : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} A (L.obj I) (n + 1)))
    (B : C) (hB : ∀ n : ℕ, IsZero ((L.rightDerived (n + 1)).obj B)) (n : ℕ) :
    extReverseOfLeftExact L A e hI B n =
      (extAddEquivOfLeftExactAcyclic L A e hI B hB n).symm.toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro x
  simp only [extReverseOfLeftExact, AddMonoidHom.comp_apply,
    AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
  rw [rightDerivedHomReverse_app_eq_inv L A e hI B hB n]
  rfl

/-- The all-coefficient reverse arrow preserves actual target maps. -/
theorem extReverseOfLeftExact_naturality {X : C}
    (e : L ⋙ preadditiveCoyoneda.obj (op A) ≅ preadditiveCoyoneda.obj (op X))
    (hI : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} A (L.obj I) (n + 1)))
    {B B' : C} (f : B ⟶ B') (n : ℕ) (x : Ext.{w'} A (L.obj B) n) :
    extReverseOfLeftExact L A e hI B' n
        (x.comp (Ext.mk₀ (L.map f)) (Nat.add_zero n)) =
      (extReverseOfLeftExact L A e hI B n x).comp (Ext.mk₀ f) (Nat.add_zero n) := by
  apply (extRightDerivedRepresentedAddEquiv X B' n).injective
  simp only [extReverseOfLeftExact, AddMonoidHom.comp_apply,
    AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
    AddEquiv.apply_symm_apply, extRightDerivedRepresentedAddEquiv_naturality]
  exact (ConcreteCategory.congr_hom
    ((rightDerivedHomReverse L A e hI n).naturality f)
    (extRightDerivedRepresentedAddEquiv A (L.obj B) n x))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Degree zero of the canonical reverse map is the original supplied Hom arrow,
for every coefficient. Only this normalization uses left exactness. -/
theorem extReverseOfLeftExact_mk₀ [PreservesFiniteLimits L] {X : C}
    (e : L ⋙ preadditiveCoyoneda.obj (op A) ≅ preadditiveCoyoneda.obj (op X))
    (hI : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} A (L.obj I) (n + 1)))
    (B : C) (f : A ⟶ L.obj B) :
    extReverseOfLeftExact L A e hI B 0 (Ext.mk₀ f) = Ext.mk₀ (e.hom.app B f) := by
  have hzero (I : C) [Injective I] (g : A ⟶ L.obj I) :
      extReverseOfLeftExact L A e hI I 0 (Ext.mk₀ g) = Ext.mk₀ (e.hom.app I g) := by
    let hI₀ : ∀ n : ℕ, IsZero ((L.rightDerived (n + 1)).obj I) :=
      fun n => L.isZero_rightDerived_obj_injective_succ n I
    rw [extReverseOfLeftExact_eq_symm L A e hI I hI₀ 0]
    change (extAddEquivOfLeftExactAcyclic L A e hI I hI₀ 0).symm (Ext.mk₀ g) = _
    apply (extAddEquivOfLeftExactAcyclic L A e hI I hI₀ 0).injective
    rw [AddEquiv.apply_symm_apply, extAddEquivOfLeftExactAcyclic_mk₀]
    apply congrArg Ext.mk₀
    have h := ConcreteCategory.congr_hom (e.hom_inv_id_app I) g
    change e.inv.app I (e.hom.app I g) = g at h
    exact h.symm
  have hinj : Function.Injective (fun x : Ext.{w} X B 0 =>
      x.comp (Ext.mk₀ (Injective.ι B)) (Nat.add_zero 0)) := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective X B).surjective x
    obtain ⟨b, rfl⟩ := (Ext.mk₀_bijective X B).surjective y
    dsimp only at hxy
    rw [Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀] at hxy
    have hab := (Ext.mk₀_bijective X (Injective.under B)).injective hxy
    exact congrArg Ext.mk₀ ((cancel_mono (Injective.ι B)).mp hab)
  apply hinj
  dsimp only
  rw [← extReverseOfLeftExact_naturality, Ext.mk₀_comp_mk₀, hzero, Ext.mk₀_comp_mk₀]
  apply congrArg Ext.mk₀
  exact ConcreteCategory.congr_hom (e.hom.naturality (Injective.ι B)) f

end CategoryTheory.Functor
