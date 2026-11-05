/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.Injective.MapAugmentation
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Exact precomposition for natural-degree right-derived functors

An additive functor preserving homology and injective objects carries the
original injective resolution, with its original mapped augmentation, to an
injective resolution. Computing both sides on that same complex gives the
canonical precomposition comparison for the native natural-degree derivatives.
The comparison is natural in coefficients and additive functor transformations.
No derived-category model or choice of a second resolution is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v u₁ v₁ u₂ v₂

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u₁} [Category.{v₁} D] [Abelian D]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  (E : C ⥤ D) [E.Additive] [E.PreservesHomology] [E.PreservesInjectiveObjects]

namespace InjectiveResolution

/-- The literal image of the supplied resolution, with the original mapped augmentation. -/
@[implicit_reducible]
def mapOfPreservesHomology {M : C} (I : InjectiveResolution M) :
    InjectiveResolution (E.obj M) := by
  letI : QuasiIso (I.mapAugmentation E) := by
    rw [mapAugmentation_eq]
    infer_instance
  exact {
    cocomplex := (E.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
    injective n := E.injective_obj_of_injective (I.injective n)
    ι := I.mapAugmentation E }

/-- An original resolution lift maps to the actual mapped resolutions. -/
def mapHomOfPreservesHomology {M N : C}
    {I : InjectiveResolution M} {J : InjectiveResolution N} {f : M ⟶ N}
    (φ : InjectiveResolution.Hom I J f) :
    InjectiveResolution.Hom (I.mapOfPreservesHomology E)
      (J.mapOfPreservesHomology E) (E.map f) where
  hom := (E.mapHomologicalComplex (.up ℕ)).map φ.hom
  ι_f_zero_comp_hom_f_zero := by
    simpa only [mapOfPreservesHomology, comp_f] using
      congrArg (fun g => g.f 0) (I.mapAugmentation_naturality E φ)

variable [HasInjectiveResolutions C] [HasInjectiveResolutions D]
  (F : D ⥤ B) [F.Additive]

/-- Precomposition computed on the supplied original resolution and its literal image. -/
def isoRightDerivedPrecompObj {M : C} (I : InjectiveResolution M) (n : ℕ) :
    ((E ⋙ F).rightDerived n).obj M ≅ (F.rightDerived n).obj (E.obj M) :=
  I.isoRightDerivedObj (E ⋙ F) n ≪≫
    ((I.mapOfPreservesHomology E).isoRightDerivedObj F n).symm

/-- Every lift of the original coefficient map preserves the precomposition comparison. -/
@[reassoc]
theorem isoRightDerivedPrecompObj_hom_naturality
    {M N : C} (f : M ⟶ N) (I : InjectiveResolution M) (J : InjectiveResolution N)
    (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (n : ℕ) :
    ((E ⋙ F).rightDerived n).map f ≫ (J.isoRightDerivedPrecompObj E F n).hom =
      (I.isoRightDerivedPrecompObj E F n).hom ≫ (F.rightDerived n).map (E.map f) := by
  have hφ' : (I.mapOfPreservesHomology E).ι.f 0 ≫
      ((E.mapHomologicalComplex (.up ℕ)).map φ).f 0 =
        E.map f ≫ (J.mapOfPreservesHomology E).ι.f 0 := by
    let ψ : InjectiveResolution.Hom I J f := {
      hom := φ
      ι_f_zero_comp_hom_f_zero := hφ.trans (congrArg
        (fun k : ((CochainComplex.single₀ C).obj M).X 0 ⟶
            ((CochainComplex.single₀ C).obj N).X 0 => k ≫ J.ι.f 0)
        (CochainComplex.single₀_map_f_zero f).symm) }
    have h := (mapHomOfPreservesHomology E ψ).ι_f_zero_comp_hom_f_zero
    change (I.mapOfPreservesHomology E).ι.f 0 ≫
      ((E.mapHomologicalComplex (.up ℕ)).map φ).f 0 =
        ((CochainComplex.single₀ D).map (E.map f)).f 0 ≫
          (J.mapOfPreservesHomology E).ι.f 0 at h
    exact h.trans (congrArg
      (fun k : ((CochainComplex.single₀ D).obj (E.obj M)).X 0 ⟶
          ((CochainComplex.single₀ D).obj (E.obj N)).X 0 =>
        k ≫ (J.mapOfPreservesHomology E).ι.f 0)
      (CochainComplex.single₀_map_f_zero (E.map f)))
  have h₁ := isoRightDerivedObj_hom_naturality f I J φ hφ (E ⋙ F) n
  have h₂ := isoRightDerivedObj_inv_naturality (E.map f)
    (I.mapOfPreservesHomology E) (J.mapOfPreservesHomology E)
    ((E.mapHomologicalComplex (.up ℕ)).map φ) hφ' F n
  have hmap : ((E ⋙ F).mapHomologicalComplex (.up ℕ)).map φ =
      (F.mapHomologicalComplex (.up ℕ)).map
        ((E.mapHomologicalComplex (.up ℕ)).map φ) := by
    ext i
    rfl
  have h₃ :
      ((E ⋙ F).mapHomologicalComplex (.up ℕ) ⋙ homologyFunctor B (.up ℕ) n).map φ =
        (F.mapHomologicalComplex (.up ℕ) ⋙ homologyFunctor B (.up ℕ) n).map
          ((E.mapHomologicalComplex (.up ℕ)).map φ) :=
    congrArg (fun ψ => (homologyFunctor B (.up ℕ) n).map ψ) hmap
  simp only [isoRightDerivedPrecompObj, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, h₁, Category.assoc]
  exact congrArg (fun t => (I.isoRightDerivedObj (E ⋙ F) n).hom ≫ t)
    ((congrArg (fun t => t ≫ ((J.mapOfPreservesHomology E).isoRightDerivedObj F n).inv)
      h₃).trans h₂.symm)

/-- The same comparison respects every original additive functor transformation. -/
@[reassoc]
theorem isoRightDerivedPrecompObj_hom_natTrans
    {G : D ⥤ B} [G.Additive] (τ : F ⟶ G) {M : C}
    (I : InjectiveResolution M) (n : ℕ) :
    (NatTrans.rightDerived (Functor.whiskerLeft E τ) n).app M ≫
        (I.isoRightDerivedPrecompObj E G n).hom =
      (I.isoRightDerivedPrecompObj E F n).hom ≫
        (NatTrans.rightDerived τ n).app (E.obj M) := by
  have hτ : (NatTrans.mapHomologicalComplex (Functor.whiskerLeft E τ) (.up ℕ)).app
      I.cocomplex =
        (NatTrans.mapHomologicalComplex τ (.up ℕ)).app
          (I.mapOfPreservesHomology E).cocomplex := by
    ext i
    rfl
  have hτ' := congrArg (fun ψ => (I.isoRightDerivedObj (E ⋙ F) n).hom ≫
    (homologyFunctor B (.up ℕ) n).map ψ ≫
      ((I.mapOfPreservesHomology E).isoRightDerivedObj G n).inv) hτ
  rw [I.rightDerived_app_eq (Functor.whiskerLeft E τ) n,
    (I.mapOfPreservesHomology E).rightDerived_app_eq τ n]
  simpa only [isoRightDerivedPrecompObj, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc] using hτ'

end InjectiveResolution

namespace Functor

variable [HasInjectiveResolutions C] [HasInjectiveResolutions D]
  (F : D ⥤ B) [F.Additive]

/-- Compute exact precomposition using the original chosen injective resolution. -/
def rightDerivedPrecompObjIso (n : ℕ) (M : C) :
    ((E ⋙ F).rightDerived n).obj M ≅ (F.rightDerived n).obj (E.obj M) :=
  (injectiveResolution M).isoRightDerivedPrecompObj E F n

/-- Precomposition preserving homology and injectives commutes with native right derivatives. -/
def rightDerivedPrecompIso (n : ℕ) :
    (E ⋙ F).rightDerived n ≅ E ⋙ F.rightDerived n :=
  NatIso.ofComponents (rightDerivedPrecompObjIso E F n) (by
    intro M N f
    exact InjectiveResolution.isoRightDerivedPrecompObj_hom_naturality E F f
      (injectiveResolution M) (injectiveResolution N)
      (InjectiveResolution.desc f (injectiveResolution N) (injectiveResolution M))
      (InjectiveResolution.desc_commutes_zero f
        (injectiveResolution N) (injectiveResolution M)) n)

/-- The whole precomposition comparison is natural in additive functor transformations. -/
@[reassoc]
theorem rightDerivedPrecompIso_hom_natTrans
    {G : D ⥤ B} [G.Additive] (τ : F ⟶ G) (n : ℕ) :
    NatTrans.rightDerived (Functor.whiskerLeft E τ) n ≫
        (rightDerivedPrecompIso E G n).hom =
      (rightDerivedPrecompIso E F n).hom ≫
        Functor.whiskerLeft E (NatTrans.rightDerived τ n) := by
  ext M
  exact InjectiveResolution.isoRightDerivedPrecompObj_hom_natTrans E F τ
    (injectiveResolution M) n

end Functor

end CategoryTheory
