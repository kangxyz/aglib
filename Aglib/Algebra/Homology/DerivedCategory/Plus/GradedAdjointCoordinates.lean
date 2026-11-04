/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.GradedBiproductExt
public import Aglib.CategoryTheory.Adjunction.ShiftedHom
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Linear.Basic

/-! Coordinates of original Ext through an adjunction and an invertible graded sum map. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasExt D]
  {L : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D}
  {R : DerivedCategory.Plus D ⥤ DerivedCategory.Plus C}
  [L.Additive] [R.CommShift ℤ] (adj : L ⊣ R)

/-- The original Ext class under the original shifted adjunction, with its unit transport. -/
def unitAdjunctAddEquiv (A : DerivedCategory.Plus C) (V : D) (d : ℕ)
    (e : L.obj A ≅ (DerivedCategory.Plus.singleFunctor D 0).obj V) :
    Ext V V d ≃+
      ShiftedHom A (R.obj ((DerivedCategory.Plus.singleFunctor D 0).obj V)) (d : ℤ) :=
  let V₀ := (DerivedCategory.Plus.singleFunctor D 0).obj V
  (Ext.homPlusAddEquiv (X := V) (Y := V) d).trans
    ((Linear.homCongr ℤ e.symm (Iso.refl (V₀⟦(d : ℤ)⟧))).toAddEquiv.trans
      ((adj.homAddEquiv A (V₀⟦(d : ℤ)⟧)).trans
        (Linear.homCongr ℤ (Iso.refl A) ((R.commShiftIso (d : ℤ)).app V₀)).toAddEquiv))

/-- The forward comparison is the original shifted adjunct of the original class. -/
theorem unitAdjunctAddEquiv_apply (A : DerivedCategory.Plus C) (V : D) (d : ℕ)
    (e : L.obj A ≅ (DerivedCategory.Plus.singleFunctor D 0).obj V) (x : Ext V V d) :
    unitAdjunctAddEquiv adj A V d e x =
      adj.shiftedHomEquiv (d : ℤ) A ((DerivedCategory.Plus.singleFunctor D 0).obj V)
        (e.hom ≫ x.homPlus) := by
  let V₀ := (DerivedCategory.Plus.singleFunctor D 0).obj V
  change (𝟙 A ≫ adj.homEquiv A (V₀⟦(d : ℤ)⟧) ((e.hom ≫ x.homPlus) ≫ 𝟙 _)) ≫
    (R.commShiftIso (d : ℤ)).hom.app V₀ = _
  simp only [Category.id_comp, Category.comp_id, Adjunction.shiftedHomEquiv_apply]
  rfl

variable [HasExt C] (U : C) (V : D) (d : ℕ)
  (e : L.obj ((DerivedCategory.Plus.singleFunctor C 0).obj U) ≅
    (DerivedCategory.Plus.singleFunctor D 0).obj V)
  {J : Type} [Finite J] (W : J → C) (grade : J → ℕ)
  {f : (⨁ fun j : J => (DerivedCategory.Plus.singleFunctor C (grade j : ℤ)).obj (W j)) ⟶
    R.obj ((DerivedCategory.Plus.singleFunctor D 0).obj V)} (hf : IsIso f)

/-- The original graded coordinates via an invertible map from the actual biproduct. -/
def unitAdjunctGradedExtAddEquiv :
    Ext V V d ≃+ (∀ j : {j : J // grade j ≤ d}, Ext U (W j.val) (d - grade j.val)) :=
  let A := (DerivedCategory.Plus.singleFunctor C 0).obj U
  let i := (shiftFunctor (DerivedCategory.Plus C) (d : ℤ)).mapIso (@asIso _ _ _ _ f hf)
  (unitAdjunctAddEquiv adj A V d e).trans
    ((Linear.homCongr ℤ (Iso.refl A) i.symm).toAddEquiv.trans
      (plusUnitGradedBiproductExtAddEquiv U W grade d))

/-- A class with the original single-component adjunct has exactly that Ext coordinate. -/
theorem unitAdjunctGradedExtAddEquiv_of_value [DecidableEq {j : J // grade j ≤ d}]
    (x : Ext V V d) (j : {j : J // grade j ≤ d}) (y : Ext U (W j.val) (d - grade j.val))
    (h : adj.shiftedHomEquiv (d : ℤ) ((DerivedCategory.Plus.singleFunctor C 0).obj U)
        ((DerivedCategory.Plus.singleFunctor D 0).obj V) (e.hom ≫ x.homPlus) =
      plusUnitGradedExtInjection U W grade d j y ≫ f⟦(d : ℤ)⟧') :
    unitAdjunctGradedExtAddEquiv adj U V d e W grade hf x = Pi.single j y := by
  let A := (DerivedCategory.Plus.singleFunctor C 0).obj U
  let Q := shiftFunctor (DerivedCategory.Plus C) (d : ℤ)
  let i := Q.mapIso (@asIso _ _ _ _ f hf)
  have hi : i.hom = Q.map f := rfl
  change plusUnitGradedBiproductExtAddEquiv U W grade d
      ((𝟙 A ≫ unitAdjunctAddEquiv adj A V d e x) ≫ i.inv) = _
  rw [Category.id_comp, unitAdjunctAddEquiv_apply, h, ← hi, Category.assoc, i.hom_inv_id,
    Category.comp_id]
  exact plusUnitGradedBiproductExtAddEquiv_injection U W grade d j y

end CategoryTheory.Abelian.Ext

namespace CategoryTheory.Abelian.Ext

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasExt C] [HasExt D]
  {L : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D}
  {R : DerivedCategory.Plus D ⥤ DerivedCategory.Plus C}
  [L.Additive] [L.CommShift ℤ] [R.CommShift ℤ] (adj : L ⊣ R) [adj.CommShift ℤ]
  (U : C) (V : D) (d : ℕ)
  (e : L.obj ((DerivedCategory.Plus.singleFunctor C 0).obj U) ≅
    (DerivedCategory.Plus.singleFunctor D 0).obj V)
  {J : Type} [Finite J] (grade : J → ℕ)
  {f : (⨁ fun j : J => (DerivedCategory.Plus.singleFunctor C (grade j : ℤ)).obj U) ⟶
    R.obj ((DerivedCategory.Plus.singleFunctor D 0).obj V)} (hf : IsIso f)

local notation "U₀" => Functor.obj (DerivedCategory.Plus.singleFunctor C 0) U
local notation "V₀" => Functor.obj (DerivedCategory.Plus.singleFunctor D 0) V

/-- A transported Yoneda product has just its original graded coordinate. -/
theorem unitAdjunctGradedExtAddEquiv_of_ordered_product
    [DecidableEq {j : J // grade j ≤ d}]
    (j : {j : J // grade j ≤ d})
    (x : Ext U U (d - grade j.val)) (z : Ext V V (d - grade j.val))
    (y : Ext V V (grade j.val))
    (hz : z.homPlus = e.inv ≫ x.homPlus.map L ≫ e.hom⟦((d - grade j.val : ℕ) : ℤ)⟧')
    (hj :
      let q := grade j.val
      let η := ((DerivedCategory.Plus.singleFunctors C).shiftIso (-(q : ℤ)) (q : ℤ) 0
        (by omega)).app U
      biproduct.ι (fun k : J => (DerivedCategory.Plus.singleFunctor C (grade k : ℤ)).obj U)
          j.val ≫ f =
        η.inv ≫ ((shiftEquiv' (DerivedCategory.Plus C) (-(q : ℤ)) (q : ℤ)
          (by omega)).toAdjunction.homEquiv U₀ (R.obj V₀)).symm
          (adj.shiftedHomEquiv (q : ℤ) U₀ V₀ (e.hom ≫ y.homPlus))) :
    unitAdjunctGradedExtAddEquiv adj U V d e (fun _ => U) grade hf
      (z.comp y (by have := j.property; omega)) = Pi.single j x := by
  apply unitAdjunctGradedExtAddEquiv_of_value
  let q := grade j.val
  have hq : q ≤ d := j.property
  let η := ((DerivedCategory.Plus.singleFunctors C).shiftIso (-(q : ℤ)) (q : ℤ) 0
    (by omega)).app U
  let r := adj.shiftedHomEquiv (q : ℤ) U₀ V₀ (e.hom ≫ y.homPlus)
  let s := ((shiftEquiv' (DerivedCategory.Plus C) (-(q : ℤ)) (q : ℤ)
    (by omega)).toAdjunction.homEquiv U₀ (R.obj V₀)).symm r
  let T := plusSingleTotalShiftIso U q d hq
  let b := biproduct.ι (fun k : J =>
    (DerivedCategory.Plus.singleFunctor C (grade k : ℤ)).obj U) j.val
  let H := shiftFunctor (DerivedCategory.Plus C) (d : ℤ)
  have hc : b ≫ f = η.inv ≫ s := hj
  have he := adj.shiftedHomEquiv_comp_map_of_unitIso e x.homPlus y.homPlus z.homPlus hz
    (by omega : (q : ℤ) + ((d - q : ℕ) : ℤ) = (d : ℤ))
  have hr : x.homPlus ≫ T.inv ≫ H.map (η.inv ≫ s) =
      x.homPlus.comp r (by omega : (q : ℤ) + ((d - q : ℕ) : ℤ) = (d : ℤ)) :=
    plusSingleAdjunctionInverse_comp U q d hq x.homPlus r
  rw [homPlus_comp]
  change adj.shiftedHomEquiv (d : ℤ) U₀ V₀
    (e.hom ≫ z.homPlus.comp y.homPlus (by omega)) =
    ((x.homPlus ≫ T.inv) ≫ H.map b) ≫ H.map f
  rw [he, ← hr, Category.assoc (x.homPlus ≫ T.inv), ← H.map_comp, hc, Category.assoc]

end CategoryTheory.Abelian.Ext
