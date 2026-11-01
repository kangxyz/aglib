/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.TStructure
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic

/-!
# Serre properties under original bounded-below right derivation

A lower-bound-preserving triangulated functor preserves a Serre homology
condition if it does so on the original single coefficients. Finite Postnikov
truncation suffices in each output degree; no upper bound on the input is
required. For the installed right-derived functor the tests are the ordinary
natural-degree right-derived functors on the original homology coefficients.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open ZeroObject

universe u v w u' v' w'

namespace DerivedCategory.Plus

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
  (F : Plus A ⥤ Plus B) [F.CommShift ℤ] [F.IsTriangulated]
  (P : ObjectProperty B) [P.IsSerreClass]

/-- A Serre property of the homology of the images of the original singles
passes to the image of a cohomologically bounded object. -/
theorem homologyProperty_obj_of_homology_bounds (K : Plus A) (a b n : ℤ)
    [K.IsGE a] [K.IsLE b]
    (hs : ∀ i : ℤ, a ≤ i → i ≤ b →
      P ((homologyFunctor B n).obj
        (F.obj ((singleFunctor A i).obj ((homologyFunctor A i).obj K))))) :
    P ((homologyFunctor B n).obj (F.obj K)) := by
  let Q : ObjectProperty (Plus A) := fun L => P ((homologyFunctor B n).obj (F.obj L))
  let : Q.IsClosedUnderIsomorphisms := {
    of_iso := fun e h => P.prop_of_iso ((F ⋙ homologyFunctor B n).mapIso e) h }
  let : Q.ContainsZero := {
    exists_zero := ⟨0, isZero_zero _,
      P.prop_of_isZero ((F ⋙ homologyFunctor B n).map_isZero (isZero_zero _))⟩ }
  let : Q.IsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.mk'
    (P := Q) (fun T hT h₁ h₃ =>
      P.prop_X₂_of_exact ((homologyFunctor B 0).homologySequence_exact₂
        (F.mapTriangle.obj T) (F.map_distinguished T hT) n) h₁ h₃)
  exact property_of_homology_bounds Q K a b hs

/-- Lower-bound preservation and the finite Postnikov layers propagate a Serre
homology property from original singles to any native bounded-below object. -/
theorem homologyProperty_obj_of_homology_singles
    (hF : ∀ (L : Plus A) (a : ℤ), L.IsGE a → (F.obj L).IsGE a)
    (K : Plus A)
    (hs : ∀ i n : ℤ, P ((homologyFunctor B n).obj
      (F.obj ((singleFunctor A i).obj ((homologyFunctor A i).obj K)))))
    (n : ℤ) : P ((homologyFunctor B n).obj (F.obj K)) := by
  obtain ⟨a, ha⟩ := K.property
  let : K.IsGE a := (isGE_ι_obj_iff K a).mp ha
  let L := (TStructure.t.truncLT (n + 1)).obj K
  let : L.IsGE a := by dsimp [L]; infer_instance
  let : L.IsLE n := by dsimp [L]; infer_instance
  have hL : P ((homologyFunctor B n).obj (F.obj L)) := by
    apply homologyProperty_obj_of_homology_bounds F P L a n n
    intro i hai hin
    exact P.prop_of_iso ((F ⋙ homologyFunctor B n).mapIso
      ((singleFunctor A i).mapIso (homologyTruncLTIso K (n + 1) i (by omega))).symm)
        (hs i n)
  let T := (TStructure.t.triangleLTGE (n + 1)).obj K
  have hT : T ∈ distTriang _ := TStructure.t.triangleLTGE_distinguished (n + 1) K
  let : (F.mapTriangle.obj T).obj₃.IsGE (n + 1) := hF _ _ inferInstance
  let φ : (homologyFunctor B n).obj (F.obj L) ⟶
      (homologyFunctor B n).obj (F.obj K) :=
    (homologyFunctor B n).map (F.map T.mor₁)
  have hφ : IsIso φ :=
    isIso_homology_mor₁_of_isGE (F.mapTriangle.obj T) (F.map_distinguished T hT)
      (n + 1) n (by omega)
  exact P.prop_of_iso (@asIso B _ _ _ φ hφ) hL

omit [F.IsTriangulated] [P.IsSerreClass] in
/-- Original shift and homology comparisons transport a degree-zero single to
any single degree without changing its coefficient object. -/
def homologyObjSingleShiftIso (M : A) (i n : ℤ) :
    (homologyFunctor B n).obj (F.obj ((singleFunctor A i).obj M)) ≅
      (homologyFunctor B (n - i)).obj (F.obj ((singleFunctor A 0).obj M)) := by
  let K := F.obj ((singleFunctor A 0).obj M)
  let eShift : (homologyFunctor B n).obj (K⟦-i⟧) ≅
      (homologyFunctor B (n - i)).obj K := by
    change (DerivedCategory.homologyFunctor B n).obj (ι.obj (K⟦-i⟧)) ≅
      (DerivedCategory.homologyFunctor B (n - i)).obj (ι.obj K)
    let e := ((DerivedCategory.homologyFunctor B 0).shiftIso (-i) n (n - i)
      (by omega)).app (ι.obj K)
    have e' : (DerivedCategory.homologyFunctor B n).obj ((ι.obj K)⟦-i⟧) ≅
        (DerivedCategory.homologyFunctor B (n - i)).obj (ι.obj K) := by
      simpa only [Functor.comp_obj, DerivedCategory.shift_homologyFunctor] using e
    exact (DerivedCategory.homologyFunctor B n).mapIso
      ((ι.commShiftIso (-i)).app K) ≪≫ e'
  exact (homologyFunctor B n).mapIso
      (F.mapIso (((singleFunctors A).shiftIso (-i) i 0 (by omega)).app M).symm ≪≫
        (F.commShiftIso (-i)).app ((singleFunctor A 0).obj M)) ≪≫ eShift

end DerivedCategory.Plus

namespace CategoryTheory.Functor

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [EnoughInjectives A] {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w'} B] (F : A ⥤ B) [F.Additive]
  (P : ObjectProperty B) [P.IsSerreClass]

/-- A Serre property of all ordinary right-derived functors on a coefficient
is the same property on every homology degree of any shifted derived single. -/
theorem homologyProperty_rightDerivedFunctorPlus_single
    (M : A) (hM : ∀ q : ℕ, P ((F.rightDerived q).obj M)) (i n : ℤ) :
    P ((DerivedCategory.Plus.homologyFunctor B n).obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A i).obj M))) := by
  apply P.prop_of_iso
    (DerivedCategory.Plus.homologyObjSingleShiftIso F.rightDerivedFunctorPlus M i n).symm
  by_cases hn : 0 ≤ n - i
  · obtain ⟨q, hq⟩ := Int.eq_ofNat_of_zero_le hn
    rw [hq]
    exact P.prop_of_iso ((F.rightDerivedSingleHomologyIso q).app M) (hM q)
  · exact P.prop_of_isZero (F.isZero_homology_rightDerivedFunctorPlus_of_isGE
      ((DerivedCategory.Plus.singleFunctor A 0).obj M) 0 (n - i) (by omega))

/-- Ordinary higher-derived preservation on the original homology coefficients
implies the Serre property on every homology of the installed `D+` image.
No uniform amplitude, exponent, or upper bound on the input is assumed. -/
theorem homologyProperty_rightDerivedFunctorPlus
    (K : DerivedCategory.Plus A)
    (hK : ∀ (i : ℤ) (q : ℕ), P ((F.rightDerived q).obj
      ((DerivedCategory.Plus.homologyFunctor A i).obj K))) (n : ℤ) :
    P ((DerivedCategory.Plus.homologyFunctor B n).obj (F.rightDerivedFunctorPlus.obj K)) :=
  DerivedCategory.Plus.homologyProperty_obj_of_homology_singles
    F.rightDerivedFunctorPlus P
    (fun L a hL => by
      let : L.IsGE a := hL
      exact F.rightDerivedFunctorPlus_isGE L a)
    K (fun i j => F.homologyProperty_rightDerivedFunctorPlus_single P _ (hK i) i j) n

end CategoryTheory.Functor
