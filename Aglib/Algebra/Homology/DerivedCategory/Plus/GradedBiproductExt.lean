/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Shift.Basic
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Ext

public import Aglib.CategoryTheory.Shift.AdjunctionTransport

/-! Original Ext coordinates of a finite graded biproduct in the bounded-below derived category. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w wd

namespace CategoryTheory.Limits

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasShift D ℤ]
  [∀ d : ℤ, (shiftFunctor D d).Additive]
  {I : Type} [Finite I]
  (K : I → D) [HasBiproduct K] (S : D) (d : ℤ)

/-- Morphisms into the original shifted finite biproduct are the family of
their literal shifted projection composites. -/
def shiftBiproductHomAddEquiv :
    (S ⟶ (⨁ K)⟦d⟧) ≃+ (∀ i, S ⟶ (K i)⟦d⟧) := by
  let e : (⨁ K)⟦d⟧ ≅ ⨁ fun i => (K i)⟦d⟧ :=
    Functor.mapBiproduct (shiftFunctor D d) K
  let hπ (i : I) : e.hom ≫ biproduct.π (fun i => (K i)⟦d⟧) i =
      (shiftFunctor D d).map (biproduct.π K i) := by
    simp only [e, Functor.mapBiproduct_hom, biproduct.lift_π]
  refine {
    toFun := fun f i => f ≫ (shiftFunctor D d).map (biproduct.π K i)
    invFun := fun g => biproduct.lift g ≫ e.inv
    left_inv := ?_
    right_inv := ?_
    map_add' := ?_ }
  · intro f
    apply (cancel_mono e.hom).mp
    apply biproduct.hom_ext
    intro i
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id, biproduct.lift_π,
      hπ]
  · intro g
    funext i
    change (biproduct.lift g ≫ e.inv) ≫ (shiftFunctor D d).map (biproduct.π K i) = g i
    calc
      _ = (biproduct.lift g ≫ e.inv) ≫
          (e.hom ≫ biproduct.π (fun i => (K i)⟦d⟧) i) := by rw [hπ i]
      _ = biproduct.lift g ≫ (e.inv ≫ e.hom) ≫
          biproduct.π (fun i => (K i)⟦d⟧) i := by simp only [Category.assoc]
      _ = g i := by rw [e.inv_hom_id]; simp
  · intro f g
    funext i
    simp only [Pi.add_apply, Preadditive.add_comp]

/-- The exact component formula uses the original projection before shifting. -/
@[simp]
theorem shiftBiproductHomAddEquiv_apply (f : S ⟶ (⨁ K)⟦d⟧) (i : I) :
    shiftBiproductHomAddEquiv K S d f i =
      f ≫ (shiftFunctor D d).map (biproduct.π K i) := rfl

/-- A summand class enters through the shifted original biproduct injection. -/
theorem shiftBiproductHomAddEquiv_injection [DecidableEq I]
    (i : I) (f : S ⟶ (K i)⟦d⟧) :
    shiftBiproductHomAddEquiv K S d
        (f ≫ (shiftFunctor D d).map (biproduct.ι K i)) = Pi.single i f := by
  funext j
  rw [shiftBiproductHomAddEquiv_apply, Category.assoc, ← Functor.map_comp]
  by_cases h : i = j
  · subst j
    simp
  · simp [h]

end CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{wd} C]
  [HasExt.{w} C] {I : Type} [Finite I]
  (U₀ : C) (U : I → C) (q : I → ℤ) (d : ℤ)

/-- The original bounded-below unit singles use the scheme-free shifted
biproduct Hom coordinates, with no new cohomology model. -/
def plusUnitShiftBiproductHomAddEquiv :
    ((DerivedCategory.Plus.singleFunctor C 0).obj U₀ ⟶
      (⨁ fun i : I => (DerivedCategory.Plus.singleFunctor C (q i)).obj (U i))⟦d⟧) ≃+
    (∀ i, (DerivedCategory.Plus.singleFunctor C 0).obj U₀ ⟶
      ((DerivedCategory.Plus.singleFunctor C (q i)).obj (U i))⟦d⟧) :=
  Limits.shiftBiproductHomAddEquiv
    (fun i => (DerivedCategory.Plus.singleFunctor C (q i)).obj (U i))
    ((DerivedCategory.Plus.singleFunctor C 0).obj U₀) d

/- In the actual bounded-below unit family, a component enters by the
shifted original biproduct injection. -/
omit [HasExt C] in
theorem plusUnitShiftBiproductHomAddEquiv_injection [DecidableEq I]
    (i : I)
    (f : (DerivedCategory.Plus.singleFunctor C 0).obj U₀ ⟶
      ((DerivedCategory.Plus.singleFunctor C (q i)).obj (U i))⟦d⟧) :
    plusUnitShiftBiproductHomAddEquiv U₀ U q d
        (f ≫ (shiftFunctor (DerivedCategory.Plus C) d).map
          (biproduct.ι
            (fun j : I => (DerivedCategory.Plus.singleFunctor C (q j)).obj (U j)) i)) =
      Pi.single i f :=
  Limits.shiftBiproductHomAddEquiv_injection
    (fun j : I => (DerivedCategory.Plus.singleFunctor C (q j)).obj (U j))
    ((DerivedCategory.Plus.singleFunctor C 0).obj U₀) d i f

/- A degree above the total degree contributes no morphism from the
degree-zero bounded-below unit. -/
omit [HasExt C] [Finite I] in
theorem plusUnitShiftComponent_eq_zero (i : I) (h : d < q i)
    (f : (DerivedCategory.Plus.singleFunctor C 0).obj U₀ ⟶
      ((DerivedCategory.Plus.singleFunctor C (q i)).obj (U i))⟦d⟧) : f = 0 := by
  let X := (DerivedCategory.Plus.singleFunctor C 0).obj U₀
  let Y := (DerivedCategory.Plus.singleFunctor C (q i)).obj (U i)
  have hX : DerivedCategory.Plus.TStructure.t.IsLE X 0 := inferInstance
  have hY : DerivedCategory.Plus.TStructure.t.IsGE (Y⟦d⟧) (q i - d) :=
    DerivedCategory.Plus.TStructure.t.isGE_shift Y (q i) d (q i - d) (by omega)
  exact DerivedCategory.Plus.TStructure.t.zero_of_isLE_of_isGE f 0 (q i - d)
    (by omega) hX hY

section SingleComponent

variable (V W : C) (a b : ℕ) (hab : a ≤ b)

/-- The shifted single in degree `a` is the original degree-zero single
shifted by `b-a`, with no replacement of the underlying object. -/
def plusSingleTotalShiftIso :
    ((DerivedCategory.Plus.singleFunctor C (a : ℤ)).obj W)⟦(b : ℤ)⟧ ≅
      ((DerivedCategory.Plus.singleFunctor C 0).obj W)⟦((b - a : ℕ) : ℤ)⟧ :=
  (((DerivedCategory.Plus.singleFunctors C).shiftIso (b : ℤ)
      ((a : ℤ) - (b : ℤ)) (a : ℤ) (by omega)).app W) ≪≫
    (((DerivedCategory.Plus.singleFunctors C).shiftIso ((b - a : ℕ) : ℤ)
      ((a : ℤ) - (b : ℤ)) 0 (by omega)).app W).symm

omit [HasExt C] in
/-- Regrading an original single and then shifting agrees with the original shift sum. -/
theorem plusSingleTotalShiftIso_hom_comp :
    (((DerivedCategory.Plus.singleFunctors C).shiftIso (-(a : ℤ)) (a : ℤ) 0
      (by omega)).hom.app W)⟦(b : ℤ)⟧' ≫
        (plusSingleTotalShiftIso W a b hab).hom =
      (shiftFunctorAdd' (DerivedCategory.Plus C) (-(a : ℤ)) (b : ℤ)
        ((b - a : ℕ) : ℤ) (by omega)).inv.app
          ((DerivedCategory.Plus.singleFunctor C 0).obj W) := by
  let F := DerivedCategory.Plus.singleFunctors C
  let U := (DerivedCategory.Plus.singleFunctor C 0).obj W
  let h : -(a : ℤ) + (b : ℤ) = ((b - a : ℕ) : ℤ) := by omega
  let A := shiftFunctorAdd' (DerivedCategory.Plus C) (-(a : ℤ)) (b : ℤ)
    ((b - a : ℕ) : ℤ) h
  let e := (F.shiftIso (-(a : ℤ)) (a : ℤ) 0 (by omega)).app W
  let u := (F.shiftIso (b : ℤ) ((a : ℤ) - (b : ℤ)) (a : ℤ) (by omega)).app W
  let v := (F.shiftIso ((b - a : ℕ) : ℤ) ((a : ℤ) - (b : ℤ)) 0 (by omega)).app W
  have he : A.hom.app U ≫ e.hom⟦(b : ℤ)⟧' ≫ u.hom = v.hom :=
    (F.shiftIso_add'_hom_app (b : ℤ) (-(a : ℤ)) ((b - a : ℕ) : ℤ) h
      ((a : ℤ) - (b : ℤ)) (a : ℤ) 0 (by omega) (by omega) W).symm
  apply (cancel_epi (A.hom.app U)).mp
  change A.hom.app U ≫ (e.hom⟦(b : ℤ)⟧' ≫ u.hom ≫ v.inv) = A.hom.app U ≫ A.inv.app U
  calc
    _ = (A.hom.app U ≫ e.hom⟦(b : ℤ)⟧' ≫ u.hom) ≫ v.inv := by
      simp only [Category.assoc]
    _ = _ := by
      rw [he, v.hom_inv_id, A.hom_inv_id_app]
      rfl

omit [HasExt C] in
/-- The exact grade insertion through the inverse shift adjunction is the
original shifted composition. -/
theorem plusSingleAdjunctionInverse_comp {X K : DerivedCategory.Plus C}
    (x : ShiftedHom X ((DerivedCategory.Plus.singleFunctor C 0).obj W) ((b - a : ℕ) : ℤ))
    (y : ShiftedHom ((DerivedCategory.Plus.singleFunctor C 0).obj W) K (a : ℤ)) :
    let U := (DerivedCategory.Plus.singleFunctor C 0).obj W
    let eta := ((DerivedCategory.Plus.singleFunctors C).shiftIso (-(a : ℤ)) (a : ℤ) 0
      (by omega)).app W
    let T := plusSingleTotalShiftIso W a b hab
    let adj := (shiftEquiv' (DerivedCategory.Plus C) (-(a : ℤ)) (a : ℤ)
      (neg_add_cancel (a : ℤ))).toAdjunction
    x ≫ T.inv ≫ (eta.inv ≫ (adj.homEquiv U K).symm y)⟦(b : ℤ)⟧' =
      x.comp y (by omega : (a : ℤ) + ((b - a : ℕ) : ℤ) = (b : ℤ)) := by
  intro U eta T adj
  exact shiftAdjunctionInverse_comp
    (D := DerivedCategory.Plus C) (X := X) (U := U)
    (Uq := (DerivedCategory.Plus.singleFunctor C (a : ℤ)).obj W) (K := K)
    (p := ((b - a : ℕ) : ℤ)) (q := (a : ℤ)) (d := (b : ℤ)) (by omega)
    eta T (plusSingleTotalShiftIso_hom_comp W a b hab) x y

/-- A component at degree `a ≤ b` is the original Ext in degree `b-a`.
The forward map is postcomposition with the original single-shift iso,
followed by `homPlusAddEquiv.symm`. -/
def plusSingleTotalHomExtAddEquiv :
    ((DerivedCategory.Plus.singleFunctor C 0).obj V ⟶
      ((DerivedCategory.Plus.singleFunctor C (a : ℤ)).obj W)⟦(b : ℤ)⟧) ≃+
      Ext.{w} V W (b - a) := by
  let S := (DerivedCategory.Plus.singleFunctor C 0).obj V
  let e := plusSingleTotalShiftIso W a b hab
  let h : (S ⟶ ((DerivedCategory.Plus.singleFunctor C (a : ℤ)).obj W)⟦(b : ℤ)⟧) ≃+
      (S ⟶ ((DerivedCategory.Plus.singleFunctor C 0).obj W)⟦((b - a : ℕ) : ℤ)⟧) :=
    { toFun := fun f => f ≫ e.hom
      invFun := fun f => f ≫ e.inv
      left_inv := fun f => by simp [Category.assoc]
      right_inv := fun f => by simp [Category.assoc]
      map_add' := fun f g => by simp }
  exact h.trans (homPlusAddEquiv (X := V) (Y := W) (b - a)).symm

/-- Its inverse is literally the bounded-below original Ext class followed
by the inverse of the original single-shift iso. -/
theorem plusSingleTotalHomExtAddEquiv_symm_apply (x : Ext.{w} V W (b - a)) :
    (plusSingleTotalHomExtAddEquiv V W a b hab).symm x =
      x.homPlus ≫ (plusSingleTotalShiftIso W a b hab).inv := rfl

end SingleComponent

section GradedCoordinates

variable {J : Type} (grade : J → ℕ) (total : ℕ)
  (P : J → Type*) [∀ j, AddCommGroup (P j)]

/-- Delete exactly the coordinates forced to be zero above the total degree. -/
def lowPiAddEquiv (hhigh : ∀ j, total < grade j → Subsingleton (P j)) :
    (∀ j, P j) ≃+ (∀ j : {j : J // grade j ≤ total}, P j.val) where
  toFun f j := f j.val
  invFun g j := if h : grade j ≤ total then g ⟨j, h⟩ else 0
  left_inv f := by
    funext j
    dsimp
    split_ifs with h
    · rfl
    · exact @Subsingleton.elim _ (hhigh j (by omega)) _ _
  right_inv g := by
    funext ⟨j, hj⟩
    simp [hj]
  map_add' f g := by
    funext j
    rfl

end GradedCoordinates

variable {J : Type} [Finite J] (V₀ : C) (W₀ : J → C)
  (grade : J → ℕ) (total : ℕ)

/-- The original total-degree Hom into the finite graded unit biproduct is
the product of its nonzero original Ext coordinates. -/
def plusUnitGradedBiproductExtAddEquiv :
    ((DerivedCategory.Plus.singleFunctor C 0).obj V₀ ⟶
      (⨁ fun j : J => (DerivedCategory.Plus.singleFunctor C (grade j : ℤ)).obj (W₀ j))
        ⟦(total : ℤ)⟧) ≃+
      (∀ j : {j : J // grade j ≤ total}, Ext.{w} V₀ (W₀ j.val) (total - grade j.val)) := by
  let K : J → DerivedCategory.Plus C :=
    fun j => (DerivedCategory.Plus.singleFunctor C (grade j : ℤ)).obj (W₀ j)
  let P (j : J) :=
    ((DerivedCategory.Plus.singleFunctor C 0).obj V₀ ⟶ (K j)⟦(total : ℤ)⟧)
  have hhigh (j : J) (hj : total < grade j) : Subsingleton (P j) := by
    constructor
    intro f g
    have hf : f = 0 := plusUnitShiftComponent_eq_zero V₀ W₀
      (fun j => (grade j : ℤ)) (total : ℤ) j (by exact_mod_cast hj) f
    have hg : g = 0 := plusUnitShiftComponent_eq_zero V₀ W₀
      (fun j => (grade j : ℤ)) (total : ℤ) j (by exact_mod_cast hj) g
    exact hf.trans hg.symm
  exact (plusUnitShiftBiproductHomAddEquiv V₀ W₀
    (fun j => (grade j : ℤ)) (total : ℤ)).trans
      ((lowPiAddEquiv (grade := grade) (total := total) (P := P) hhigh).trans
        (AddEquiv.piCongrRight fun j =>
          plusSingleTotalHomExtAddEquiv V₀ (W₀ j.val)
            (grade j.val) total j.property))

/-- The original Ext class enters the total Hom through the original
bounded-below class, single-shift inverse and shifted biproduct injection. -/
def plusUnitGradedExtInjection (j : {j : J // grade j ≤ total})
    (x : Ext.{w} V₀ (W₀ j.val) (total - grade j.val)) :
    (DerivedCategory.Plus.singleFunctor C 0).obj V₀ ⟶
      (⨁ fun k : J => (DerivedCategory.Plus.singleFunctor C (grade k : ℤ)).obj (W₀ k))
        ⟦(total : ℤ)⟧ :=
  (x.homPlus ≫ (plusSingleTotalShiftIso (W₀ j.val) (grade j.val) total j.property).inv) ≫
    (shiftFunctor (DerivedCategory.Plus C) (total : ℤ)).map
      (biproduct.ι
        (fun k : J => (DerivedCategory.Plus.singleFunctor C (grade k : ℤ)).obj (W₀ k))
        j.val)

/-- The exact original injection contributes precisely one Ext coordinate. -/
theorem plusUnitGradedBiproductExtAddEquiv_injection
    [DecidableEq {j : J // grade j ≤ total}]
    (j : {j : J // grade j ≤ total})
    (x : Ext.{w} V₀ (W₀ j.val) (total - grade j.val)) :
    plusUnitGradedBiproductExtAddEquiv V₀ W₀ grade total
      (plusUnitGradedExtInjection V₀ W₀ grade total j x) = Pi.single j x := by
  classical
  funext k
  change plusSingleTotalHomExtAddEquiv V₀ (W₀ k.val) (grade k.val) total k.property
    ((plusUnitShiftBiproductHomAddEquiv V₀ W₀
      (fun l => (grade l : ℤ)) (total : ℤ)
      (plusUnitGradedExtInjection V₀ W₀ grade total j x)) k.val) =
        (Pi.single j x : ∀ k : {j : J // grade j ≤ total},
          Ext.{w} V₀ (W₀ k.val) (total - grade k.val)) k
  rw [plusUnitGradedExtInjection,
    plusUnitShiftBiproductHomAddEquiv_injection]
  by_cases h : k = j
  · subst k
    simp only [Pi.single_eq_same]
    change plusSingleTotalHomExtAddEquiv V₀ (W₀ j.val) (grade j.val) total j.property
      ((plusSingleTotalHomExtAddEquiv V₀ (W₀ j.val)
        (grade j.val) total j.property).symm x) = x
    exact AddEquiv.apply_symm_apply _ _
  · have hval : k.val ≠ j.val := by
      intro he
      apply h
      exact Subtype.ext he
    simp only [Pi.single_eq_of_ne h, Pi.single_eq_of_ne hval, map_zero]

end CategoryTheory.Abelian.Ext
