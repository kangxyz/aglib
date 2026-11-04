/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.PairingBiproduct
public import Aglib.Algebra.Homology.DerivedCategory.Plus.GradedAdjointCoordinates
public import Aglib.LinearAlgebra.TensorProduct.Antidiagonal

public import Aglib.CategoryTheory.Shift.AdjunctValue

/-! Bijectivity of the original ordered Ext product from its graded components. -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped TensorProduct DirectSum

@[expose] public noncomputable section

namespace CategoryTheory.Abelian.Ext

private theorem piSingle_eq_of_heq {I : Type*} (A : I → Type*) [DecidableEq I]
    [∀ i, Zero (A i)] {i j : I} (h : i = j) (a : A i) (b : A j) (hab : HEq a b) :
    Pi.single i a = Pi.single j b := by
  subst j
  cases hab
  rfl

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasExt C] [HasExt D]
  {L : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D}
  {R : DerivedCategory.Plus D ⥤ DerivedCategory.Plus C}
  [L.Additive] [L.CommShift ℤ] [R.CommShift ℤ] (adj : L ⊣ R) [adj.CommShift ℤ]
  (U : C) (V : D) (n d bound : ℕ)
  [∀ p, Module (ZMod n) (Ext U U p)] [∀ p, Module (ZMod n) (Ext V V p)]
  (e : L.obj ((DerivedCategory.Plus.singleFunctor C 0).obj U) ≅
    (DerivedCategory.Plus.singleFunctor D 0).obj V)
  (rank : ℕ → ℕ) (hrank : ∀ q, bound ≤ q → rank q = 0)
  (B : ℕ → Type*) [∀ q, AddCommGroup (B q)] [∀ q, Module (ZMod n) (B q)]
  (basis : ∀ q, Module.Basis (Fin (rank q)) (ZMod n) (B q))

local notation "J" => (Σ q : Fin bound, Fin (rank (Fin.val q)))
local notation "U₀" => Functor.obj (DerivedCategory.Plus.singleFunctor C 0) U
local notation "V₀" => Functor.obj (DerivedCategory.Plus.singleFunctor D 0) V

include hrank in
/-- The original ordered Ext product is bijective once the original
adjuncts of the right basis are the specified graded inclusions. -/
theorem bijective_orderedProduct_of_graded_components
    {m : (⨁ fun j : J => (DerivedCategory.Plus.singleFunctor C (j.1.val : ℤ)).obj U) ⟶
      R.obj V₀} (hm : IsIso m)
    (z : ∀ p, Ext U U p → Ext V V p)
    (y : ∀ q, B q → Ext V V q)
    (hz : ∀ p (x : Ext U U p),
      (z p x).homPlus = e.inv ≫ x.homPlus.map L ≫ e.hom⟦(p : ℤ)⟧')
    (hy : ∀ j : J,
      let q := j.1.val
      let η := ((DerivedCategory.Plus.singleFunctors C).shiftIso (-(q : ℤ)) (q : ℤ) 0
        (by omega)).app U
      RegradedComponentValue adj e η (y q (basis q j.2)).homPlus
        (biproduct.ι (fun j : J => (DerivedCategory.Plus.singleFunctor C (j.1.val : ℤ)).obj U)
          j ≫ m))
    (K : (⨁ a : Fin (d + 1), Ext U U a.val ⊗[ZMod n] B (d - a.val)) →ₗ[ZMod n] Ext V V d)
    (hK : ∀ (a : Fin (d + 1)) (x : Ext U U a.val) (b : B (d - a.val)),
      K (DirectSum.lof (ZMod n) (Fin (d + 1))
        (fun a => Ext U U a.val ⊗[ZMod n] B (d - a.val)) a (x ⊗ₜ b)) =
      (z a.val x).comp (y (d - a.val) b) (by omega)) :
    Function.Bijective K := by
  classical
  let A := Ext U U
  let grade : J → ℕ := fun j => j.1.val
  let E := unitAdjunctGradedExtAddEquiv adj U V d e (fun _ : J => U) grade hm
  let E' := AddEquiv.toZModLinearEquiv n E
  refine TensorProduct.bijective_of_antidiagonal_basis_values A d bound rank hrank
    (fun a => B (d - a.val)) (fun a => basis (d - a.val)) E' K ?_
  intro a i x
  let j := (TensorProduct.antidiagonalIndexEquiv rank d bound hrank) ⟨a, i⟩
  let b := d - a.val
  obtain ⟨hb, hj⟩ := TensorProduct.antidiagonalIndexEquiv_value rank d bound hrank a i
  let j' : {j : J // grade j ≤ d} := ⟨⟨⟨b, hb⟩, i⟩, by dsimp [b, grade]; omega⟩
  have hj' : j = j' := Subtype.ext hj
  have ha : a.val = d - b := by dsimp [b]; omega
  let x' : A (d - b) := cast (congrArg A ha) x
  let y' := y b (basis b i)
  have hcoord :=
    unitAdjunctGradedExtAddEquiv_of_ordered_product adj U V d e grade hm j' x'
      (z (d - b) x') y' (hz _ _) (hy j'.val)
  have hp (a₀ : ℕ) (ha₀ : a₀ = d - b) (x₀ : A a₀) (hy : b ≤ d) :
      (z a₀ x₀).comp y' (by omega : a₀ + b = d) =
        (z (d - b) (cast (congrArg A ha₀) x₀)).comp y'
          (by omega : (d - b) + b = d) := by
    subst a₀
    rfl
  rw [hK]
  change E ((z a.val x).comp y' (by omega : a.val + b = d)) =
    Pi.single j (TensorProduct.antidiagonalCoefficient (R := ZMod n) A d bound rank hrank a i x)
  rw [hp a.val ha x (Nat.sub_le _ _)]
  calc
    _ = Pi.single j' x' := hcoord
    _ = _ := by
      have hcast : a.val = d - grade j.val := by rw [hj']; exact ha
      rw [TensorProduct.antidiagonalCoefficient_eq_cast A d bound rank hrank a i x hcast]
      exact piSingle_eq_of_heq _ hj'.symm _ _
        ((cast_heq (congrArg A ha) x).trans (cast_heq (congrArg A hcast) x).symm)

end CategoryTheory.Abelian.Ext
