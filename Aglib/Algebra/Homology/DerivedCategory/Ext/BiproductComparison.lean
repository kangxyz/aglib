/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.ShortExactComparison
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# Original comparison on finite products of coefficient tests

The native `Ext.addEquivBiproduct` identifies the original comparison at a
finite biproduct with its component comparisons. The bicone and its maps
are the original coefficient data. This supplies finite-product tests in
the cogenerator comparison criterion, including the empty family.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory

universe u v u' v' u'' v'' w w'

private theorem surjective_of_pi_transport
    {J : Type*} {S : Type*} {T : Type*} {Si : J → Type*} {Ti : J → Type*}
    (a : S → T) (ai : ∀ i, Si i → Ti i)
    (s : S ≃ ∀ i, Si i) (t : T ≃ ∀ i, Ti i)
    (h : ∀ x i, t (a x) i = ai i (s x i))
    (hs : ∀ i, Function.Surjective (ai i)) : Function.Surjective a := by
  classical
  intro y
  choose x hx using fun i => hs i (t y i)
  refine ⟨s.symm x, t.injective ?_⟩
  funext i
  calc
    t (a (s.symm x)) i = ai i (s (s.symm x) i) := h (s.symm x) i
    _ = ai i (x i) := congrArg (fun z => ai i (z i)) (s.apply_symm_apply x)
    _ = t y i := hx i

private def mapFiniteBilimit
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (G : C ⥤ D) [G.Additive] {J : Type*} [Finite J]
    {Y : J → C} {c : Bicone Y} (hc : c.IsBilimit) :
    (G.mapBicone c).IsBilimit := by
  classical
  let : Fintype J := Fintype.ofFinite J
  refine isBilimitOfTotal _ ?_
  change (∑ i, G.map (c.π i) ≫ G.map (c.ι i)) = 𝟙 (G.obj c.pt)
  simp_rw [← G.map_comp]
  rw [← G.map_sum, IsBilimit.total hc, G.map_id]

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w} D]
  {E : Type u''} [Category.{v''} E] [Abelian E] [HasExt.{w'} E]
  (F : D ⥤ E) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (U : C ⥤ D) [U.Additive]
  {X : D} {A : E} (a : A ⟶ F.obj X)

/-- Injectivity of finite component tests gives injectivity at the actual bicone point. -/
theorem Functor.extPrecompMap_injective_biproduct_on_image
    {J : Type*} [Finite J] {Y : J → C} {c : Bicone Y} (hc : c.IsBilimit) (n : ℕ)
    (h : ∀ i, Function.Injective (F.extPrecompMap a (U.obj (Y i)) n)) :
    Function.Injective (F.extPrecompMap a (U.obj c.pt) n) := by
  let : Fintype J := Fintype.ofFinite J
  let e₁ : Ext X (U.obj c.pt) n ≃+ ∀ i, Ext X (U.obj (Y i)) n :=
    Ext.addEquivBiproduct X (mapFiniteBilimit U hc) n
  let e₂ : Ext A (F.obj (U.obj c.pt)) n ≃+ ∀ i, Ext A (F.obj (U.obj (Y i))) n :=
    Ext.addEquivBiproduct A (mapFiniteBilimit (U ⋙ F) hc) n
  have hcomm (x : Ext X (U.obj c.pt) n) (i : J) :
      e₂ (F.extPrecompMap a (U.obj c.pt) n x) i =
        F.extPrecompMap a (U.obj (Y i)) n (e₁ x i) :=
    DFunLike.congr_fun (F.extPrecompMap_postcomp a (U.map (c.π i)) n) x
  intro x y hxy
  apply e₁.injective
  funext i
  apply h i
  exact (hcomm x i).symm.trans ((congrArg (fun z => e₂ z i) hxy).trans (hcomm y i))

/-- Surjectivity of finite component tests gives surjectivity at the actual bicone point. -/
theorem Functor.extPrecompMap_surjective_biproduct_on_image
    {J : Type*} [Finite J] {Y : J → C} {c : Bicone Y} (hc : c.IsBilimit) (n : ℕ)
    (h : ∀ i, Function.Surjective (F.extPrecompMap a (U.obj (Y i)) n)) :
    Function.Surjective (F.extPrecompMap a (U.obj c.pt) n) := by
  classical
  let : Fintype J := Fintype.ofFinite J
  let e₁ : Ext X (U.obj c.pt) n ≃+ ∀ i, Ext X (U.obj (Y i)) n :=
    Ext.addEquivBiproduct X (mapFiniteBilimit U hc) n
  let e₂ : Ext A (F.obj (U.obj c.pt)) n ≃+ ∀ i, Ext A (F.obj (U.obj (Y i))) n :=
    Ext.addEquivBiproduct A (mapFiniteBilimit (U ⋙ F) hc) n
  have hcomm (x : Ext X (U.obj c.pt) n) (i : J) :
      e₂ (F.extPrecompMap a (U.obj c.pt) n x) i =
        F.extPrecompMap a (U.obj (Y i)) n (e₁ x i) :=
    DFunLike.congr_fun (F.extPrecompMap_postcomp a (U.map (c.π i)) n) x
  exact surjective_of_pi_transport
    (F.extPrecompMap a (U.obj c.pt) n)
    (fun i => F.extPrecompMap a (U.obj (Y i)) n)
    e₁.toEquiv e₂.toEquiv hcomm h

/-- Finite products of original coefficient comparisons preserve bijectivity as well. -/
theorem Functor.extPrecompMap_bijective_biproduct_on_image
    {J : Type*} [Finite J] {Y : J → C} {c : Bicone Y} (hc : c.IsBilimit) (n : ℕ)
    (h : ∀ i, Function.Bijective (F.extPrecompMap a (U.obj (Y i)) n)) :
    Function.Bijective (F.extPrecompMap a (U.obj c.pt) n) :=
  ⟨F.extPrecompMap_injective_biproduct_on_image U a hc n (fun i => (h i).injective),
    F.extPrecompMap_surjective_biproduct_on_image U a hc n (fun i => (h i).surjective)⟩

end CategoryTheory
