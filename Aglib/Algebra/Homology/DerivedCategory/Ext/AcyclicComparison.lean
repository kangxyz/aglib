/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.FiveLemma
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Comparing Ext through an exact functor with acyclic injective images

An exact functor and a specified map into the image of a source object give
the original Ext map followed by precomposition. If this comparison is an
isomorphism in degree zero and images of injectives are acyclic for the
target source object, it is an isomorphism in every degree. Images of
injectives need not be injective. The proof uses the native connecting
extension classes and dimension shifting along an injective presentation.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory

universe u v u' v' w w'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X : C} {A : D} (a : A ⟶ F.obj X)

/-- The original exact-functor Ext map followed by the specified source precomposition. -/
def Functor.extPrecompMap (Y : C) (n : ℕ) : Ext.{w} X Y n →+ Ext.{w'} A (F.obj Y) n :=
  ((Ext.mk₀ a).precomp (F.obj Y) (Nat.zero_add n)).comp (F.mapExtAddHom X Y n)

/-- The comparison keeps its original exact-functor and source-morphism formula. -/
theorem Functor.extPrecompMap_apply (Y : C) (n : ℕ) (x : Ext.{w} X Y n) :
    F.extPrecompMap a Y n x =
      (Ext.mk₀ a).comp (x.mapExactFunctor F) (Nat.zero_add n) := rfl

/-- In degree zero the comparison is the actual map on Hom. -/
theorem Functor.extPrecompMap_mk₀ {Y : C} (f : X ⟶ Y) :
    F.extPrecompMap a Y 0 (Ext.mk₀ f) = Ext.mk₀ (a ≫ F.map f) := by
  rw [Functor.extPrecompMap_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

/-- The original comparison respects Yoneda composition in the coefficient variable. -/
theorem Functor.extPrecompMap_comp {Y Z : C} {i j k : ℕ}
    (x : Ext.{w} X Y i) (y : Ext.{w} Y Z j) (h : i + j = k) :
    F.extPrecompMap a Z k (x.comp y h) =
      (F.extPrecompMap a Y i x).comp (y.mapExactFunctor F) h := by
  rw [Functor.extPrecompMap_apply, Functor.extPrecompMap_apply,
    Ext.mapExactFunctor_comp, Ext.comp_assoc _ _ _ (Nat.zero_add i) h (by omega)]

/-- A degree-zero comparison and actual acyclicity of images of injectives imply
bijectivity of the original comparison in every degree. -/
theorem Functor.extPrecompMap_bijective_of_acyclic_injectives [EnoughInjectives C]
    (h₀ : ∀ Y : C, Function.Bijective (F.extPrecompMap a Y 0))
    (hI : ∀ (I : C) [Injective I] (n : ℕ),
      Subsingleton (Ext.{w'} A (F.obj I) (n + 1))) (Y : C) (n : ℕ) :
    Function.Bijective (F.extPrecompMap a Y n) := by
  classical
  induction n generalizing Y with
  | zero => exact h₀ Y
  | succ n hn =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    let : Subsingleton (Ext.{w'} A (S.map F).X₂ (n + 1)) := hI S.X₂ n
    refine AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (F.extPrecompMap a S.X₂ n) (F.extPrecompMap a S.X₃ n)
      (F.extPrecompMap a S.X₁ (n + 1)) ?_ ?_
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' X hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' A (hS.map_of_exact F) n (n + 1) rfl))
      (hn _).surjective (hn _)
      (fun x => Ext.covariant_sequence_exact₁ X hS x (Ext.eq_zero_of_injective _) rfl)
      (fun x => Ext.covariant_sequence_exact₁ A (hS.map_of_exact F) x
        (Subsingleton.elim _ _) rfl)
    · ext x
      change (F.extPrecompMap a S.X₂ n x).comp (Ext.mk₀ (F.map S.g)) (Nat.add_zero n) =
        F.extPrecompMap a S.X₃ n (x.comp (Ext.mk₀ S.g) (Nat.add_zero n))
      rw [Functor.extPrecompMap_comp, Ext.mapExactFunctor_mk₀]
    · ext x
      change (F.extPrecompMap a S.X₃ n x).comp (hS.map_of_exact F).extClass rfl =
        F.extPrecompMap a S.X₁ (n + 1) (x.comp hS.extClass rfl)
      rw [Functor.extPrecompMap_comp, Ext.mapExactFunctor_extClass]

/-- The additive equivalence whose forward map is the original exact-functor comparison. -/
def Functor.extPrecompAddEquivOfAcyclicInjectives [EnoughInjectives C]
    (h₀ : ∀ Y : C, Function.Bijective (F.extPrecompMap a Y 0))
    (hI : ∀ (I : C) [Injective I] (n : ℕ),
      Subsingleton (Ext.{w'} A (F.obj I) (n + 1))) (Y : C) (n : ℕ) :
    Ext.{w} X Y n ≃+ Ext.{w'} A (F.obj Y) n :=
  AddEquiv.ofBijective (F.extPrecompMap a Y n)
    (F.extPrecompMap_bijective_of_acyclic_injectives a h₀ hI Y n)

end CategoryTheory
