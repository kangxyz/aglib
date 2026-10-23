/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.AcyclicComparison

/-!
# Composite comparisons and acyclic injective images

The original exact-functor comparison for a composite is the composite of
the two original maps. If the first comparison already computes cohomology,
the second comparison on its image is determined by degree zero and actual
acyclicity of the composite images of injectives. Injectives need not stay
injective after either functor. All three Ext universes remain independent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory

universe u v u' v' u'' v'' w w' w''

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
  {E : Type u''} [Category.{v''} E] [Abelian E] [HasExt.{w''} E]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  {X : C} {A : D} {B : E} (a : A ⟶ F.obj X) (b : B ⟶ G.obj A)

/-- Exact-functor composition retains the two original source maps and Ext comparisons. -/
theorem Functor.extPrecompMap_compFunctor (Y : C) (n : ℕ) (x : Ext X Y n) :
    (F ⋙ G).extPrecompMap (b ≫ G.map a) Y n x =
      G.extPrecompMap b (F.obj Y) n (F.extPrecompMap a Y n x) := by
  simp only [Functor.extPrecompMap_apply, Ext.comp_mapExactFunctor,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rw [← Ext.mk₀_comp_mk₀]
  exact Ext.comp_assoc _ _ _ (Nat.zero_add 0) (Nat.zero_add n) (by omega)

/-- A first cohomology comparison reduces a second one to its actual injective-image tests. -/
theorem Functor.extPrecompMap_bijective_on_image_of_acyclic_injectives
    [EnoughInjectives C]
    (hF : ∀ (Y : C) (n : ℕ), Function.Bijective (F.extPrecompMap a Y n))
    (h₀ : ∀ Y : C, Function.Bijective (G.extPrecompMap b (F.obj Y) 0))
    (hI : ∀ (I : C) [Injective I] (n : ℕ),
      Subsingleton (Ext B (G.obj (F.obj I)) (n + 1))) (Y : C) (n : ℕ) :
    Function.Bijective (G.extPrecompMap b (F.obj Y) n) := by
  have hcomp (Z : C) (q : ℕ) :
      G.extPrecompMap b (F.obj Z) q ∘ F.extPrecompMap a Z q =
        (F ⋙ G).extPrecompMap (b ≫ G.map a) Z q := by
    funext x
    exact (F.extPrecompMap_compFunctor G a b Z q x).symm
  have hz : ∀ Z : C,
      Function.Bijective ((F ⋙ G).extPrecompMap (b ≫ G.map a) Z 0) := by
    intro Z
    rw [← hcomp Z 0]
    exact (h₀ Z).comp (hF Z 0)
  apply (Function.Bijective.of_comp_iff
    (G.extPrecompMap b (F.obj Y) n) (hF Y n)).mp
  rw [hcomp Y n]
  exact (F ⋙ G).extPrecompMap_bijective_of_acyclic_injectives
    (b ≫ G.map a) hz hI Y n

end CategoryTheory
