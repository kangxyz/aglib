/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Homology

/-!
# Conservativity of the right-derived functor of an exact functor

An additive functor which preserves homology and reflects isomorphisms has
a conservative native bounded-below right-derived functor. The proof uses
the original homology comparison and detection of isomorphisms by native
derived homology. The source has enough injectives, and both chosen derived
categories retain independent category, morphism and derived universes.

Scalar-forgetting comparisons for module-sheaf base change consume this
instance. No alternative derived category or derived functor is introduced.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w u' v' w'

namespace CategoryTheory.Functor

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology] [F.ReflectsIsomorphisms]

/-- The installed right-derived functor of an exact conservative additive functor
reflects isomorphisms. -/
instance rightDerivedFunctorPlus_reflectsIsomorphisms :
    F.rightDerivedFunctorPlus.ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    rw [DerivedCategory.Plus.isIso_iff]
    intro n
    have h : IsIso
        ((F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor B n).map f) := by
      change IsIso
        ((DerivedCategory.Plus.homologyFunctor B n).map (F.rightDerivedFunctorPlus.map f))
      infer_instance
    have : IsIso (F.map ((DerivedCategory.Plus.homologyFunctor A n).map f)) :=
      (NatIso.isIso_map_iff (F.rightDerivedFunctorPlusHomologyIso n) f).mp h
    exact isIso_of_reflects_iso _ F

end CategoryTheory.Functor
