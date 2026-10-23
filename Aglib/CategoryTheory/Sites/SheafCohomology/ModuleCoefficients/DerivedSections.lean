/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Represented sections and the original injective-resolution Hom complex

The first comparison identifies the native Hom complex from a single object
with application of the original additive represented functor. This retains
the original differential and is the lower supplier for derived sections.
-/

@[expose] public noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex CochainComplex.HomComplex

namespace CategoryTheory.Sheaf.ModuleCoefficients

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The actual Hom complex from a degree-zero single object is represented sections. -/
def singleHomComplexIso (X : C) (K : CochainComplex C ℤ) :
    HomComplex ((CochainComplex.singleFunctor C 0).obj X) K ≅
      (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (Cochain.fromSingleEquiv (X := X) (K := K) (zero_add n)).toAddCommGrpIso)
    (by
      intro i j hij
      ext α
      obtain ⟨a, rfl⟩ := Cochain.fromSingleMk_surjective α i (zero_add i)
      symm
      change (Cochain.fromSingleEquiv (zero_add j))
        (δ i j (Cochain.fromSingleMk a (zero_add i))) = _
      rw [Cochain.δ_fromSingleMk _ (zero_add i) j j (zero_add j),
        Cochain.fromSingleEquiv_fromSingleMk]
      change a ≫ K.d i j =
        (Cochain.fromSingleEquiv (zero_add i))
          (Cochain.fromSingleMk a (zero_add i)) ≫ K.d i j
      rw [Cochain.fromSingleEquiv_fromSingleMk])

end CategoryTheory.Sheaf.ModuleCoefficients
