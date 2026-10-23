/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Hypercohomology.SheafComparison

/-!
# Ordinary sheaf cohomology with larger coefficient universes

Mathlib's `Sheaf.cohomologyPresheaf` uses equal coefficient and site-Hom
universes. Transfer sheafification needs a larger coefficient universe. We
therefore use the existing universe-lifted free abelian representing sheaf
and the same actual Ext bifunctor. The source already represents sections.

This construction is compared to ordinary Mathlib sheaf cohomology whenever
its universes apply, and to the existing derived-Hom hypercohomology of a
single sheaf in all supported universes. No abstract cohomology provider is
introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian Opposite

universe w w' t v u

namespace CategoryTheory.Sheaf.LargeCohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]

/-- Actual Ext from the existing free abelian sheaf representing evaluation. -/
def presheafFunctor (n : ℕ) :
    Sheaf J AddCommGrpCat.{max v t} ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{w} :=
  Functor.flip ((Hypercohomology.freeAbelianSheafFunctor J).op ⋙ extFunctor n)

/-- The ordinary cohomology presheaf with universe-lifted representable source. -/
abbrev presheaf (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ) :
    Cᵒᵖ ⥤ AddCommGrpCat.{w} := (presheafFunctor J n).obj F

/-- The corresponding ordinary sheaf cohomology group. -/
abbrev H (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ) (X : C) : AddCommGrpCat.{w} :=
  (presheaf J F n).obj (op X)

/-- The cohomology group is literally Ext from the representing free abelian sheaf. -/
theorem H_eq (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ) (X : C) :
    H J F n X = AddCommGrpCat.of (Ext (Hypercohomology.freeAbelianSheaf J X) F n) := rfl

/-- Restrictions are actual precomposition by the degree-zero Ext class of the source map. -/
theorem restriction_apply (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ)
    {X Y : C} (f : X ⟶ Y) (x : H J F n Y) :
    (presheaf J F n).map f.op x =
      (Ext.mk₀ ((Hypercohomology.freeAbelianSheafFunctor J).map f)).comp x
        (zero_add n) := rfl

/-- The enlarged-universe construction is the actual existing single-complex hypercohomology. -/
def singleComparison [HasDerivedCategory.{w'} (Sheaf J AddCommGrpCat.{max v t})]
    (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ) (X : C) :
    Hypercohomology.H J ((CochainComplex.singleFunctor _ 0).obj F) (n : ℤ) X ≃+
      H J F n X := Ext.homAddEquiv.symm

end CategoryTheory.Sheaf.LargeCohomology

namespace CategoryTheory.Sheaf.LargeCohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]

/-- When the universes agree, the source is naturally the ordinary Mathlib source. -/
def ordinarySourceIso :
    Hypercohomology.freeAbelianSheafFunctor J ≅
      yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
        presheafToSheaf J AddCommGrpCat.{v} :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerRight uliftYonedaIsoYoneda
      ((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free))
    (presheafToSheaf J AddCommGrpCat.{v})

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

/-- The comparison with Mathlib is natural in both the coefficient and site variables. -/
def ordinaryComparison (n : ℕ) :
    presheafFunctor J n ≅ Sheaf.cohomologyPresheafFunctor J n :=
  (flipFunctor _ _ _).mapIso
    (Functor.isoWhiskerRight (NatIso.op (ordinarySourceIso J).symm) (extFunctor n))

end CategoryTheory.Sheaf.LargeCohomology
