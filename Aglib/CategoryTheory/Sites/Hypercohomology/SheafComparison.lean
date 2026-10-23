/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Hypercohomology.Basic

/-!
# Comparison with ordinary sheaf cohomology

When the coefficient and site-Hom universes agree, the harmless universe lift
in the free abelian representable has a canonical removal isomorphism. Using
that actual isomorphism and Mathlib's derived-Hom/Ext identification, the
unbounded hypercohomology of a sheaf placed in degree zero agrees with its
ordinary sheaf cohomology. Degree zero is additionally identified with sections.
-/

@[expose] public noncomputable section

universe w w' v u

open CategoryTheory CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf.Hypercohomology

section HomTransport

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- Transport of derived morphisms along specified isomorphisms is additive. -/
def homCongrAddEquiv {P P' Q Q' : DerivedCategory A} (eP : P ≅ P') (eQ : Q ≅ Q') :
    (P ⟶ Q) ≃+ (P' ⟶ Q') where
  toEquiv := Iso.homCongr eP eQ
  map_add' f g := by simp [Iso.homCongr]

end HomTransport

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]

/-- Removing the explicit Yoneda universe lift identifies the actual source with
the source used in Mathlib's ordinary sheaf cohomology. -/
def freeAbelianSheafIso (X : C) :
    freeAbelianSheaf J X ≅
      (presheafToSheaf J AddCommGrpCat.{v}).obj (yoneda.obj X ⋙ AddCommGrpCat.free) :=
  (presheafToSheaf J AddCommGrpCat).mapIso
    (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).mapIso
      (uliftYonedaIsoYoneda.app X))

variable [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{v})]

/-- In degree-zero single complexes, unbounded hypercohomology agrees with ordinary sheaf
cohomology. `HasExt` controls the universe of the existing shrunk Ext groups only. -/
def singleComparison [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) (X : C) :
    H J ((CochainComplex.singleFunctor _ 0).obj F) (n : ℤ) X ≃+ F.H' n X :=
  (homCongrAddEquiv
    ((DerivedCategory.singleFunctor _ 0).mapIso (freeAbelianSheafIso J X))
    (Iso.refl _)).trans Ext.homAddEquiv.symm

/-- The single-complex hypercohomology in degree zero is the group of sections.
This uses full faithfulness of the single functor, not exact evaluation. -/
def singleZeroSections (F : Sheaf J AddCommGrpCat.{v}) (X : C) :
    H J ((CochainComplex.singleFunctor _ 0).obj F) 0 X ≃+ F.obj.obj (op X) := by
  letI : HasExt.{w} (Sheaf J AddCommGrpCat.{v}) := hasExt_of_hasDerivedCategory _
  exact ((Ext.homAddEquiv (X := freeAbelianSheaf J X) (Y := F) (n := 0)).symm.trans
    Ext.addEquiv₀).trans (sectionsAddEquiv J X F)

end CategoryTheory.Sheaf.Hypercohomology
