/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Endomorphism

/-!
# Functoriality and natural-isomorphism coherence of actual automorphism conjugacy.

Source: `lean/R5Lab/Aglib/CategoryTheory/Functor/AutomorphismTransport.lean`
at frozen R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `d1d953466ad25e13841105048df46850f345400ca2824025c5a79848d1d217ce`.
Native objects and canonical maps are reused; provenance does not select declaration namespaces.
-/

@[expose] public section

open CategoryTheory
namespace CategoryTheory.Functor
universe u v u' v'

section CategoricalCoherence
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]

lemma mapIso_conjugate (F : C ⥤ D) {A B : C} (e : A ≅ B) (α : Aut A) :
    F.mapIso (Aut.autMulEquivOfIso e α) =
      Aut.autMulEquivOfIso (F.mapIso e) (F.mapIso α) := by
  apply Iso.ext
  change F.map (e.inv ≫ α.hom ≫ e.hom) =
    F.map e.inv ≫ F.map α.hom ≫ F.map e.hom
  simp only [Functor.map_comp]

end CategoricalCoherence
end CategoryTheory.Functor

namespace CategoryTheory.NatIso
universe u v u' v'
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]

lemma mapAut_conjugate {F G : C ⥤ D} (e : F ≅ G) (A : C) (α : Aut A) :
    Aut.autMulEquivOfIso (e.app A) (F.mapIso α) = G.mapIso α := by
  apply Iso.ext
  change (e.app A).inv ≫ F.map α.hom ≫ (e.app A).hom = G.map α.hom
  rw [← NatIso.naturality_1 e α.hom]
  simp
end CategoryTheory.NatIso
