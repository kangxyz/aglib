/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ScalarExtensionCoordinates

/-! # Naturality of specified scalar-extension coordinates -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
namespace ModuleCat
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {M M' N N' : ModuleCat.{u} R} {P P' : ModuleCat.{u} S}

/-- Two original naturality squares determine the coordinate square, without
normalizing any underlying tensor carrier. -/
theorem scalarExtensionCoordinatesIso_naturality
    (d : (extendScalars (algebraMap R S)).obj M ≅ P)
    (d' : (extendScalars (algebraMap R S)).obj M' ≅ P')
    (e : M ≅ N) (e' : M' ≅ N')
    (a : M ⟶ M') (b : N ⟶ N') (p : P ⟶ P')
    (hd : (extendScalars (algebraMap R S)).map a ≫ d'.hom = d.hom ≫ p)
    (he : a ≫ e'.hom = e.hom ≫ b) :
    p ≫ (scalarExtensionCoordinatesIso d' e').hom =
      (scalarExtensionCoordinatesIso d e).hom ≫
        (extendScalarsAlgebraIso R S N).inv ≫
        (extendScalars (algebraMap R S)).map b ≫
        (extendScalarsAlgebraIso R S N').hom := by
  apply (cancel_epi d.hom).mp
  simp only [scalarExtensionCoordinatesIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← hd, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, he, Functor.map_comp]
  simp only [Category.assoc]

end ModuleCat
