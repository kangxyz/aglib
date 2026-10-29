/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# A point specializes a cartesian shear

An isomorphism `G ⊗ P ≅ P ⊗ P` over the second projection restricts along
an actual terminal-object point of `P` to an isomorphism `G ≅ P`. Both maps
use the given shear and its inverse. No group or action structure is needed.

Consumer: intrinsic global-point trivialization of the existing sheaf torsor.
-/

@[expose] public section

namespace CategoryTheory.CartesianMonoidalCategory

open MonoidalCategory Limits

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {G P T : C}

/-- Restrict an actual shear isomorphism along an actual terminal-object point. -/
def isoOfShear (hT : IsTerminal T) (e : G ⊗ P ≅ P ⊗ P)
    (he : e.hom ≫ snd P P = snd G P) (s : T ⟶ P) : G ≅ P := by
  let iG : G ⟶ G ⊗ P := lift (𝟙 G) (hT.from G ≫ s)
  let iP : P ⟶ P ⊗ P := lift (𝟙 P) (hT.from P ≫ s)
  let f : G ⟶ P := iG ≫ e.hom ≫ fst P P
  let g : P ⟶ G := iP ≫ e.inv ≫ fst G P
  have hinv : e.inv ≫ snd G P = snd P P := by
    calc
      e.inv ≫ snd G P = e.inv ≫ (e.hom ≫ snd P P) :=
        congrArg (fun q => e.inv ≫ q) he.symm
      _ = snd P P := by rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hfT : f ≫ hT.from P = hT.from G := hT.hom_ext _ _
  have hgT : g ≫ hT.from G = hT.from P := hT.hom_ext _ _
  have hf : f ≫ iP = iG ≫ e.hom := by
    apply hom_ext
    · simp only [f, iP, Category.assoc, lift_fst, Category.comp_id]
    · simp only [iP, Category.assoc, lift_snd, he]
      rw [← Category.assoc, hfT]
      exact (lift_snd (𝟙 G) (hT.from G ≫ s)).symm
  have hg : g ≫ iG = iP ≫ e.inv := by
    apply hom_ext
    · simp only [g, iG, Category.assoc, lift_fst, Category.comp_id]
    · simp only [iG, Category.assoc, lift_snd, hinv]
      rw [← Category.assoc, hgT]
      exact (lift_snd (𝟙 P) (hT.from P ≫ s)).symm
  refine ⟨f, g, ?_, ?_⟩
  · calc
      f ≫ g = (f ≫ iP) ≫ e.inv ≫ fst G P := by simp only [g, Category.assoc]
      _ = (iG ≫ e.hom) ≫ e.inv ≫ fst G P := by rw [hf]
      _ = 𝟙 G := by
        rw [Category.assoc, e.hom_inv_id_assoc]
        exact lift_fst _ _
  · calc
      g ≫ f = (g ≫ iG) ≫ e.hom ≫ fst P P := by simp only [f, Category.assoc]
      _ = (iP ≫ e.inv) ≫ e.hom ≫ fst P P := by rw [hg]
      _ = 𝟙 P := by
        rw [Category.assoc, e.inv_hom_id_assoc]
        exact lift_fst _ _

/-- The forward map is the original shear evaluated at the given point. -/
@[simp]
theorem isoOfShear_hom (hT : IsTerminal T) (e : G ⊗ P ≅ P ⊗ P)
    (he : e.hom ≫ snd P P = snd G P) (s : T ⟶ P) :
    (isoOfShear hT e he s).hom =
      lift (𝟙 G) (hT.from G ≫ s) ≫ e.hom ≫ fst P P := rfl

/-- The inverse is the original inverse shear evaluated at the same point. -/
@[simp]
theorem isoOfShear_inv (hT : IsTerminal T) (e : G ⊗ P ≅ P ⊗ P)
    (he : e.hom ≫ snd P P = snd G P) (s : T ⟶ P) :
    (isoOfShear hT e he s).inv =
      lift (𝟙 P) (hT.from P ≫ s) ≫ e.inv ≫ fst G P := rfl

end CategoryTheory.CartesianMonoidalCategory
