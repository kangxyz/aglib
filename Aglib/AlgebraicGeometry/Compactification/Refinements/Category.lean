/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Basic

/-!
# Schematically dense compactifications and their actual refinements

The objects retain the existing compactification, including its original open
immersion and structural morphism. Refinements are proper morphisms preserving
both triangles. No common-refinement or existence assertion is part of the data.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A compactification whose original open source is schematically dense. -/
structure DenseCompactification extends Compactification f where
  /-- Schematic density retains the scheme structure, including nilpotents. -/
  isSchemeTheoreticallyDominant_j : IsSchemeTheoreticallyDominant j

attribute [instance] DenseCompactification.isSchemeTheoreticallyDominant_j

namespace DenseCompactification

instance (C : DenseCompactification f) : IsOpenImmersion C.j :=
  C.toCompactification.isOpenImmersion_j

instance (C : DenseCompactification f) : IsProper C.p :=
  C.toCompactification.isProper_p

variable {f}

/-- A refinement is an actual proper map over the base, identical on the
specified original open source. -/
structure Refinement (C D : DenseCompactification f) where
  /-- The underlying map of the compactifying schemes. -/
  hom : C.Xbar ⟶ D.Xbar
  /-- Refinement maps are proper. -/
  isProper_hom : IsProper hom
  /-- The original open immersion is unchanged. -/
  open_fac : C.j ≫ hom = D.j
  /-- The original structural morphism is unchanged. -/
  base_fac : hom ≫ D.p = C.p

attribute [instance] Refinement.isProper_hom
attribute [reassoc (attr := simp)] Refinement.open_fac Refinement.base_fac

namespace Refinement

variable {C D E : DenseCompactification f}

@[ext]
lemma ext {a b : Refinement C D} (h : a.hom = b.hom) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- The identity refinement has the original identity map. -/
def id (C : DenseCompactification f) : Refinement C C where
  hom := 𝟙 C.Xbar
  isProper_hom := inferInstance
  open_fac := Category.comp_id _
  base_fac := Category.id_comp _

/-- Refinements compose by composition of their original proper maps. -/
def comp (a : Refinement C D) (b : Refinement D E) : Refinement C E where
  hom := a.hom ≫ b.hom
  isProper_hom := inferInstance
  open_fac := by rw [← Category.assoc, a.open_fac, b.open_fac]
  base_fac := by rw [Category.assoc, b.base_fac, a.base_fac]

end Refinement

instance : Category (DenseCompactification f) where
  Hom := Refinement
  id := Refinement.id
  comp := Refinement.comp
  id_comp a := by apply Refinement.ext; exact Category.id_comp _
  comp_id a := by apply Refinement.ext; exact Category.comp_id _
  assoc a b c := by apply Refinement.ext; exact Category.assoc _ _ _

@[simp]
lemma id_hom (C : DenseCompactification f) : (𝟙 C : C ⟶ C).hom = 𝟙 C.Xbar := rfl

@[simp]
lemma comp_hom {C D E : DenseCompactification f} (a : C ⟶ D) (b : D ⟶ E) :
    (a ≫ b).hom = a.hom ≫ b.hom := rfl

/-- Forget only density and the open source, retaining the actual scheme over S. -/
def forgetToOver : DenseCompactification f ⥤ Over S where
  obj C := Over.mk C.p
  map a := Over.homMk a.hom a.base_fac
  map_id C := by ext; rfl
  map_comp a b := by ext; rfl

instance : (forgetToOver (f := f)).Faithful where
  map_injective h := Refinement.ext (congrArg (fun a => a.left) h)

end DenseCompactification

end AlgebraicGeometry.Scheme.Hom
