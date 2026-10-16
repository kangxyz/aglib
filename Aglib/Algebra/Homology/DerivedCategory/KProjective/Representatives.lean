/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective


/-!
# Actual representatives of derived morphisms from K-projective complexes

In an arbitrary abelian category with a derived category, K-projectivity
supplies an actual chain representative for each derived morphism and an
actual chain homotopy for each derived equality. The canonical functors and
their factorization isomorphism are retained throughout.
-/
/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/Algebra/Homology/KProjectiveRepresentatives.lean`.
SHA-256: `34fd0442aa6021f9144594551cbb5204e3e8f3822e395e7e31395ccc5264ad2a`.
Selected source lines: 1–61.
Actual source objects, maps, hypotheses and independent universes are preserved.
-/

@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {K L : CochainComplex C ℤ} [K.IsKProjective]

/-- An actual derived morphism with K-projective source has a chain
representative, with its image equal to the original morphism. -/
theorem exists_chain_representative_of_isKProjective
    (α : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    ∃ f : K ⟶ L, DerivedCategory.Q.map f = α := by
  let e := DerivedCategory.quotientCompQhIso C
  obtain ⟨β, hβ⟩ := (CochainComplex.IsKProjective.Qh_map_bijective K
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L)).surjective
      (e.hom.app K ≫ α ≫ e.inv.app L)
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective β
  refine ⟨f, ?_⟩
  rw [← NatIso.naturality_1 e f]
  change e.inv.app K ≫ DerivedCategory.Qh.map
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f) ≫ e.hom.app L = α
  rw [hβ]
  simp

/-- Equality in the actual derived category from a K-projective source is
witnessed by an actual chain homotopy. -/
def homotopyOfDerivedEqOfIsKProjective (f g : K ⟶ L)
    (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) : Homotopy f g := by
  let e := DerivedCategory.quotientCompQhIso C
  apply HomotopyCategory.homotopyOfEq f g
  apply (CochainComplex.IsKProjective.Qh_map_bijective K
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L)).injective
  have hf := NatIso.naturality_2 e f
  have hg := NatIso.naturality_2 e g
  exact hf.symm.trans ((congrArg (fun t => e.hom.app K ≫ t ≫ e.inv.app L) h).trans hg)

end CochainComplex
