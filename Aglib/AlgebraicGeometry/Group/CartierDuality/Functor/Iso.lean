/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.EvaluationLaws

/-! Actual dual isomorphisms and transposition of the original evaluation. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory BraidedCategory
open Scheme.OverField
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.Group.CartierDuality

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] {G H : Grp (FScheme k)}
  [IsFinite G.X.hom] [IsFinite H.X.hom] [IsCommMonObj G.X] [IsCommMonObj H.X]

/-- The original contravariant dual map sends a given isomorphism to an isomorphism. -/
def dualIso (e : G ≅ H) : dualGroup H ≅ dualGroup G where
  hom := dualMap e.hom
  inv := dualMap e.inv
  hom_inv_id := by rw [← dualMap_comp, Iso.inv_hom_id, dualMap_id]
  inv_hom_id := by rw [← dualMap_comp, Iso.hom_inv_id, dualMap_id]

/-- The other adjoint of the evaluation transported by `e` uses the
original bidual isomorphism and original contravariant dual of `e`. -/
def evaluationTransposeIso (e : H ≅ dualGroup G) : G ≅ dualGroup H :=
  bidualIso G ≪≫ dualIso e

/-- The two original evaluation descriptions agree as whole scheme maps. -/
theorem evaluation_transpose (e : H ≅ dualGroup G) :
    (𝟙 G.X ⊗ₘ e.hom.hom.hom) ≫ evaluation G =
      (β_ G.X H.X).hom ≫
        (𝟙 H.X ⊗ₘ (evaluationTransposeIso e).hom.hom.hom) ≫ evaluation H := by
  let B := (dualGroup G).X
  let C := (dualGroup (dualGroup G)).X
  let a : H.X ⟶ B := e.hom.hom.hom
  let b : G.X ⟶ C := (bidualIso G).hom.hom.hom
  let d : C ⟶ (dualGroup H).X := (dualMap e.hom).hom.hom
  have hB := braiding_naturality (𝟙 G.X) a
  have hN : (a ⊗ₘ 𝟙 C) ≫ evaluation (dualGroup G) =
      (𝟙 H.X ⊗ₘ d) ≫ evaluation H := evaluation_naturality e.hom
  change (𝟙 G.X ⊗ₘ a) ≫ evaluation G =
    (β_ G.X H.X).hom ≫ (𝟙 H.X ⊗ₘ (b ≫ d)) ≫ evaluation H
  calc
    _ = (𝟙 G.X ⊗ₘ a) ≫ (β_ G.X B).hom ≫ (𝟙 B ⊗ₘ b) ≫
        evaluation (dualGroup G) :=
      congrArg (fun t => (𝟙 G.X ⊗ₘ a) ≫ t) (evaluation_bidual G).symm
    _ = (β_ G.X H.X).hom ≫ (a ⊗ₘ 𝟙 G.X) ≫ (𝟙 B ⊗ₘ b) ≫
        evaluation (dualGroup G) := by
      simpa only [Category.assoc] using congrArg
        (fun t => t ≫ (𝟙 B ⊗ₘ b) ≫ evaluation (dualGroup G)) hB
    _ = (β_ G.X H.X).hom ≫ (𝟙 H.X ⊗ₘ b) ≫ (a ⊗ₘ 𝟙 C) ≫
        evaluation (dualGroup G) := by
      simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
    _ = (β_ G.X H.X).hom ≫ (𝟙 H.X ⊗ₘ b) ≫ (𝟙 H.X ⊗ₘ d) ≫ evaluation H := by rw [hN]
    _ = _ := by simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp]

end AlgebraicGeometry.Scheme.Group.CartierDuality
