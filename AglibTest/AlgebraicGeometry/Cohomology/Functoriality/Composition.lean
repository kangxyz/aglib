/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Composition

/-! A section/retraction consumer deliberately retains arbitrary scheme
maps, including generally nonflat sections. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.OverField

universe u

example {S X : Scheme.{u}} (p : X ⟶ S) (s : S ⟶ X) (h : s ≫ p = 𝟙 S) (n : ℕ) :
    (structureCohomologyPullback s n).comp (structureCohomologyPullback p n) =
      AddMonoidHom.id _ := by
  rw [← structureCohomologyPullback_comp, h, structureCohomologyPullback_id]

example {k : Type u} [Field k] {X Y Z : FScheme k}
    (p : Y ⟶ X) (q : Z ⟶ Y) (n : ℕ) :
    structureCohomologyPullbackLinear (q ≫ p) n =
      (structureCohomologyPullbackLinear q n) ∘ₗ structureCohomologyPullbackLinear p n :=
  structureCohomologyPullbackLinear_comp p q n
