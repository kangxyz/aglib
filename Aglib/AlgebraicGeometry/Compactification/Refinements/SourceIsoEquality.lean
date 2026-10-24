/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.SourceIso

/-! # Equality of original source identifications -/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.DenseCompactification

variable {X X' S : Scheme.{u}} {f : X ⟶ S} (f' : X' ⟶ S)
  {e₀ e₁ : X' ≅ X} (he : e₀ = e₁) (h₀ : e₀.hom ≫ f = f') (h₁ : e₁.hom ≫ f = f')

/-- Equal original source identifications induce equal transport functors. -/
def sourceIsoEquality : sourceIso f' e₀ h₀ ≅ sourceIso f' e₁ h₁ :=
  eqToIso (by subst he; rfl)

/-- Equality transport acts by the identity on each original ambient scheme. -/
@[simp]
lemma sourceIsoEquality_hom (C : DenseCompactification f) :
    ((sourceIsoEquality f' he h₀ h₁).hom.app C).hom = 𝟙 C.Xbar := by
  subst he
  rfl

end AlgebraicGeometry.Scheme.Hom.DenseCompactification
