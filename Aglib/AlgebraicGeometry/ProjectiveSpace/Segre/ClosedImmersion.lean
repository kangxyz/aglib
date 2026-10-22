/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Segre.Map
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Segre.ChartSurjectivity

/-!
# The original binary Segre closed immersion
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ProjectiveSpace.Segre

variable (R : Type u) [CommRing R] (ι κ : Type u)

/-- The original binary Segre morphism from the native scheme pullback. -/
def embedding : product R ι κ ⟶ ProjectiveSpace R (ι × κ) :=
  map (first R ι κ) (second R ι κ)

/-- The original binary Segre map is a closed immersion over any commutative base. -/
instance instIsClosedImmersionEmbedding : IsClosedImmersion (embedding R ι κ) := by
  apply ChartGluing.map_isClosedImmersion
    (sourceOpen (first R ι κ) (second R ι κ))
    (sectionChartHom (first R ι κ) (second R ι κ))
    (sectionChartHom_compatible _ _) (iSup_sourceOpen_eq_top _ _)
  · intro a b
    rw [sectionChartHom_ratio, basicOpen_sectionValue]
  · rintro ⟨a, b⟩
    exact isAffineOpen_sourceOpen R a b
  · rintro ⟨a, b⟩
    exact sectionChartHom_surjective R a b

/-- Segre preserves the original structural morphism, without a chosen replacement base map. -/
@[reassoc (attr := simp)]
theorem embedding_toSpec :
    embedding R ι κ ≫ toSpec R (ι × κ) = first R ι κ ≫ toSpec R ι :=
  map_toSpec _ _

end AlgebraicGeometry.ProjectiveSpace.Segre
