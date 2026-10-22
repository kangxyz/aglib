/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.SchemeTheoreticImage.Dominance
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Compactification by scheme-theoretic image

A quasi-compact immersion into a proper scheme over the base gives a compactification:
take its native scheme-theoretic image. The resulting open immersion is dominant.
This construction is valid over arbitrary schemes; no Noetherian hypothesis is used.
It supplies the elementary building blocks for Nagata compactification, not the general
gluing or existence theorem.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S P : Scheme.{u}} (f : X ⟶ S)

/-- A compactification of a scheme morphism is an open immersion followed by a proper
morphism, whose composite is the original morphism. Density is not part of this basic
contract; the scheme-theoretic-image construction below also supplies it. -/
structure Compactification where
  /-- The scheme containing the original source. -/
  Xbar : Scheme.{u}
  /-- The open immersion of the original source. -/
  j : X ⟶ Xbar
  /-- The proper structural morphism. -/
  p : Xbar ⟶ S
  isOpenImmersion_j : IsOpenImmersion j
  isProper_p : IsProper p
  /-- The original structural morphism is unchanged. -/
  fac : j ≫ p = f

attribute [instance] Compactification.isOpenImmersion_j Compactification.isProper_p
attribute [reassoc (attr := simp)] Compactification.fac

namespace Compactification

/-- The native scheme-theoretic image compactifies a quasi-compact immersion into a
proper scheme over the base. All maps are the canonical image-factorization maps. -/
def ofImmersion (j : X ⟶ P) (p : P ⟶ S) [IsImmersion j] [QuasiCompact j]
    [IsProper p] (h : j ≫ p = f) : Compactification f where
  Xbar := j.image
  j := j.toImage
  p := j.imageι ≫ p
  isOpenImmersion_j := inferInstance
  isProper_p := inferInstance
  fac := by rw [← Category.assoc, j.toImage_imageι, h]

/-- The open immersion in the image compactification has dense image. -/
instance ofImmersion_isDominant (j : X ⟶ P) (p : P ⟶ S)
    [IsImmersion j] [QuasiCompact j] [IsProper p] (h : j ≫ p = f) :
    IsDominant (ofImmersion f j p h).j :=
  inferInstanceAs (IsDominant j.toImage)

/-- The actual image-factor source is schematically dense, without a
reducedness assumption on the ambient compactification. -/
instance ofImmersion_isSchemeTheoreticallyDominant (j : X ⟶ P) (p : P ⟶ S)
    [IsImmersion j] [QuasiCompact j] [IsProper p] (h : j ≫ p = f) :
    IsSchemeTheoreticallyDominant (ofImmersion f j p h).j :=
  Scheme.isSchemeTheoreticallyDominant_toImage j

end Compactification

/-- An actual quasi-compact immersion into a proper scheme gives a compactification
with dense open source, preserving the specified structural morphism. -/
theorem exists_compactification_of_immersion (j : X ⟶ P) (p : P ⟶ S)
    [IsImmersion j] [QuasiCompact j] [IsProper p] (h : j ≫ p = f) :
    ∃ C : Compactification f, IsDominant C.j :=
  ⟨Compactification.ofImmersion f j p h, inferInstance⟩

end AlgebraicGeometry.Scheme.Hom
