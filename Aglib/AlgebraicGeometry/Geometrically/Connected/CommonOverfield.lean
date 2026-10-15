/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Compatible common overfields and connectedness descent for B02 FE-04.
Repository basis: `1e2b2a1a27c19ecbb9575ef9eeb57d0ae46f520e`.
All schemes and extension fields are arbitrary in the displayed universe. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Geometrically
universe u

/-- The two actual base-field maps into the common overfield agree. -/
theorem commonClosure_tower (F K : Type u) [Field F] [Field K] [Algebra F K] :
    IsScalarTower F K (AlgebraicClosure K) := inferInstance

/-- An actual base-field embedding of the chosen algebraic closure into the
common overfield. -/
def commonClosureEmbedding (F K : Type u) [Field F] [Field K] [Algebra F K] :
    AlgebraicClosure F →ₐ[F] AlgebraicClosure K := IsAlgClosed.lift

/-- Compatibility is the explicit equality of actual ring maps from the
original field into the common overfield. -/
theorem commonClosureEmbedding_compatible
    (F K : Type u) [Field F] [Field K] [Algebra F K] :
    (commonClosureEmbedding F K).toRingHom.comp (algebraMap F (AlgebraicClosure F)) =
      (algebraMap K (AlgebraicClosure K)).comp (algebraMap F K) := by
  ext x
  change (commonClosureEmbedding F K) (algebraMap F (AlgebraicClosure F) x) =
    algebraMap K (AlgebraicClosure K) (algebraMap F K x)
  rw [← IsScalarTower.algebraMap_apply F K (AlgebraicClosure K)]
  exact (commonClosureEmbedding F K).commutes x

/-- Any actual morphism between spectra of fields is surjective. -/
theorem fieldSpec_surjective
    {K L : Type u} [Field K] [Field L]
    (b : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)) : Surjective b := by
  constructor
  intro x
  exact ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩

/-- Connectedness descends along the actual projection of an arbitrary scheme
base change by a field extension. -/
theorem connectedSpace_of_fieldBaseChange
    {K L : Type u} [Field K] [Field L] {Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of K))
    (b : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
    (h : ConnectedSpace (Limits.pullback q b : Scheme.{u})) : ConnectedSpace Y := by
  let := h
  let := fieldSpec_surjective b
  exact (Limits.pullback.fst q b).surjective.connectedSpace (Limits.pullback.fst q b).continuous

end AlgebraicGeometry.Scheme.Geometrically
