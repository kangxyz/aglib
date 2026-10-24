/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Scheme.Separated

/-!
# Consumer checks for the separatedness of the Picard scheme

The pieces `Pic^{φ,ψ}_m` are separated, cover the Picard scheme, increase with `m` and are disjoint
for distinct `(φ, ψ)`, so the Picard scheme is separated over `Spec A` (Kleiman, *The Picard
scheme*, arXiv:math/0504020v1, Thm 4.8 (1) and its proof, p. 28), with axiom guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.RelativePicard.Strata

universe u

namespace AglibTest.PicardSchemeSeparated

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace A ι} [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  [GeometricallyIntegral (i ≫ toSpec A ι)] {N : ℕ} {e : ι ≃ Fin (N + 1)}
  (h : FineStrataRepresentableByHQuasiProjective i N e)

/-- The Picard scheme is separated over `Spec A`. -/
example : IsSeparated (picardScheme h).obj.hom :=
  inferInstance

/-- The pieces `Pic^{φ,ψ}_m` of the separatedness argument. -/
example (φ ψ : Polynomial ℚ) (m : ℤ) :
    IsSeparated ((picardBaseLevelOpens h φ ψ m).ι ≫ (picardScheme h).obj.hom) ∧
      Monotone (picardBaseLevelOpens h φ ψ) ∧
      ⨆ x : Polynomial ℚ × Polynomial ℚ, ⨆ m', picardBaseLevelOpens h x.1 x.2 m' = ⊤ :=
  ⟨isSeparated_picardBaseLevelOpens h φ ψ m, monotone_picardBaseLevelOpens h φ ψ,
    iSup_picardBaseLevelOpens h⟩

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isSeparated_picardScheme' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isSeparated_picardScheme

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isSeparated_picardBaseLevelOpens' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isSeparated_picardBaseLevelOpens

end AglibTest.PicardSchemeSeparated
