/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.RingTheory.FiniteType

/-!
# Noetherianity of the actual Laurent ring

Supporting auxiliary for `K2-018#prop:k2018-arithmetic-characters`
(`research/exposes/K2/018/expose.tex`), source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.

A finitely generated commutative monoid gives a finite-type monoid algebra; a Noetherian
coefficient ring therefore gives a Noetherian monoid algebra.

This module supplies the stated local algebraic construction; it does not
claim a full original face-cycle or motivic comparison theorem.

## Extraction basis

Transferred from `R5Lab.RingTheory.LocalLength.MonoidAlgebraNoetherian` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`eaea516e1a9e5acf1e1a6851d0011f13a8cdd85f2ea2a3a9590b6b84a4964863`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MonoidAlgebra
universe u v

/-- A commutative monoid algebra with a finitely generated monoid is a
finite-type algebra, with the actual monoid generators giving algebra generators. -/
theorem monoidAlgebra_finiteType (A : Type u) [CommRing A]
    (G : Type v) [CommMonoid G] [Monoid.FG G] : Algebra.FiniteType A (MonoidAlgebra A G) := by
  classical
  obtain ⟨s, hs⟩ := Monoid.FG.fg_top (M := G)
  let generators : Finset (MonoidAlgebra A G) := s.image (MonoidAlgebra.of A G)
  let B := Algebra.adjoin A (generators : Set (MonoidAlgebra A G))
  have hmon : ∀ g : G, MonoidAlgebra.of A G g ∈ B := by
    have hpre : (⊤ : Submonoid G) ≤
        B.toSubsemiring.toSubmonoid.comap (MonoidAlgebra.of A G) := by
      rw [← hs]
      apply Submonoid.closure_le.mpr
      intro g hg
      exact Algebra.subset_adjoin (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
    intro g
    exact hpre (Submonoid.mem_top g)
  refine ⟨generators, top_unique ?_⟩
  intro x _
  exact MonoidAlgebra.induction_on x hmon
    (fun x y hx hy => B.add_mem hx hy) (fun a x hx => B.smul_mem hx a)

theorem monoidAlgebra_isNoetherianRing (A : Type u) [CommRing A] [IsNoetherianRing A]
    (G : Type v) [CommMonoid G] [Monoid.FG G] : IsNoetherianRing (MonoidAlgebra A G) := by
  let := monoidAlgebra_finiteType A G
  exact Algebra.FiniteType.isNoetherianRing A (MonoidAlgebra A G)

end MonoidAlgebra
