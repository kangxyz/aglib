/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Connected.Clopen

/-!
# Normal stalks and connected normal schemes

General declarations from `R5Lab.AlgebraicGeometry.Curves.Core` at revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`.
`NormalComponentsOpen` is retained as an all-scheme theorem-family predicate;
its proved supplier is in `Aglib.AlgebraicGeometry.Properties.Normal.Components`.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

/-- Normality defined on the actual local rings, including the domain condition. -/
def NormalStalks (X : Scheme.{u}) : Prop :=
  ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)

/-- General normal-scheme component theorem, Stacks 0357 (28.7.5), specialized
to locally Noetherian schemes as in 033N (28.7.7). Inspected 2026-10-09.
The 2018 correction removes an unjustified global finiteness claim; no such
claim occurs here. This predicate records the general theorem interface;
`normalComponentsOpen` in
`Aglib.AlgebraicGeometry.Properties.Normal.Components` supplies its proved term. -/
def NormalComponentsOpen : Prop :=
  ∀ (X : Scheme.{u}), IsLocallyNoetherian X → NormalStalks X →
    ∀ Z ∈ irreducibleComponents X, IsOpen Z

/-- Local domains imply reducedness of the actual structure sheaf. -/
theorem NormalStalks.isReduced {X : Scheme.{u}} (h : NormalStalks X) : IsReduced X := by
  let (x : X) : IsDomain (X.presheaf.stalk x) := (h x).1
  exact isReduced_of_isReduced_stalk X

/-- Connectedness turns an open-and-closed irreducible component into the
whole scheme; reducedness is independently obtained from the actual stalks. -/
theorem isIntegral_of_connected_normalStalks (hcomp : NormalComponentsOpen.{u})
    (X : Scheme.{u}) [IsLocallyNoetherian X] [ConnectedSpace X]
    (h : NormalStalks X) : IsIntegral X := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have hclopen : IsClopen (irreducibleComponent x) :=
    ⟨isClosed_irreducibleComponent,
      hcomp X inferInstance h _ (irreducibleComponent_mem_irreducibleComponents x)⟩
  have heq := hclopen.eq_univ ⟨x, mem_irreducibleComponent⟩
  have hi : IsIrreducible (Set.univ : Set X) := by
    rw [← heq]
    exact isIrreducible_irreducibleComponent
  let : IrreducibleSpace X := { isPreirreducible_univ := hi.2, toNonempty := ⟨x⟩ }
  let : IsReduced X := h.isReduced
  exact isIntegral_of_irreducibleSpace_of_isReduced X

end AlgebraicGeometry.Scheme
