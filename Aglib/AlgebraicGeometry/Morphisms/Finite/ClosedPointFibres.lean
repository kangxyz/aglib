/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Finite morphisms from finite fibres through closed points

Let `f : X ⟶ Y` be a morphism locally of finite type whose source is a Jacobson space (for
instance `X` locally of finite type over a field). If the fibre `f⁻¹(f x)` is finite for every
closed point `x` of `X`, then `f` is locally quasi-finite
(`LocallyQuasiFinite.of_finite_preimage_singleton_of_isClosed_of_jacobsonSpace`), and finite if
moreover `f` is proper
(`IsFinite.of_isProper_of_finite_preimage_singleton_of_isClosed_of_jacobsonSpace`).

The proof uses that the set of points where `f` is quasi-finite is open (Mathlib's
`Scheme.Hom.quasiFiniteLocus`, from Zariski's main theorem). A point with a finite fibre is in it
(Mathlib's `Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber`, the fibre being a finite
Jacobson scheme), and a nonempty closed subset of a Jacobson space has a closed point. The
finiteness of `f` from properness is Mathlib's `IsFinite.of_isProper_of_locallyQuasiFinite`.

`JacobsonSpace.finite_of_isClosed_of_finite_inter_closedPoints` records the topological input
used to check the hypothesis: a closed subset of a Jacobson space with finitely many closed points
is finite.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

/-- **A closed subset of a Jacobson space with finitely many closed points is finite**: it is the
closure of its closed points, a finite union of closed points. -/
theorem JacobsonSpace.finite_of_isClosed_of_finite_inter_closedPoints {X : Type*}
    [TopologicalSpace X] [JacobsonSpace X] {Z : Set X} (hZ : IsClosed Z)
    (h : (Z ∩ closedPoints X).Finite) : Z.Finite := by
  have hc : IsClosed (Z ∩ closedPoints X) := by
    rw [← Set.biUnion_of_singleton (Z ∩ closedPoints X)]
    exact h.isClosed_biUnion fun z hz => hz.2
  rw [← closure_inter_closedPoints hZ, hc.closure_eq]
  exact h

namespace AlgebraicGeometry

/-- **Local quasi-finiteness from the fibres through closed points.** A morphism locally of finite
type from a Jacobson scheme whose fibres through closed points are finite is locally
quasi-finite. -/
theorem LocallyQuasiFinite.of_finite_preimage_singleton_of_isClosed_of_jacobsonSpace
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [JacobsonSpace X]
    (hf : ∀ x : X, IsClosed {x} → (f ⁻¹' {f x}).Finite) : LocallyQuasiFinite f := by
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
  by_contra h
  have hne : ((f.quasiFiniteLocus : Set X)ᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    exact fun h' => h (Opens.coe_eq_univ.mp h')
  obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints hne
    f.quasiFiniteLocus.isOpen.isClosed_compl.isLocallyClosed
  apply hx
  have : Finite (f.fiber (f x)) := (f.fiberHomeo (f x)).finite_iff.mpr (hf x hxc)
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)

/-- **Finiteness from the fibres through closed points.** A proper morphism from a Jacobson scheme
whose fibres through closed points are finite is finite. -/
theorem IsFinite.of_isProper_of_finite_preimage_singleton_of_isClosed_of_jacobsonSpace
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [JacobsonSpace X]
    (hf : ∀ x : X, IsClosed {x} → (f ⁻¹' {f x}).Finite) : IsFinite f := by
  have : LocallyQuasiFinite f := .of_finite_preimage_singleton_of_isClosed_of_jacobsonSpace f hf
  exact .of_isProper_of_locallyQuasiFinite f

end AlgebraicGeometry
