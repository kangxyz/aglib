/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Support
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Property
public import Aglib.AlgebraicGeometry.Modules.Exact
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeProperty
public import Aglib.CategoryTheory.SmallModel.Abelian

/-!
# Finite height slices of coherent support

Source-only extraction from `R5Lab.KTheory.Quillen.CoherentFiniteSupport` at R5Lab revision
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`. Existing objects, maps,
hypotheses, universes, proof bodies and mathematical namespaces are retained.
The original source correspondence remains in the supplying application module.
-/



/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.Support.HeightSlice` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`df23d9f177066e6f3eca3f437af0bf5d1ffbe066ed16c94348305246b6bdc65c`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
open AlgebraicGeometry TopologicalSpace CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules.Coherent.Support
universe u

/-- The height-p slice of a closed set supported in height at least p is finite.
The proof uses finite irreducible decomposition and the actual coheight order. -/
theorem finite_closed_height_slice (X : Scheme.{u}) [IsNoetherian X]
    (Z : Set X) (hZ : IsClosed Z) (p : ℕ)
    (hlower : ∀ x ∈ Z, (p : ℕ∞) ≤ Order.coheight x) :
    {x : X | x ∈ Z ∧ Order.coheight x = p}.Finite := by
  classical
  obtain ⟨S, hS, hSc, hSi, hSZ⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  let g : S → X := fun s => (hSi s.1 s.2).genericPoint
  let : Finite S := hS.to_subtype
  apply (Set.finite_range g).subset
  rintro x ⟨hx, hxp⟩
  obtain ⟨s, hs, hxs⟩ := Set.mem_sUnion.mp (hSZ ▸ hx)
  let t : S := ⟨s, hs⟩
  have hg : IsGenericPoint (g t) s :=
    (hSi s hs).isGenericPoint_genericPoint (hSc s hs)
  have hgs : g t ∈ Z := by
    rw [hSZ]
    exact Set.mem_sUnion.mpr ⟨s, hs, hg.mem⟩
  have hxg : x ≤ g t := hg.specializes hxs
  have heq : g t = x := by
    by_contra hn
    have hlt : x < g t := lt_iff_le_not_ge.mpr
      ⟨hxg, fun h => hn (Specializes.antisymm hxg h).eq⟩
    have hgfin : Order.coheight (g t) < ⊤ :=
      lt_of_le_of_lt (Order.coheight_anti hxg) (by rw [hxp]; exact WithTop.coe_lt_top p)
    have hbad := Order.coheight_strictAnti hlt hgfin
    exact (not_lt_of_ge (hlower (g t) hgs)) (hxp ▸ hbad)
  exact ⟨t, heq⟩

/-- Actual coherent support has finitely many height-p stalks once it vanishes
below p. Neither integrality nor regularity is used by this lemma. -/
theorem coherent_finite_height_support (X : Scheme.{u}) [IsNoetherian X]
    (M : _root_.AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteTypeSheaves X) (p : ℕ)
    (hlower : ∀ x, ringKrullDim (X.presheaf.stalk x) < p →
      IsZero ((_root_.AlgebraicGeometry.Scheme.Modules.stalkFunctor X x).obj M.obj)) :
    {x : X | ringKrullDim (X.presheaf.stalk x) = p ∧
      ¬ IsZero ((_root_.AlgebraicGeometry.Scheme.Modules.stalkFunctor X x).obj M.obj)}.Finite := by
  have hf := finite_closed_height_slice X (_root_.AlgebraicGeometry.Scheme.Modules.support M.obj)
    (_root_.AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteType_support_isClosed M) p ?_
  · apply hf.subset
    rintro x ⟨hdim, hnonzero⟩
    refine ⟨hnonzero, ?_⟩
    rw [ringKrullDim_stalk_eq_coheight] at hdim
    exact WithBot.coe_injective hdim
  · intro x hx
    by_contra hn
    apply hx
    apply hlower x
    rw [ringKrullDim_stalk_eq_coheight]
    exact WithBot.coe_lt_coe.mpr (lt_of_not_ge hn)

end AlgebraicGeometry.Scheme.Modules.Coherent.Support
