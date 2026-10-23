/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Descent of the covering condition along affine-transition limits

An etale family defined at a stage which covers after pullback to the limit
already covers after pullback to a later stage. The family, its actual scheme
pullbacks and their original projections are retained. The index of the
covering family need not be finite; compactness is required of the stages.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u v

/-- The covering relation for the literal pullback of an etale family descends
along a cofiltered limit of quasi-compact schemes with affine transitions. -/
theorem exists_jointlySurjective_pullback_family
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, CompactSpace (D.obj i)]
    [∀ {i j} (q : i ⟶ j), IsAffineHom (D.map q)]
    {i : I} {κ : Type v} (V : κ → Scheme.{u}) (f : ∀ k, V k ⟶ D.obj i)
    [∀ k, Etale (f k)]
    (hcover : ∀ x : c.pt, ∃ k, ∃ y : (pullback (c.π.app i) (f k) : Scheme),
      pullback.fst (c.π.app i) (f k) y = x) :
    ∃ (j : I) (q : j ⟶ i), ∀ x : D.obj j,
      ∃ k, ∃ y : (pullback (D.map q) (f k) : Scheme),
        pullback.fst (D.map q) (f k) y = x := by
  let U : (D.obj i).Opens :=
    ⟨⋃ k, Set.range (f k), isOpen_iUnion fun k ↦ (f k).isOpenMap.isOpen_range⟩
  have hU : c.π.app i ⁻¹ᵁ U = ⊤ := by
    apply le_antisymm le_top
    intro x _
    obtain ⟨k, y, hy⟩ := hcover x
    change c.π.app i x ∈ ⋃ k, Set.range (f k)
    apply Set.mem_iUnion.mpr
    refine ⟨k, ?_⟩
    have h : x ∈ Set.range (pullback.fst (c.π.app i) (f k)) := ⟨y, hy⟩
    rw [Scheme.Pullback.range_fst] at h
    exact h
  obtain ⟨j, q, hq⟩ := AlgebraicGeometry.exists_map_eq_top D c hc U hU
  refine ⟨j, q, fun x ↦ ?_⟩
  have hx : x ∈ D.map q ⁻¹ᵁ U := hq.ge (Set.mem_univ x)
  change D.map q x ∈ ⋃ k, Set.range (f k) at hx
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
  refine ⟨k, ?_⟩
  have h : x ∈ Set.range (pullback.fst (D.map q) (f k)) := by
    rw [Scheme.Pullback.range_fst]
    exact hk
  exact h

end AlgebraicGeometry.Scheme.EtaleAffineBasis
