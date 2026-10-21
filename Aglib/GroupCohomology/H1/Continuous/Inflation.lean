/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupCohomology.H1.Continuous
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Continuous cocycle descent through quotient homomorphisms

A continuous cocycle descends along a continuous group homomorphism that is a quotient map when
the coefficient actions agree and the cocycle vanishes on its kernel. The compact-to-Hausdorff
version derives the quotient-map hypothesis from surjectivity. No descent through a bare
surjection is asserted.

Extraction source: `R5Lab.Aglib.GroupCohomology.H1.Inflation`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`521fcfca30111a38af356687ede479e369593bd6c91315ff6a408f83de63db89`.
The source conditions, actual objects and canonical maps are retained under native names.
-/

@[expose] public section

noncomputable section
open _root_.GroupCohomology.ContinuousH1
namespace GroupCohomology.ContinuousH1
namespace Inflation
variable {G H A : Type*} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [DistribMulAction H A]

/-- A continuous cocycle vanishing on the kernel descends through a quotient
homomorphism. The two given coefficient actions must agree along `p`. -/
theorem exists_descended_cocycle (p : ContinuousMonoidHom G H)
    (hp : Topology.IsQuotientMap p)
    (ha : ∀ (g : G) (a : A), g • a = p g • a)
    (c : Cocycle G A) (hc : ∀ g : G, p g = 1 → c.val g = 0) :
    ∃ d : Cocycle H A, ∀ g : G, d.val (p g) = c.val g := by
  classical
  have hsame : ∀ g h : G, p g = p h → c.val g = c.val h := by
    intro g h hgh
    have hk : p (g⁻¹ * h) = 1 := by simp [hgh]
    have h := c.map_mul g (g⁻¹ * h)
    rw [hc _ hk, smul_zero, add_zero, mul_inv_cancel_left] at h
    exact h.symm
  let s : H → G := fun h => (hp.surjective h).choose
  have hs : ∀ h : H, p (s h) = h := fun h => (hp.surjective h).choose_spec
  let d : H → A := fun h => c.val (s h)
  have hd : ∀ g : G, d (p g) = c.val g := fun g => hsame _ _ (hs (p g))
  have hcont : Continuous d := hp.continuous_iff.mpr (by
    have he : d ∘ p = c.val := funext hd
    rw [he]
    exact c.continuous)
  refine ⟨⟨⟨d, hcont⟩, ?_⟩, hd⟩
  intro h k
  change c.val (s (h * k)) = c.val (s h) + h • c.val (s k)
  calc
    c.val (s (h * k)) = c.val (s h * s k) := hsame _ _ (by simp [hs])
    _ = c.val (s h) + s h • c.val (s k) := c.map_mul _ _
    _ = c.val (s h) + h • c.val (s k) := by rw [ha, hs]

/-- Compact-to-Hausdorff continuous surjectivity supplies the needed quotient topology. -/
theorem exists_descended_cocycle_of_compact [CompactSpace G] [T2Space H]
    (p : ContinuousMonoidHom G H) (hp : Function.Surjective p)
    (ha : ∀ (g : G) (a : A), g • a = p g • a)
    (c : Cocycle G A) (hc : ∀ g : G, p g = 1 → c.val g = 0) :
    ∃ d : Cocycle H A, ∀ g : G, d.val (p g) = c.val g :=
  exists_descended_cocycle p
    (Topology.IsQuotientMap.of_surjective_continuous hp p.continuous) ha c hc

end Inflation
end GroupCohomology.ContinuousH1
