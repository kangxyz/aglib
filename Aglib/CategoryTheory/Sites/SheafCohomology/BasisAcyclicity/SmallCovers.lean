/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.Covers

/-! # Small covers in a larger coefficient universe

Only the index type is enlarged: every selected family still has a small
indexing type up to the specified equivalence. This allows arbitrary small open
covers, not merely finite covers, with larger-valued coefficients.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.BasisAcyclicity

universe c h w t

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [∀ W : C, HasFiniteProducts (Over W)]

omit [∀ W : C, HasFiniteProducts (Over W)] in
private lemma sieveOfArrows_reindex {W : C} {ι : Type w} {κ : Type t}
    (U : ι → Over W) (e : κ ≃ ι) :
    Sieve.ofArrows (fun k => (U (e k)).left) (fun k => (U (e k)).hom) =
      Sieve.ofArrows (fun i => (U i).left) (fun i => (U i).hom) := by
  ext V f
  simp only [Sieve.mem_ofArrows_iff]
  constructor
  · rintro ⟨k, a, ha⟩
    exact ⟨e k, a, ha⟩
  · rintro ⟨i, a, ha⟩
    refine ⟨e.symm i, ?_⟩
    rw [e.apply_symm_apply]
    exact ⟨a, ha⟩

/-- Enlarge the index universe without introducing any genuinely larger covers.
The original small indexing type and equivalence remain part of selection. -/
def CoverBasis.raise (B : CoverBasis.{c, h, w} J) : CoverBasis.{c, h, max w t} J where
  objects := B.objects
  selected W κ U := ∃ (ι : Type w) (V : ι → Over W) (e : κ ≃ ι),
    B.selected W ι V ∧ U = V ∘ e
  covering := by
    rintro W κ U ⟨ι, V, e, hV, rfl⟩
    simpa only [Function.comp_apply, sieveOfArrows_reindex] using B.covering hV
  cofinal W hW R hR := by
    obtain ⟨ι, U, hU, hRU⟩ := B.cofinal W hW R hR
    refine ⟨ULift.{t} ι, fun i => U i.down, ⟨ι, U, Equiv.ulift, hU, rfl⟩, ?_⟩
    intro i
    exact hRU i.down
  intersections := by
    rintro W κ U ⟨ι, V, e, hV, rfl⟩ n a
    exact B.intersections hV n (fun i => e (a i))

/-- Every selected enlarged cover has an original small indexing type. -/
theorem CoverBasis.raise_selected_small (B : CoverBasis.{c, h, w} J)
    {W : C} {κ : Type (max w t)} {U : κ → Over W}
    (hU : B.raise.selected W κ U) : Small.{w} κ := by
  obtain ⟨ι, V, e, hV, hU⟩ := hU
  exact small_of_injective e.injective

end CategoryTheory.Sheaf.BasisAcyclicity
