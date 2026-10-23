/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.Covers

/-! # The cofinal basis of all small covering families

The family of all arrows in a covering sieve is small in the combined site
universe and refines that sieve literally. This is suitable for non-quasi-compact
spaces; no finite-cover assertion is made.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Sheaf.BasisAcyclicity

universe c h

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  [∀ W : C, HasFiniteProducts (Over W)]

/-- Every site with finite products in slices has a cofinal supply of
`max(c,h)`-small covering families on all its objects. -/
def CoverBasis.all : CoverBasis.{c, h, max c h} J where
  objects _ := True
  selected W ι U := Sieve.ofArrows (fun i => (U i).left) (fun i => (U i).hom) ∈ J W
  covering h := h
  cofinal W _ R hR := by
    let ι := Σ V : C, {f : V ⟶ W // R f}
    let U : ι → Over W := fun i => Over.mk i.2.1
    have he : Sieve.ofArrows (fun i => (U i).left) (fun i => (U i).hom) = R := by
      ext V f
      rw [Sieve.mem_ofArrows_iff]
      constructor
      · rintro ⟨i, a, rfl⟩
        exact R.downward_closed i.2.2 a
      · intro hf
        exact ⟨⟨V, f, hf⟩, 𝟙 V, (Category.id_comp f).symm⟩
    exact ⟨ι, U, he.symm ▸ hR, fun i => i.2.2⟩
  intersections _ _ _ := trivial

end CategoryTheory.Sheaf.BasisAcyclicity
