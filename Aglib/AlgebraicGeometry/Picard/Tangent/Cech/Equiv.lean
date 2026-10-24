/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Tangent.Cech.Frames

/-!
# The kernel of `i^*` on Picard groups is pair cohomology

Let `i : X ⟶ Y`, `p : Y ⟶ X` with `i ≫ p = 𝟙 X` and an `IdealGenerator` (for example the dual
numbers `X[ε]`), and let `U : ι → X.Opens` cover `X` by affine opens whose preimages `p⁻¹ U j`
and pairwise intersections `U j ⊓ U l` are affine. Then
`IdealGenerator.pairCohomologyEquivKer : PairCohomology U ≃+ ker(i^* : Pic Y → Pic X)` sends the
class of a pair cocycle `b` to the class of the line bundle glued from `1 + ε b`
(`pairCohomologyEquivKer_mk`).

The kernel of `IdealGenerator.cocycleClass` is the group of pair coboundaries
(`ker_cocycleClass`) and its range is the kernel of `i^*` (`range_cocycleClass`); the
equivalence is the first isomorphism theorem (compare Kleiman, arXiv:math/0504020v1, proof of
Thm 5.11, p. 43, and Stacks, Tag 0B8R, for a fixed cover).
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local

universe u

namespace AlgebraicGeometry.Scheme.SplitThickening.IdealGenerator

variable {X Y : Scheme.{u}} {i : X ⟶ Y} {p : Y ⟶ X} {h : i ≫ p = 𝟙 X}
  (G : IdealGenerator i p h) {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)
  (hU₁ : ∀ j, IsAffineOpen (U j))

include hU₁ in
/-- The kernel of the class map is the group of pair coboundaries. -/
theorem ker_cocycleClass : (G.cocycleClass U hU).ker = pairCoboundaries U :=
  AddSubgroup.ext fun b => AddMonoidHom.mem_ker.trans (G.cocycleClass_eq_zero_iff U hU hU₁ b)

variable (hV₁ : ∀ j, IsAffineOpen (p ⁻¹ᵁ U j)) (hU₂ : ∀ j l, IsAffineOpen (U j ⊓ U l))

include hU₁ hV₁ hU₂ in
/-- The range of the class map is the kernel of `i^*`. -/
theorem range_cocycleClass : (G.cocycleClass U hU).range = (pullbackHom i).ker := by
  ext c
  rw [AddMonoidHom.mem_range, AddMonoidHom.mem_ker]
  constructor
  · rintro ⟨b, rfl⟩
    exact G.pullbackHom_cocycleClass U hU b
  · exact G.exists_cocycleClass_eq U hU₁ hV₁ hU hU₂ c

/-- Pair cohomology is the kernel of `i^* : Pic Y → Pic X`: the class of a pair cocycle `b`
goes to the class of the line bundle glued from `1 + ε b`. -/
def pairCohomologyEquivKer : PairCohomology U ≃+ (pullbackHom i).ker :=
  (QuotientAddGroup.quotientAddEquivOfEq (G.ker_cocycleClass U hU hU₁).symm).trans
    ((QuotientAddGroup.quotientKerEquivRange (G.cocycleClass U hU)).trans
      (AddEquiv.addSubgroupCongr (G.range_cocycleClass U hU hU₁ hV₁ hU₂)))

theorem pairCohomologyEquivKer_mk (b : pairCocycles U) :
    (G.pairCohomologyEquivKer U hU hU₁ hV₁ hU₂ (QuotientAddGroup.mk b) : PicardGroup Y) =
      G.cocycleClass U hU b :=
  rfl

end AlgebraicGeometry.Scheme.SplitThickening.IdealGenerator
