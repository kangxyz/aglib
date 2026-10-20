/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The quotient grading of a homogeneous ideal

Source: ordinary R5 Weierstrass.Projective, lines 102–177.
The grading is the actual image of each original homogeneous component.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open DirectSum
namespace GradedAlgebra.Quotient
universe u
variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
variable (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜] (I : Ideal A)

/-- The image of the degree-`n` submodule in the quotient ring. -/
def grading (n : ℕ) : Submodule k (A ⧸ I) :=
  (𝒜 n).map (Ideal.Quotient.mkₐ k I).toLinearMap

/-- The additive quotient map on a single homogeneous component. -/
def gradeMap (n : ℕ) : 𝒜 n →+ grading 𝒜 I n where
  toFun x := ⟨Ideal.Quotient.mk I x, Submodule.mem_map.mpr ⟨x, x.property, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add (Ideal.Quotient.mk I) (x : A) (y : A))

instance gradedMonoid : SetLike.GradedMonoid (grading 𝒜 I) where
  one_mem := Submodule.mem_map.mpr ⟨1, SetLike.one_mem_graded 𝒜, map_one (Ideal.Quotient.mkₐ k I)⟩
  mul_mem := by
    intro i j a b ha hb
    obtain ⟨a0, ha0, rfl⟩ := Submodule.mem_map.mp ha
    obtain ⟨b0, hb0, rfl⟩ := Submodule.mem_map.mp hb
    exact Submodule.mem_map.mpr ⟨a0 * b0, SetLike.mul_mem_graded (A := 𝒜) ha0 hb0,
      map_mul (Ideal.Quotient.mkₐ k I) _ _⟩

/-- Decompose an element into homogeneous components and map each to the quotient. -/
def predecompose : A →+ ⨁ n, grading 𝒜 I n :=
  (DirectSum.map (gradeMap 𝒜 I)).comp (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom

lemma predecompose_zero (hI : I.IsHomogeneous 𝒜) (a : A) (ha : a ∈ I) :
    predecompose 𝒜 I a = 0 := by
  ext n
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hI n ha)

/-- The homogeneous decomposition descended through a homogeneous ideal. -/
def decompose (hI : I.IsHomogeneous 𝒜) : (A ⧸ I) →+ ⨁ n, grading 𝒜 I n :=
  QuotientAddGroup.lift I.toAddSubgroup (predecompose 𝒜 I)
    (predecompose_zero 𝒜 I hI)

lemma decompose_mk (hI : I.IsHomogeneous 𝒜) (a : A) :
    decompose 𝒜 I hI (Ideal.Quotient.mk I a) = predecompose 𝒜 I a := rfl

lemma predecompose_of_mem {n : ℕ} (a : A) (ha : a ∈ 𝒜 n) :
    predecompose 𝒜 I a = DirectSum.of _ n (gradeMap 𝒜 I n ⟨a, ha⟩) := by
  simp [predecompose, DirectSum.decompose_of_mem 𝒜 ha]

/-- The quotient grading associated with a homogeneous ideal. -/
@[instance_reducible]
def gradedAlgebra (hI : I.IsHomogeneous 𝒜) : GradedAlgebra (grading 𝒜 I) where
  decompose' := decompose 𝒜 I hI
  left_inv := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change DirectSum.coeAddMonoidHom _ (predecompose 𝒜 I a) = Ideal.Quotient.mk I a
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous n a => simp [predecompose_of_mem 𝒜 I a a.property, gradeMap]
    | add a b ha hb => simp only [map_add, ha, hb]
  right_inv := by
    have h : (decompose 𝒜 I hI).comp (DirectSum.coeAddMonoidHom _) = AddMonoidHom.id _ := by
      ext n x : 2
      obtain ⟨a, ha, hax⟩ := Submodule.mem_map.mp x.property
      have hx : x = gradeMap 𝒜 I n ⟨a, ha⟩ := Subtype.ext hax.symm
      subst x
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, DirectSum.coeAddMonoidHom_of]
      change predecompose 𝒜 I a = DirectSum.of _ n (gradeMap 𝒜 I n ⟨a, ha⟩)
      exact predecompose_of_mem 𝒜 I a ha
    exact DFunLike.congr_fun h

end GradedAlgebra.Quotient
