/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Dimension.QuasiFiniteSurjective
public import Aglib.AlgebraicGeometry.Group.IdentityComponent.Irreducible
public import Aglib.AlgebraicGeometry.Morphisms.Finite.ClosedPointFibres

/-! # Multiplication by `n` on a proper connected group scheme with finite `k`-point fibres

Let `k` be an algebraically closed field, `G` a group scheme over `k` (`G : Over (Spec k)` with a
group object structure) which is proper over `k` with connected underlying space, and `n` a
natural number. Write `[n] = (𝟙 G) ^ n : G ⟶ G` for the multiplication by `n`, so that
`p ≫ [n] = p ^ n` on `k`-points `p`. Assume that for every `k`-point `y` of `G` the set of
`k`-points `p` with `p ^ n = y` is finite. Then:

* `multiplication_isFinite_of_finite_setOf_pow_eq_of_isAlgClosed`: `[n]` is finite;
* `multiplication_surjective_of_finite_setOf_pow_eq_of_isAlgClosed`: `[n]` is surjective;
* `exists_pow_eq_of_finite_setOf_pow_eq_of_isAlgClosed`: every `k`-point of `G` is an `n`-th
  power, that is, the group `G(k)` is `n`-divisible.

For an abelian variety `A` these are Stacks, Groupoid Schemes, Proposition 9.11 (3) and (4),
Tag 03RP, and the finiteness of `[d]` in the proof of Lemma 9.8, Tag 0BFG (fibres of dimension
zero). Here the finiteness of the `k`-point fibres is the hypothesis, and the proof uses neither
an ample line bundle nor smoothness:

1. `[n]` is proper (`G` is proper over `k`). A fibre of `[n]` through a closed point is closed,
   and its closed points are `k`-points `p` with `p ^ n` fixed (Mathlib's
   `pointEquivClosedPoint`), hence finitely many; `G` is Jacobson, so the fibre is finite
   (`JacobsonSpace.finite_of_isClosed_of_finite_inter_closedPoints`). Hence `[n]` is finite
   (`IsFinite.of_isProper_of_finite_preimage_singleton_of_isClosed_of_jacobsonSpace`).
2. `G` is irreducible (`irreducibleSpace_of_connectedSpace_of_isAlgClosed`, Stacks 0B7Q for
   algebraically closed `k`) and locally Noetherian, and `[n]` fixes the unit point; a finite
   endomorphism fixing a point of an irreducible locally Noetherian scheme is surjective
   (`Scheme.Hom.surjective_of_locallyQuasiFinite_of_isClosed_range_of_apply_eq`).
3. A nonempty closed fibre of `[n]` over a `k`-point contains a closed point, which is a `k`-point
   (Mathlib's `pointOfClosedPoint`); two `k`-points with the same value are equal.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.Group.Multiplication

variable {k : Type u} [Field k] (G : Over (Spec (.of k)))

section GrpObj

variable [GrpObj G]

/-- On `k`-points, multiplication by `n` is the `n`-th power: `[n](p) = p ^ n`. -/
theorem multiplication_left_apply_point (n : ℕ) (p : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    ((𝟙 G) ^ n).left (p.left (IsLocalRing.closedPoint k)) =
      (p ^ n).left (IsLocalRing.closedPoint k) := by
  have h : p ≫ (𝟙 G) ^ n = p ^ n := by rw [MonObj.comp_pow, Category.comp_id]
  exact congrArg (fun φ : 𝟙_ (Over (Spec (.of k))) ⟶ G => φ.left (IsLocalRing.closedPoint k)) h

/-- Multiplication by `n` fixes the unit point. -/
theorem multiplication_left_apply_unitPoint (n : ℕ) :
    ((𝟙 G) ^ n).left (unitPoint G) = unitPoint G := by
  have h : η[G] ≫ (𝟙 G) ^ n = η[G] := by
    rw [MonObj.comp_pow, Category.comp_id, MonObj.one_eq_one, one_pow]
  exact congrArg (fun φ : 𝟙_ (Over (Spec (.of k))) ⟶ G => φ.left (IsLocalRing.closedPoint k)) h

/-- Multiplication by `n` on a group scheme proper over `k` is proper. -/
theorem multiplication_isProper [IsProper G.hom] (n : ℕ) : IsProper ((𝟙 G) ^ n).left := by
  have : IsProper (((𝟙 G) ^ n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  exact IsProper.of_comp _ G.hom

end GrpObj

variable [IsAlgClosed k]

section LocallyOfFiniteType

variable [LocallyOfFiniteType G.hom]

/-- Over an algebraically closed field, two `k`-points of a scheme locally of finite type over
`k` with the same value are equal (Mathlib's `ext_of_apply_closedPoint_eq`). -/
private theorem point_ext_of_isAlgClosed {p q : 𝟙_ (Over (Spec (.of k))) ⟶ G}
    (h : p.left (IsLocalRing.closedPoint k) = q.left (IsLocalRing.closedPoint k)) : p = q :=
  Over.OverMorphism.ext (ext_of_apply_closedPoint_eq G.hom (Over.w p) (Over.w q) h)

/-- The value of a `k`-point of a scheme locally of finite type over an algebraically closed
field is a closed point (Mathlib's `pointEquivClosedPoint`). -/
private theorem isClosed_singleton_point_left_apply_of_isAlgClosed
    (p : 𝟙_ (Over (Spec (.of k))) ⟶ G) : IsClosed {p.left (IsLocalRing.closedPoint k)} :=
  (pointEquivClosedPoint G.hom ⟨p.left, Over.w p⟩).2

/-- **The fibres of multiplication by `n` through closed points are finite** on a group scheme
locally of finite type over an algebraically closed field whose `k`-point fibres
`{p | p ^ n = y}` are finite. -/
theorem multiplication_finite_preimage_singleton_of_isClosed_of_finite_setOf_pow_eq_of_isAlgClosed
    [GrpObj G] (n : ℕ) (hfin : ∀ y : 𝟙_ (Over (Spec (.of k))) ⟶ G, {p | p ^ n = y}.Finite)
    (x : G.left) (hx : IsClosed {x}) :
    (((𝟙 G) ^ n).left ⁻¹' {((𝟙 G) ^ n).left x}).Finite := by
  have : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  obtain ⟨px, rfl⟩ := exists_point_left_apply_eq_of_isClosed_of_isAlgClosed G hx
  rw [multiplication_left_apply_point G n px]
  refine JacobsonSpace.finite_of_isClosed_of_finite_inter_closedPoints
    ((isClosed_singleton_point_left_apply_of_isAlgClosed G (px ^ n)).preimage
      ((𝟙 G) ^ n).left.continuous) ?_
  refine ((hfin (px ^ n)).image fun p => p.left (IsLocalRing.closedPoint k)).subset ?_
  rintro z ⟨hz, hzc⟩
  obtain ⟨pz, rfl⟩ := exists_point_left_apply_eq_of_isClosed_of_isAlgClosed G hzc
  have hz' : ((𝟙 G) ^ n).left (pz.left (IsLocalRing.closedPoint k)) =
      (px ^ n).left (IsLocalRing.closedPoint k) := hz
  exact ⟨pz, point_ext_of_isAlgClosed G ((multiplication_left_apply_point G n pz).symm.trans hz'),
    rfl⟩

end LocallyOfFiniteType

variable [GrpObj G] [IsProper G.hom]

/-- **Multiplication by `n` is finite** on a group scheme proper over an algebraically closed field
whose `k`-point fibres `{p | p ^ n = y}` are finite (for an abelian variety, the finiteness of
`[d]` is shown in the proof of Stacks, Groupoid Schemes, Lemma 9.8, Tag 0BFG). -/
theorem multiplication_isFinite_of_finite_setOf_pow_eq_of_isAlgClosed (n : ℕ)
    (hfin : ∀ y : 𝟙_ (Over (Spec (.of k))) ⟶ G, {p | p ^ n = y}.Finite) :
    IsFinite ((𝟙 G) ^ n).left := by
  have : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  have := multiplication_isProper G n
  exact IsFinite.of_isProper_of_finite_preimage_singleton_of_isClosed_of_jacobsonSpace _
    (multiplication_finite_preimage_singleton_of_isClosed_of_finite_setOf_pow_eq_of_isAlgClosed G n
      hfin)

variable [ConnectedSpace G.left]

/-- **Multiplication by `n` is surjective** on a proper connected group scheme over an
algebraically closed field whose `k`-point fibres `{p | p ^ n = y}` are finite (Stacks, Groupoid
Schemes, Proposition 9.11(3), Tag 03RP, for an abelian variety). -/
theorem multiplication_surjective_of_finite_setOf_pow_eq_of_isAlgClosed (n : ℕ)
    (hfin : ∀ y : 𝟙_ (Over (Spec (.of k))) ⟶ G, {p | p ^ n = y}.Finite) :
    Surjective ((𝟙 G) ^ n).left := by
  have := multiplication_isFinite_of_finite_setOf_pow_eq_of_isAlgClosed G n hfin
  have : IrreducibleSpace G.left := irreducibleSpace_of_connectedSpace_of_isAlgClosed G
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  exact Scheme.Hom.surjective_of_locallyQuasiFinite_of_isClosed_range_of_apply_eq _
    ((𝟙 G) ^ n).left.isClosedMap.isClosed_range (multiplication_left_apply_unitPoint G n)

/-- **The `k`-points form an `n`-divisible group**: on a proper connected group scheme over an
algebraically closed field whose `k`-point fibres `{p | p ^ n = y}` are finite, every `k`-point
is an `n`-th power (Stacks, Groupoid Schemes, Proposition 9.11(4), Tag 03RP, for an abelian
variety). -/
theorem exists_pow_eq_of_finite_setOf_pow_eq_of_isAlgClosed (n : ℕ)
    (hfin : ∀ y : 𝟙_ (Over (Spec (.of k))) ⟶ G, {p | p ^ n = y}.Finite)
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ G) : ∃ p, p ^ n = y := by
  have : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  have hsurj := (multiplication_surjective_of_finite_setOf_pow_eq_of_isAlgClosed G n hfin).surj
  have hZ : IsClosed (((𝟙 G) ^ n).left ⁻¹' {y.left (IsLocalRing.closedPoint k)}) :=
    (isClosed_singleton_point_left_apply_of_isAlgClosed G y).preimage
      ((𝟙 G) ^ n).left.continuous
  obtain ⟨x, hx⟩ := hsurj (y.left (IsLocalRing.closedPoint k))
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints (Z := ((𝟙 G) ^ n).left ⁻¹'
    {y.left (IsLocalRing.closedPoint k)}) ⟨x, hx⟩ hZ.isLocallyClosed
  obtain ⟨p, rfl⟩ := exists_point_left_apply_eq_of_isClosed_of_isAlgClosed G hzc
  have hz' : ((𝟙 G) ^ n).left (p.left (IsLocalRing.closedPoint k)) =
      y.left (IsLocalRing.closedPoint k) := hz
  exact ⟨p, point_ext_of_isAlgClosed G ((multiplication_left_apply_point G n p).symm.trans hz')⟩

end AlgebraicGeometry.Scheme.Group.Multiplication
