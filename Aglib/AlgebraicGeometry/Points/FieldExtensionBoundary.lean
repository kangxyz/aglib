/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Points.Closed
public import Aglib.AlgebraicGeometry.RationalPoint.BaseChange
public import Aglib.AlgebraicGeometry.RationalPoint.SmoothCurve
public import Aglib.AlgebraicGeometry.Limits.Range
public import Aglib.AlgebraicGeometry.Curves.Divisors.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Original closed boundary points under field extension

Over an algebraically closed source field, each actual closed point of a
locally finite-type scheme has its native rational section. Its literal base
change is a closed point and is the entire fibre above the original point,
for any target field. The resulting embedding contains every closed point
outside the base change of a nonempty open of an integral Noetherian curve.
No algebraic closure of the target, finite boundary enumeration, or separate
point model is used. Algebraic closedness of the source is essential here;
separable closedness alone does not give this rational multiplicity-one claim.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.ClosedPoint

variable {k K : Type u} [Field k] [IsAlgClosed k] [Field K]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
  (q : Spec (.of K) ⟶ Spec (.of k))

/-- The native rational section of an actual closed point, with the original
structure map retained. -/
def rationalPoint (x : ClosedPoint X) : RationalPoint k X :=
  ⟨p, pointOfClosedPoint p x.val x.property, pointOfClosedPoint_comp p x.val x.property⟩

/-- The rational section retains the original structure map. -/
@[simp]
theorem rationalPoint_structureMap (x : ClosedPoint X) :
    (rationalPoint p x).structureMap = p := rfl

/-- The rational section has exactly the original closed point. -/
@[simp]
theorem rationalPoint_point (x : ClosedPoint X) :
    (rationalPoint p x).point = x.val :=
  pointOfClosedPoint_apply p x.val x.property _

/-- The actual closed point of the literal field base change above a closed point. -/
def fieldExtensionPoint (x : ClosedPoint X) : ClosedPoint (pullback p q) :=
  ⟨((rationalPoint p x).baseChange q).point,
    ((rationalPoint p x).baseChange q).point_isClosed⟩

/-- The selected point is exactly the native base change of the original
closed-point rational section; no second point choice is made. -/
@[simp]
theorem fieldExtensionPoint_val (x : ClosedPoint X) :
    (fieldExtensionPoint p q x).val = ((rationalPoint p x).baseChange q).point := rfl

/-- The original projection recovers the original closed point. -/
@[simp]
theorem fieldExtensionPoint_fst (x : ClosedPoint X) :
    pullback.fst p q (fieldExtensionPoint p q x).val = x.val := by
  have h := congrArg (fun f : Spec (.of K) ⟶ X => f (IsLocalRing.closedPoint K))
    ((rationalPoint p x).baseChange_sectionMap_fst q)
  exact h.trans (pointOfClosedPoint_apply p x.val x.property _)

/-- The full original point fibre is a singleton, not just its rational points. -/
theorem preimage_singleton_fieldExtensionPoint (x : ClosedPoint X) :
    (pullback.fst p q) ⁻¹' ({x.val} : Set X) =
      {(fieldExtensionPoint p q x).val} := by
  let r := rationalPoint p x
  let s := r.baseChange q
  have hr : Set.range r.sectionMap = ({x.val} : Set X) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact pointOfClosedPoint_apply p x.val x.property z
    · intro hy
      exact ⟨IsLocalRing.closedPoint k,
        (pointOfClosedPoint_apply p x.val x.property _).trans hy.symm⟩
  have hs : Set.range s.sectionMap = ({s.point} : Set (pullback p q : Scheme.{u})) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact congrArg s.sectionMap (Subsingleton.elim z (IsLocalRing.closedPoint K))
    · intro hy
      exact ⟨IsLocalRing.closedPoint K, hy.symm⟩
  exact (congrArg (fun A : Set X => (pullback.fst p q) ⁻¹' A) hr).symm.trans
    ((Scheme.Pullback.Fibre.pullback_range_snd (r.baseChange_isPullback q)).symm.trans hs)

/-- The same actual point construction is an embedding of original closed points. -/
def fieldExtensionEmbedding : ClosedPoint X ↪ ClosedPoint (pullback p q) where
  toFun := fieldExtensionPoint p q
  inj' := by
    intro x y h
    apply Subtype.ext
    have he := congrArg (fun z : ClosedPoint (pullback p q) => pullback.fst p q z.val) h
    exact (fieldExtensionPoint_fst p q x).symm.trans
      (he.trans (fieldExtensionPoint_fst p q y))

/-- Injectivity of the original point function, for native finitely supported maps. -/
theorem fieldExtensionPoint_injective : Function.Injective (fieldExtensionPoint p q) :=
  (fieldExtensionEmbedding p q).injective

/-- A target closed point lies in the embedding precisely when its original
projection is closed. This does not assert that every closed point descends. -/
theorem mem_range_fieldExtensionEmbedding_iff (y : ClosedPoint (pullback p q)) :
    y ∈ Set.range (fieldExtensionEmbedding p q) ↔
      IsClosed ({pullback.fst p q y.val} : Set X) := by
  constructor
  · rintro ⟨x, rfl⟩
    change IsClosed ({pullback.fst p q (fieldExtensionPoint p q x).val} : Set X)
    rw [fieldExtensionPoint_fst]
    exact x.property
  · intro hy
    let x : ClosedPoint X := ⟨pullback.fst p q y.val, hy⟩
    refine ⟨x, Subtype.ext ?_⟩
    have hm : y.val ∈ (pullback.fst p q) ⁻¹' ({x.val} : Set X) := rfl
    rw [preimage_singleton_fieldExtensionPoint p q x] at hm
    exact hm.symm

/-- Every target boundary closed point of a nonempty curve open is the image
of an original closed point under this same embedding. -/
theorem mem_range_fieldExtensionEmbedding_of_not_mem_preimage
    [IsIntegral X] [IsNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1) (V : X.Opens) [Nonempty V]
    (y : ClosedPoint (pullback p q))
    (hy : y.val ∉ (pullback.fst p q) ⁻¹ᵁ V) :
    y ∈ Set.range (fieldExtensionEmbedding p q) := by
  apply (mem_range_fieldExtensionEmbedding_iff p q y).mpr
  rcases Scheme.OverField.Curve.Divisors.point_eq_generic_or_isClosed X hdim
    (pullback.fst p q y.val) with hg | hc
  · exfalso
    apply hy
    change pullback.fst p q y.val ∈ V
    rw [hg]
    exact ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr
      (by simpa using (inferInstance : Nonempty V))
  · exact hc

/-- The boundary range statement for the original point function itself. -/
theorem mem_range_fieldExtensionPoint_of_not_mem_preimage
    [IsIntegral X] [IsNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1) (V : X.Opens) [Nonempty V]
    (y : ClosedPoint (pullback p q))
    (hy : y.val ∉ (pullback.fst p q) ⁻¹ᵁ V) :
    y ∈ Set.range (fieldExtensionPoint p q) :=
  mem_range_fieldExtensionEmbedding_of_not_mem_preimage p q hdim V y hy

/-- Boundary membership of the lifted point is exactly original boundary membership. -/
@[simp]
theorem fieldExtensionPoint_mem_preimage_iff (V : X.Opens) (x : ClosedPoint X) :
    (fieldExtensionPoint p q x).val ∈ (pullback.fst p q) ⁻¹ᵁ V ↔ x.val ∈ V := by
  change pullback.fst p q (fieldExtensionPoint p q x).val ∈ V ↔ x.val ∈ V
  rw [fieldExtensionPoint_fst]

end AlgebraicGeometry.Scheme.ClosedPoint
