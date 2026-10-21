/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FundamentalGroup.GeometricKernel
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Connectedness
public import Mathlib.Algebra.Group.Subgroup.Actions

/-!
# Geometric connectedness from the actual arithmetic-kernel action

Source packet: `R5Lab.Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GeometricConnectedness`,
SHA-256 `64ca2a144b6c241f3a0a117cc18a67a80114cb05f0a6b63452659569f87c567b`.
Current consumer: the actual multiplication-cover quotient surjectivity theorem.

This is the geometric-connectedness bridge for the primitive-cover paragraph of
`K2-018#prop:k2018-arithmetic-characters`, on source bases
`e73d98b1b5c1e5abcdebf7d058e436d792b87982` and
`ac804cb2f648f42380e612235b972786506d0b9f`.
The frozen connectedness comparison is `Connectedness.lean`, SHA256
`c6b16712e10db03179f0f93657a29ff58bd49d2d9a52e606a54e2c8545e774f0`;
the actual kernel map is `GeometricKernel.lean`, SHA256
`8828c7bc19fdcf20e85b9a1805b949b6ffa8974fa22b4d86f90373b95cb24dbe`.

The pullback-composition isomorphism compares the entire base-changed total
scheme with the underlying scheme of the pulled-back cover. It is also an
isomorphism over the extension field, and its effect on the actual field-valued
points is proved. The existing pointed fibre equivalence intertwines the actual
geometric-group action with restriction to the actual arithmetic projection
kernel. No replacement action or point-normalization premise is introduced.

For a proper geometrically connected scheme with a rational section, the final
criterion retains `GeometricKernel.Stacks0BTX F`, the standard Galois-category
and fibre-functor classes on the actual geometric base change, and the explicitly
named universal premise `Stacks0387 F`. The latter is the connected-algebraic-
closure criterion of Stacks Project, Lemma 33.7.7, tag `0387`,
https://stacks.math.columbia.edu/tag/0387 (statement and proof inspected).
That lemma applies to every scheme over a field and a separable algebraic closure.
Here characteristic zero allows the displayed `AlgebraicClosure F`; there is no
finite-type restriction on the schemes quantified by the premise. Only its
implication from connected base change to geometric connectedness is retained;
the converse uses mathlib. No proof or global instance of this premise is supplied.

The conclusion is geometric connectedness of the actual total scheme exactly
when its actual fibre is nonempty and the actual projection kernel acts
pretransitively. The evaluation version exposes the kernel's natural-automorphism
components directly for use with an existing equivariant fibre marking. The
standard classes on the original scheme, needed for inverse classification in
the consumer, are not needed by this geometric criterion itself.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.PreGaloisCategory
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange fiberToFinite)
open _root_.AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open _root_.AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel

namespace AlgebraicGeometry.Scheme.FiniteEtale.GeometricCoverConnectedness
universe u

section BaseChange
variable {B X : Scheme.{u}} {K : Type u} [Field K]
variable (b : Spec (CommRingCat.of K) ⟶ B) (p : X ⟶ B)

/-- The actual pullback of a finite étale cover along the first geometric projection. -/
abbrev pulledbackCover (Y : Scheme.FiniteEtale X) : Scheme.FiniteEtale (pullback p b) :=
  (baseChange (pullback.fst p b)).obj Y

/-- Pulling back the cover and then forgetting to its total scheme agrees with
base-changing the total scheme over the original base. -/
def totalBaseChangeIso (Y : Scheme.FiniteEtale X) :
    (pulledbackCover b p Y).obj.left ≅ pullback (Y.obj.hom ≫ p) b :=
  pullbackRightPullbackFstIso p b Y.obj.hom

/-- The total-space comparison preserves the projection to the original cover. -/
@[simp] theorem totalBaseChangeIso_hom_fst (Y : Scheme.FiniteEtale X) :
    (totalBaseChangeIso b p Y).hom ≫ pullback.fst (Y.obj.hom ≫ p) b =
      pullback.fst Y.obj.hom (pullback.fst p b) :=
  pullbackRightPullbackFstIso_hom_fst p b Y.obj.hom

/-- The total-space comparison preserves the entire extension-field structure map. -/
@[simp] theorem totalBaseChangeIso_hom_snd (Y : Scheme.FiniteEtale X) :
    (totalBaseChangeIso b p Y).hom ≫ pullback.snd (Y.obj.hom ≫ p) b =
      (pulledbackCover b p Y).obj.hom ≫ pullback.snd p b :=
  pullbackRightPullbackFstIso_hom_snd p b Y.obj.hom

/-- The total-space comparison is an isomorphism of schemes over the extension field. -/
def totalBaseChangeOverIso (Y : Scheme.FiniteEtale X) :
    Over.mk ((pulledbackCover b p Y).obj.hom ≫ pullback.snd p b) ≅
      Over.mk (pullback.snd (Y.obj.hom ≫ p) b) :=
  Over.isoMk (totalBaseChangeIso b p Y) (totalBaseChangeIso_hom_snd b p Y)

/-- Connectedness is transported through the actual total-space isomorphism. -/
theorem connected_pulledbackCover_iff (Y : Scheme.FiniteEtale X) :
    ConnectedSpace (pulledbackCover b p Y).obj.left ↔
      ConnectedSpace (pullback (Y.obj.hom ≫ p) b : Scheme.{u}) :=
  (totalBaseChangeIso b p Y).hom.homeomorph.connectedSpace_iff

variable (o : B ⟶ X) (h : o ≫ p = 𝟙 B)

/-- The actual pointed pullback identifies the two finite fibres. -/
def baseChangedFiberEquiv (Y : Scheme.FiniteEtale X) :
    (fiberToFinite (b ≫ o)).obj Y ≃
      (fiberToFinite (baseChangePoint b p o h)).obj (pulledbackCover b p Y) :=
  pointedFiberEquiv (pointedInclusion b p o h) Y

/-- Under the total-space comparison, the transported point is the actual pullback
lift of the original point and the identity field morphism. -/
theorem totalBaseChangeIso_point (Y : Scheme.FiniteEtale X) (q : Fiber (b ≫ o) Y) :
    (baseChangedFiberEquiv b p o h Y q).left ≫ (totalBaseChangeIso b p Y).hom =
      pullback.lift q.left (𝟙 _) (by
        rw [Category.id_comp, ← Category.assoc, Over.w]
        change (b ≫ o) ≫ p = b
        rw [Category.assoc, h, Category.comp_id]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, totalBaseChangeIso_hom_fst]
    change (pointedFiberEquiv (pointedInclusion b p o h) Y q).left ≫ _ = _
    rw [pointedFiberEquiv_left, pullback.lift_fst]
    change pullback.lift (f := Y.obj.hom) (g := pullback.fst p b)
      q.left (baseChangePoint b p o h) _ ≫ pullback.fst Y.obj.hom (pullback.fst p b) = q.left
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, totalBaseChangeIso_hom_snd, ← Category.assoc]
    rw [pullback.lift_snd]
    exact (congrArg (fun f => f ≫ pullback.snd p b)
      (Over.w (baseChangedFiberEquiv b p o h Y q))).trans (baseChangePoint_snd b p o h)

end BaseChange

/-- Explicit retained implication from Stacks Lemma 33.7.7 (`0387`), in characteristic
zero. It quantifies over every actual scheme over `F`, independently of the cover
to which it will be applied; it is not a target-specific connectedness premise. -/
structure Stacks0387 (F : Type u) [Field F] [CharZero F] : Prop where
  /-- Connectedness after the displayed algebraic-closure base change detects
  geometric connectedness of any scheme over `F`. -/
  geometricallyConnected_of_connected_algebraicClosure :
    ∀ {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of F)),
      ConnectedSpace (pullback q (algebraicClosurePoint F) : Scheme.{u}) → GeometricallyConnected q

section Field
variable (F : Type u) [Field F]
variable {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of F))
variable (o : Spec (CommRingCat.of F) ⟶ X) (h : o ≫ p = 𝟙 _)

/-- The actual finite étale cover of the geometric base change. -/
abbrev geometricCover (Y : Scheme.FiniteEtale X) : Scheme.FiniteEtale (geometricBaseChange F p) :=
  pulledbackCover (algebraicClosurePoint F) p Y

/-- The actual fibre identification for the chosen algebraic-closure point. -/
abbrev geometricFiberEquiv (Y : Scheme.FiniteEtale X) :
    (fiberToFinite (algebraicClosurePoint F ≫ o)).obj Y ≃
      (fiberToFinite (geometricPoint F p o h)).obj (geometricCover F p Y) :=
  baseChangedFiberEquiv (algebraicClosurePoint F) p o h Y

/-- The subgroup action is exactly evaluation of the underlying natural fibre automorphism. -/
@[simp] theorem kernel_smul (Y : Scheme.FiniteEtale X) (n : ArithmeticKernel F p o h)
    (q : (fiberToFinite (algebraicClosurePoint F ≫ o)).obj Y) :
    n • q = (n : FiberAutGroup (algebraicClosurePoint F ≫ o)).hom.app Y q := rfl

/-- The actual pointed fibre equivalence intertwines the constructed geometric
map into the kernel with the geometric-group action. No exactness is used here. -/
theorem geometricFiberEquiv_kernelHom_smul (Y : Scheme.FiniteEtale X) (a : GeometricGroup F p o h)
    (q : (fiberToFinite (algebraicClosurePoint F ≫ o)).obj Y) :
    geometricFiberEquiv F p o h Y (geometricKernelHom F p o h a • q) =
      a • geometricFiberEquiv F p o h Y q := by
  change (pointedFiberEquiv (pointedInclusion (algebraicClosurePoint F) p o h) Y)
    ((geometricKernelHom F p o h a : FiberAutGroup (algebraicClosurePoint F ≫ o)).hom.app Y q) = _
  rw [geometricKernelHom_evaluate, Equiv.apply_symm_apply]
  rfl

section ClosureCheck
variable [CharZero F] (h0387 : Stacks0387 F)

include h0387 in
/-- The retained universal Stacks criterion and the actual total-space isomorphism
identify geometric connectedness with connectedness of the pulled-back cover. -/
theorem geometricallyConnected_iff_connected_geometricCover (Y : Scheme.FiniteEtale X) :
    GeometricallyConnected (Y.obj.hom ≫ p) ↔ ConnectedSpace (geometricCover F p Y).obj.left := by
  constructor
  · intro hY
    let := hY
    apply (connected_pulledbackCover_iff (algebraicClosurePoint F) p Y).mpr
    exact pullback_of_geometrically GeometricallyConnected.geometrically_connectedSpace
      (AlgebraicClosure F) (algebraicClosurePoint F)
  · intro hY
    exact h0387.geometricallyConnected_of_connected_algebraicClosure (Y.obj.hom ≫ p)
      ((connected_pulledbackCover_iff (algebraicClosurePoint F) p Y).mp hY)

end ClosureCheck

variable (h0BTX : Stacks0BTX F) [IsProper p] [GeometricallyConnected p]

/-- Under Stacks `0BTX`, the constructed kernel equivalence preserves the actual
fibre actions through the canonical pointed fibre identification. -/
theorem geometricFiberEquiv_kernelEquiv_smul (Y : Scheme.FiniteEtale X) (a : GeometricGroup F p o h)
    (q : (fiberToFinite (algebraicClosurePoint F ≫ o)).obj Y) :
    geometricFiberEquiv F p o h Y (geometricKernelContinuousEquiv F h0BTX p o h a • q) =
      a • geometricFiberEquiv F p o h Y q :=
  geometricFiberEquiv_kernelHom_smul F p o h Y a q

include h0BTX in
/-- Stacks `0BTX` identifies actual-kernel pretransitivity with pretransitivity
on the fibre of the actual geometric cover. -/
theorem kernel_pretransitive_iff (Y : Scheme.FiniteEtale X) :
    MulAction.IsPretransitive (ArithmeticKernel F p o h)
      ((fiberToFinite (algebraicClosurePoint F ≫ o)).obj Y) ↔
    MulAction.IsPretransitive (GeometricGroup F p o h)
      ((fiberToFinite (geometricPoint F p o h)).obj (geometricCover F p Y)) := by
  let e := geometricFiberEquiv F p o h Y
  let c := geometricKernelContinuousEquiv F h0BTX p o h
  constructor
  · intro H
    constructor
    intro x y
    obtain ⟨n, hn⟩ := H.exists_smul_eq (e.symm x) (e.symm y)
    obtain ⟨a, ha⟩ := c.surjective n
    refine ⟨a, ?_⟩
    have he := congrArg e hn
    rw [← ha] at he
    change geometricFiberEquiv F p o h Y (geometricKernelContinuousEquiv F h0BTX p o h a •
      e.symm x) = e (e.symm y) at he
    rw [geometricFiberEquiv_kernelEquiv_smul] at he
    simpa only [e, Equiv.apply_symm_apply] using he
  · intro H
    constructor
    intro x y
    obtain ⟨a, ha⟩ := H.exists_smul_eq (e x) (e y)
    refine ⟨c a, e.injective ?_⟩
    change geometricFiberEquiv F p o h Y (geometricKernelContinuousEquiv F h0BTX p o h a • x) = _
    rw [geometricFiberEquiv_kernelEquiv_smul]
    exact ha

section Connectedness
variable [GaloisCategory (Scheme.FiniteEtale (geometricBaseChange F p))]
  [PreGaloisCategory.FiberFunctor (fiberToFinite (geometricPoint F p o h))]

include h0BTX in
/-- The physical connectedness comparison turns the geometric action criterion
into the nonempty transitive action of the actual arithmetic kernel. -/
theorem connected_geometricCover_iff_kernel_transitive (Y : Scheme.FiniteEtale X) :
    ConnectedSpace (geometricCover F p Y).obj.left ↔
      Nonempty ((fiberToFinite (algebraicClosurePoint F ≫ o)).obj Y) ∧
        MulAction.IsPretransitive (ArithmeticKernel F p o h)
          ((fiberToFinite (algebraicClosurePoint F ≫ o)).obj Y) := by
  exact (_root_.AlgebraicGeometry.Scheme.FiniteEtale.Connectedness.connectedSpace_iff_transitive
    (geometricPoint F p o h) (geometricCover F p Y)).trans
      (and_congr (geometricFiberEquiv F p o h Y).nonempty_congr.symm
        (kernel_pretransitive_iff F p o h h0BTX Y).symm)

variable [CharZero F] (h0387 : Stacks0387 F)

include h0BTX h0387 in
/-- Geometric connectedness of an actual total scheme is equivalent to a nonempty
transitive actual-kernel fibre action, with both retained standard theorems explicit. -/
theorem geometricallyConnected_iff_kernel_transitive (Y : Scheme.FiniteEtale X) :
    GeometricallyConnected (Y.obj.hom ≫ p) ↔
      Nonempty ((fiberToFinite (algebraicClosurePoint F ≫ o)).obj Y) ∧
        MulAction.IsPretransitive (ArithmeticKernel F p o h)
          ((fiberToFinite (algebraicClosurePoint F ≫ o)).obj Y) :=
  (geometricallyConnected_iff_connected_geometricCover F p h0387 Y).trans
    (connected_geometricCover_iff_kernel_transitive F p o h h0BTX Y)

include h0BTX h0387 in
/-- The same criterion in direct natural-automorphism evaluations, for consumers
with an equivariant marking of the actual fibre. -/
theorem geometricallyConnected_iff_kernel_evaluation (Y : Scheme.FiniteEtale X) :
    GeometricallyConnected (Y.obj.hom ≫ p) ↔
      Nonempty (Fiber (algebraicClosurePoint F ≫ o) Y) ∧
        ∀ q r : Fiber (algebraicClosurePoint F ≫ o) Y,
          ∃ n : ArithmeticKernel F p o h,
            (n : FiberAutGroup (algebraicClosurePoint F ≫ o)).hom.app Y q = r := by
  rw [geometricallyConnected_iff_kernel_transitive F p o h h0BTX h0387 Y]
  constructor
  · rintro ⟨hne, htrans⟩
    exact ⟨hne, fun q r => htrans.exists_smul_eq q r⟩
  · rintro ⟨hne, htrans⟩
    exact ⟨hne, ⟨htrans⟩⟩

end Connectedness
end Field
end AlgebraicGeometry.Scheme.FiniteEtale.GeometricCoverConnectedness
