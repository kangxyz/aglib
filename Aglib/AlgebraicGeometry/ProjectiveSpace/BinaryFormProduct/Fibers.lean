/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Native geometric-point criteria for the binary-form product proof

Finite fibres of algebraically closed field-valued points imply finite
topological scheme fibres for a proper map. The native quasi-finite and
Zariski-main-theorem interfaces then give actual finiteness. Geometric
point lifting gives actual surjectivity without a properness premise.

The finite point-fibre hypothesis is a precise remaining obligation for
the binary-form map, not an assumed finiteness conclusion.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct

universe u

private theorem finite_pullback_of_finite_point_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (K : Type u) [Field K] [IsAlgClosed K] (g : Spec (CommRingCat.of K) ⟶ Y)
    [Finite {s : Spec (CommRingCat.of K) ⟶ X // s ≫ f = g}] :
    Finite (Limits.pullback f g : Scheme.{u}) := by
  let W : Scheme.{u} := Limits.pullback f g
  let w : W ⟶ Spec (CommRingCat.of K) := Limits.pullback.snd f g
  have : IsProper w := by dsimp only [w]; infer_instance
  have : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace w
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace w
  let toLift : {s : Spec (CommRingCat.of K) ⟶ W // s ≫ w = 𝟙 _} →
      {s : Spec (CommRingCat.of K) ⟶ X // s ≫ f = g} := fun s =>
    ⟨s.val ≫ Limits.pullback.fst f g, by
      rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, s.property,
        Category.id_comp]⟩
  have hinj : Function.Injective toLift := by
    intro a b h
    apply Subtype.ext
    apply Limits.pullback.hom_ext
    · exact congrArg Subtype.val h
    · exact a.property.trans b.property.symm
  have : Finite {s : Spec (CommRingCat.of K) ⟶ W // s ≫ w = 𝟙 _} :=
    Finite.of_injective toLift hinj
  have : Finite (closedPoints W) := Finite.of_equiv _ (pointEquivClosedPoint w)
  have : DiscreteTopology W := JacobsonSpace.discreteTopology
    (Set.finite_coe_iff.mp (show Finite (closedPoints W) from inferInstance))
  exact finite_of_compact_of_discrete

/-- Properness and the actual finite geometric point fibres imply finiteness
of the original scheme morphism, through native quasi-finiteness and Zariski main. -/
theorem isFinite_of_finite_geometric_point_fibers
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (g : Spec (CommRingCat.of K) ⟶ Y),
      Finite {s : Spec (CommRingCat.of K) ⟶ X // s ≫ f = g}) : IsFinite f := by
  have hfiber (y : Y) : Finite (f.fiber y) := by
    let k : Type u := Y.residueField y
    let K := AlgebraicClosure k
    let b : Spec (CommRingCat.of K) ⟶ Spec (Y.residueField y) := Spec.algebraMap k K
    let g : Spec (CommRingCat.of K) ⟶ Y := b ≫ Y.fromSpecResidueField y
    have : Surjective b := ⟨fun x => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ x⟩⟩
    have : Finite {s : Spec (CommRingCat.of K) ⟶ X // s ≫ f = g} := h K g
    have : Finite (Limits.pullback f g : Scheme.{u}) :=
      finite_pullback_of_finite_point_fiber f K g
    let e := pullbackLeftPullbackSndIso f (Y.fromSpecResidueField y) b
    have : Finite (Limits.pullback (f.fiberToSpecResidueField y) b : Scheme.{u}) :=
      Finite.of_injective (fun x : (Limits.pullback
        (f.fiberToSpecResidueField y) b : Scheme.{u}) => e.hom x)
          (by intro a b hab; exact e.hom.homeomorph.injective hab)
    have : Surjective (Limits.pullback.fst (f.fiberToSpecResidueField y) b) :=
      MorphismProperty.pullback_fst _ _ inferInstance
    exact Finite.of_surjective _
      (Limits.pullback.fst (f.fiberToSpecResidueField y) b).surjective
  have : LocallyQuasiFinite f := LocallyQuasiFinite.of_finite_preimage_singleton f (fun y => by
    have : Finite (f.fiber y) := hfiber y
    have : Finite (f ⁻¹' {y}) := Finite.of_equiv _ (f.fiberHomeo y).toEquiv
    exact Set.finite_coe_iff.mp (show Finite (f ⁻¹' {y}) from inferInstance))
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

/-- Actual lifting of algebraically closed field-valued points implies
surjectivity of the original scheme morphism. -/
theorem surjective_of_geometric_point_lifting
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (g : Spec (CommRingCat.of K) ⟶ Y),
      ∃ s : Spec (CommRingCat.of K) ⟶ X, s ≫ f = g) : Surjective f := by
  constructor
  intro y
  let k : Type u := Y.residueField y
  let K := AlgebraicClosure k
  let g : Spec (CommRingCat.of K) ⟶ Y :=
    Spec.algebraMap k K ≫ Y.fromSpecResidueField y
  obtain ⟨s, hs⟩ := h K g
  refine ⟨s (IsLocalRing.closedPoint K), ?_⟩
  have hp := congrArg (fun a : Spec (CommRingCat.of K) ⟶ Y =>
    a (IsLocalRing.closedPoint K)) hs
  change f (s (IsLocalRing.closedPoint K)) =
    Y.fromSpecResidueField y ((Spec.algebraMap k K) (IsLocalRing.closedPoint K)) at hp
  exact hp.trans (Scheme.fromSpecResidueField_apply y
    ((Spec.algebraMap k K) (IsLocalRing.closedPoint K)))

end AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct
