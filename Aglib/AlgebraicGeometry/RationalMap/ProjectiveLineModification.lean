/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.ProjectiveLineDimension
public import Aglib.AlgebraicGeometry.Dimension.Finite
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.BaseChangeSource

/-! # Actual dominant projective-line graph modifications

Positive dimension supplies a transcendental affine section, hence an actual
dominant rational map to the projective line. Its native schematic graph is
integral and proper over both the original scheme and the projective line.
The original projection is surjective and is an isomorphism above the same
dense open. Its field-valued fibres are closed subschemes of a projective
line, so have dimension at most one. No normalization is performed.

The geometric dimension drop for fibres of the projection to the line is a
separate assertion, not an assumption hidden in this construction. These
results supply geometry for an auxiliary finite cohomological-dimension
argument; they do not assert the sharp cohomological bound `2 * dim X`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

open OverField OverField.Curve.Projectivity ProjectiveLine.TwoChart

universe u

/-- Every positive-dimensional integral field scheme has a genuinely
transcendental section on a nonempty affine open. No finite-type or
algebraically closed field hypothesis is needed. -/
theorem exists_affine_transcendental_of_dimension_pos
    {k : Type u} [Field k] (X : FScheme k) [IsIntegral X.left]
    (hdim : 0 < topologicalKrullDim X.left) :
    ∃ U : X.left.affineOpens, Nonempty U.1 ∧
      ∃ a : Γ(X.left, U.1),
        letI := (constantSection X U.1).toAlgebra
        Transcendental k a := by
  have hnss : ¬ Subsingleton X.left := by
    intro h
    let := h
    exact (not_le_of_gt hdim) (topologicalKrullDim_zero_of_discreteTopology X.left)
  let : Nontrivial X.left := not_subsingleton_iff_nontrivial.mp hnss
  obtain ⟨x, hx⟩ := exists_ne (genericPoint X.left)
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X.left) (U := ⊤) (x := x) (by trivial)
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hnfield : ¬ IsField Γ(X.left, U) := by
    intro hfield
    let : Field Γ(X.left, U) := hfield.toField
    let : Subsingleton (Spec Γ(X.left, U)) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum Γ(X.left, U)))
    have hUss : Subsingleton U :=
      Function.Injective.subsingleton hU.isoSpec.hom.homeomorph.injective
    have hηU : genericPoint X.left ∈ U :=
      (genericPoint_specializes x).mem_open U.isOpen hxU
    have hηx : genericPoint X.left = x :=
      congrArg Subtype.val (hUss.elim ⟨_, hηU⟩ ⟨_, hxU⟩)
    exact hx hηx.symm
  obtain ⟨a, ha0, haunit⟩ := Ring.exists_not_isUnit_of_not_isField hnfield
  let := (constantSection X U).toAlgebra
  exact ⟨⟨U, hU⟩, inferInstance, a, fun ha => haunit (ha.isIntegral.isUnit ha0)⟩

/-- Every field-valued fibre of the actual graph projection to its original
source has dimension at most one. The graph inclusion is base-changed as an
actual finite morphism into the original projective-line product. -/
theorem rationalGraphProjectionLeft_geometricFiber_dimension_le_one
    {k : Type u} [Field k] (X : FScheme k)
    (U : X.left.Opens) (r : U.toScheme ⟶ twoChartLine (.of k))
    (hr : U.ι ≫ X.hom = r ≫ projection (.of k))
    (Ω : Type u) [Field Ω] (η : Spec (.of Ω) ⟶ X.left) :
    topologicalKrullDim (pullback (C := Scheme)
      (rationalGraphProjectionLeft X (Over.mk (projection (.of k))) U r hr).left η) ≤ 1 := by
  let P : FScheme k := Over.mk (projection (.of k))
  let a := rationalGraph X P U r hr
  let b := (rationalGraphProjectionLeft X P U r hr).left
  let i : Over.mk b ⟶ Over.mk (pullback.fst X.hom P.hom) :=
    Over.homMk a.imageι rfl
  let j := ((Over.pullback η).map i).left
  have hj : IsFinite j := MorphismProperty.overPullbackMap (P := @IsFinite)
    η i (by change IsFinite a.imageι; infer_instance)
  let e₁ : pullback (pullback.fst X.hom P.hom) η ≅
      pullback P.hom (η ≫ X.hom) :=
    pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso X.hom P.hom η ≪≫
      pullbackSymmetry _ _
  let e₂ : pullback P.hom (η ≫ X.hom) ≅
      pullback (ProjectiveLine.structureMap k) (η ≫ X.hom) :=
    (Over.forget _).mapIso
      ((Over.pullback (η ≫ X.hom)).mapIso (twoChartLineOverIsoProjectiveP1 k))
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (η ≫ X.hom)
  let e₃ : pullback (ProjectiveLine.structureMap k) (η ≫ X.hom) ≅
      ProjectiveLine.projectiveP1 Ω :=
    pullback.congrHom rfl hφ.symm ≪≫
      ((Over.forget _).mapIso
        (AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.lineOverBaseChangeIso φ.hom)).symm
  have hline : topologicalKrullDim (ProjectiveLine.projectiveP1 Ω) = 1 :=
    (IsHomeomorph.topologicalKrullDim_eq _
      (twoChartLineIsoProjectiveP1 Ω).hom.homeomorph.isHomeomorph).symm.trans
        (twoChartLine_topologicalKrullDim Ω)
  calc
    _ ≤ topologicalKrullDim (pullback (C := Scheme) (pullback.fst X.hom P.hom) η) :=
      j.topologicalKrullDim_le_of_isFinite
    _ = topologicalKrullDim (ProjectiveLine.projectiveP1 Ω) :=
      IsHomeomorph.topologicalKrullDim_eq _ (e₁ ≪≫ e₂ ≪≫ e₃).hom.homeomorph.isHomeomorph
    _ = 1 := hline

/-- A positive-dimensional integral proper field scheme has an actual proper
integral graph modification with a dominant proper map to the native
projective line. The modification has geometric fibres of dimension at most
one and is an isomorphism over an explicitly supplied dense open. -/
theorem exists_proper_projectiveLine_graph_modification
    {k : Type u} [Field k] (X : FScheme k)
    [IsIntegral X.left] [IsNoetherian X.left] [IsProper X.hom]
    (hdim : 0 < topologicalKrullDim X.left) :
    ∃ (Y : Scheme.{u}) (b : Y ⟶ X.left) (g : Y ⟶ ProjectiveLine.projectiveP1 k),
      IsIntegral Y ∧ IsProper b ∧ Surjective b ∧ IsProper g ∧ IsDominant g ∧
      b ≫ X.hom = g ≫ ProjectiveLine.structureMap k ∧
      (∃ U : X.left.Opens, Nonempty U ∧ Dense (U : Set X.left) ∧ IsIso (b ∣_ U)) ∧
      topologicalKrullDim Y ≤ topologicalKrullDim X.left ∧
      ∀ (Ω : Type u) [Field Ω] (η : Spec (.of Ω) ⟶ X.left),
        topologicalKrullDim (pullback (C := Scheme) b η) ≤ 1 := by
  obtain ⟨U, hU, a, ha⟩ := exists_affine_transcendental_of_dimension_pos X hdim
  let : Nonempty U.1 := hU
  let r := affineSectionToLine X U a
  let hr := affineSectionToLine_over X U a
  let : IsDominant r := affineSectionToLine_isDominant X U a ha
  let P : FScheme k := Over.mk (projection (.of k))
  let : IsProper P.hom := inferInstanceAs (IsProper (projection (.of k)))
  let Y := (rationalGraphImage X P U.1 r hr).left
  let b := (rationalGraphProjectionLeft X P U.1 r hr).left
  let g₀ := (rationalGraphProjectionRight X P U.1 r hr).left
  let g := g₀ ≫ (twoChartLineIsoProjectiveP1 k).hom
  have hsurj : Surjective b :=
    surjective_of_isDominant_of_isClosed_range b b.isClosedMap.isClosed_range
  refine ⟨Y, b, g, inferInstance, inferInstance, hsurj, inferInstance, inferInstance,
    ?_, ⟨U.1, hU, U.1.isOpen.dense (Set.nonempty_coe_sort.mp hU), inferInstance⟩,
    rationalGraphImage_topologicalKrullDim_le X U.1 r hr, ?_⟩
  · dsimp only [g]
    rw [Category.assoc, twoChartLineIsoProjectiveP1_over]
    exact (rationalGraphProjectionRight X P U.1 r hr).w.symm
  · intro Ω _ η
    exact rationalGraphProjectionLeft_geometricFiber_dimension_le_one X U.1 r hr Ω η

end AlgebraicGeometry.Scheme
