/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.GenericClopenLift
public import Aglib.AlgebraicGeometry.Spec.AffineSectionAlgebra
public import Aglib.AlgebraicGeometry.Limits.ImmersionBaseChange
public import Aglib.AlgebraicGeometry.Morphisms.Flat.GenericFiberCriteria
public import Aglib.Topology.Clopen.DenseRange

/-! # Original generic clopens lift over a normal base

The original affine charts lift their generic idempotents. Positive and
negative open images cover the original scheme; density of the original
generic projection makes them disjoint. This constructs the unique global
clopen with the original generic preimage. No Noetherian, quasi-compactness,
quasi-separatedness, or connected-source hypothesis is imposed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

universe u

/-- Construct both original open pieces and their actual generic membership
laws on one supplied affine chart before choosing a scheme cover. -/
private theorem exists_generic_clopen_chart_pieces
    (R K B : Type u) [CommRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    (i : Spec (.of B) ⟶ X) [IsOpenImmersion i]
    (hi : i ≫ f = Spec.algebraMap R B)
    (U : (pullback f (Spec.algebraMap R K)).Opens)
    (hU : IsClosed (U : Set (pullback f (Spec.algebraMap R K) : Scheme.{u}))) :
    ∃ A C : Set X, IsOpen A ∧ IsOpen C ∧ Set.range i ⊆ A ∪ C ∧
      pullback.fst f (Spec.algebraMap R K) ⁻¹' A ⊆ U ∧
      pullback.fst f (Spec.algebraMap R K) ⁻¹' C ⊆ (U : Set _)ᶜ := by
  let b := Spec.algebraMap R K
  let p := Spec.algebraMap R B
  let m : Over.mk p ⟶ Over.mk f := Over.homMk i hi
  let a : pullback p b ⟶ pullback f b := ((Over.pullback b).map m).left
  let q := pullback.fst p b
  let g := pullback.fst f b
  let : IsOpenImmersion a := MorphismProperty.overPullbackMap
    (P := @IsOpenImmersion) b m (by change IsOpenImmersion i; infer_instance)
  have H : IsPullback q a i g := isPullback_overPullbackMap b m
  obtain ⟨V, hV, hpre⟩ := exists_clopen_generic_preimage_of_smooth_algebra R K B
    (a ⁻¹ᵁ U) (hU.preimage a.continuous)
  let Vc : (Spec (.of B)).Opens := ⟨(V : Set _)ᶜ, hV.isOpen_compl⟩
  let Uc : (pullback f b).Opens := ⟨(U : Set _)ᶜ, hU.isOpen_compl⟩
  have hprec : q ⁻¹ᵁ Vc = a ⁻¹ᵁ Uc := by
    apply TopologicalSpace.Opens.ext
    change q ⁻¹' (V : Set _)ᶜ = a ⁻¹' (U : Set _)ᶜ
    rw [Set.preimage_compl, Set.preimage_compl]
    exact congrArg (fun W : (pullback p b).Opens =>
      (W : Set (pullback p b : Scheme.{u}))ᶜ) hpre
  have hpos : g ⁻¹ᵁ (i ''ᵁ V) = a ''ᵁ (a ⁻¹ᵁ U) := by
    rw [← IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H V, hpre]
  have hneg : g ⁻¹ᵁ (i ''ᵁ Vc) = a ''ᵁ (a ⁻¹ᵁ Uc) := by
    rw [← IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H Vc, hprec]
  refine ⟨(i ''ᵁ V : Set X), (i ''ᵁ Vc : Set X), (i ''ᵁ V).isOpen,
    (i ''ᵁ Vc).isOpen, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ V
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩
  · change (g ⁻¹ᵁ (i ''ᵁ V) : Set (pullback f b : Scheme.{u})) ⊆
      (U : Set (pullback f b : Scheme.{u}))
    rw [hpos]
    exact Set.image_preimage_subset a (U : Set (pullback f b : Scheme.{u}))
  · change (g ⁻¹ᵁ (i ''ᵁ Vc) : Set (pullback f b : Scheme.{u})) ⊆
      (Uc : Set (pullback f b : Scheme.{u}))
    rw [hneg]
    exact Set.image_preimage_subset a (Uc : Set (pullback f b : Scheme.{u}))

/-- Every clopen of the original generic fibre of a smooth scheme over a
normal domain is the literal preimage of a unique original clopen. The
original fraction-field projection is used throughout, with no Noetherian
or quasi-compactness assumptions. -/
theorem existsUnique_clopen_generic_preimage_of_smooth_normalBase
    (R K : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Smooth f]
    (U : (pullback f (Spec.algebraMap R K)).Opens)
    (hU : IsClosed (U : Set (pullback f (Spec.algebraMap R K) : Scheme.{u}))) :
    ∃! V : X.Opens, IsClosed (V : Set X) ∧
      pullback.fst f (Spec.algebraMap R K) ⁻¹ᵁ V = U := by
  classical
  let g := pullback.fst f (Spec.algebraMap R K)
  have hg : DenseRange g := by
    have h := LocalRing.GenericFiber.generic_projection_dominant R K f
    change IsDominant g at h
    exact h.denseRange
  have hcharts (j : X.affineOpens) : ∃ A C : Set X, IsOpen A ∧ IsOpen C ∧
      Set.range j.2.fromSpec ⊆ A ∪ C ∧ g ⁻¹' A ⊆ U ∧ g ⁻¹' C ⊆ (U : Set _)ᶜ := by
    let B := Γ(X, j.1)
    let : Algebra R B := (affineSectionCoefficientMap f j.1).toAlgebra
    let : Algebra.Smooth R B :=
      RingHom.smooth_algebraMap.mp (affineSectionCoefficientMap_smooth f j.2)
    have hj : j.2.fromSpec ≫ f = Spec.algebraMap R B :=
      (affineSectionCoefficientMap_spec f j.2).symm
    exact exists_generic_clopen_chart_pieces R K B f j.2.fromSpec hj U hU
  choose A C hAo hCo hcover hA hC using hcharts
  have hcoverX : ∀ x : X, ∃ j, x ∈ A j ∨ x ∈ C j := by
    intro x
    obtain ⟨V, hV, hx, _⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (⊤ : X.Opens) from trivial)
    refine ⟨⟨V, hV⟩, hcover ⟨V, hV⟩ ?_⟩
    rw [hV.range_fromSpec]
    exact hx
  obtain ⟨hcl, hpre⟩ := hg.isClopen_iUnion_of_preimage_subset hAo hCo hcoverX hA hC
  let V : X.Opens := ⟨⋃ j, A j, hcl.isOpen⟩
  have he : g ⁻¹ᵁ V = U := TopologicalSpace.Opens.ext hpre
  refine ⟨V, ⟨hcl.isClosed, he⟩, ?_⟩
  intro W hW
  apply TopologicalSpace.Opens.ext
  apply hg.eq_of_isClopen_preimage_eq ⟨hW.1, W.isOpen⟩ hcl
  exact congrArg (fun O : (pullback f (Spec.algebraMap R K)).Opens =>
    (O : Set (pullback f (Spec.algebraMap R K) : Scheme.{u})))
    (hW.2.trans he.symm)

end AlgebraicGeometry.Scheme
