/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.OpenRecovery
public import Aglib.AlgebraicGeometry.Morphisms.Etale.PointwiseOpenBaseChange
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # The original normalization is etale over its original cover open

The proved original-cover pullback supplies an actual cover point over every
normalization point lying above the open. Its original open inclusion carries
an etale source neighborhood back to the unchanged normalization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

/-- The actual normalization is etale at every original point over the original
finite-etale cover open. No global finite-presentation hypothesis is added. -/
theorem fromNormalization_etaleAt_of_image_mem
    {X U E : Scheme.{u}} [IsIntegral X] [Nonempty U]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (j : U ⟶ X) [IsOpenImmersion j] (p : E ⟶ U) [IsFinite p] [Etale p]
    (x : (genericMap j p).normalization)
    (hx : (genericMap j p).fromNormalization x ∈ Set.range j) :
    (genericMap j p).fromNormalization.etaleAt x := by
  let q := genericMap j p
  obtain ⟨u, hu⟩ := hx
  obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := q.fromNormalization) (g := j) x u hu.symm
  let H := isPullback j p
  let y := H.isoPullback.inv z
  have hy : inclusion j p y = x := by
    have h := congrArg (fun k : pullback q.fromNormalization j ⟶ q.normalization => k z)
      H.isoPullback_inv_fst
    exact h.trans hz
  let : Etale (inclusion j p ≫ q.fromNormalization) := by
    rw [inclusion_over]
    infer_instance
  have hlocal : (inclusion j p ≫ q.fromNormalization).etaleAt y :=
    ⟨⊤, trivial, inferInstance⟩
  have h := Scheme.Hom.etaleAt.of_comp_openImmersion
    (inclusion j p) q.fromNormalization y hlocal
  rwa [hy] at h

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
