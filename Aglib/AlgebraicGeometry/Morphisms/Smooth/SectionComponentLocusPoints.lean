/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.SectionComponentLocus

/-! # Original point interpretations of the section-component locus

The original section-point interpretation and the field-base interpretation
connect native fibre statements to the single original locus. No additional
smoothness or finiteness hypothesis is needed for these point identities.
-/

@[expose] public noncomputable section
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme
universe u

/-- The original residue section maps to the original section point. -/
lemma sectionOnFiber_point_fiberι {X S : Scheme.{u}} (f : X ⟶ S)
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 _) (s : S) :
    f.fiberι s (sectionOnFiber f σ hσ s (IsLocalRing.closedPoint (S.residueField s))) = σ s := by
  have h := congrArg (fun a : Spec (S.residueField s) ⟶ X =>
    a (IsLocalRing.closedPoint (S.residueField s))) (sectionOnFiber_fiberι f σ hσ s)
  change f.fiberι s (sectionOnFiber f σ hσ s (IsLocalRing.closedPoint (S.residueField s))) =
    σ (S.fromSpecResidueField s (IsLocalRing.closedPoint (S.residueField s))) at h
  exact h.trans (congrArg σ (S.fromSpecResidueField_apply s
    (IsLocalRing.closedPoint (S.residueField s))))

/-- Membership of an original second section in the locus is exactly the
same-component condition on the two original residue-field sections. -/
theorem section_point_mem_sectionComponentLocus_iff {X S : Scheme.{u}} (f : X ⟶ S)
    (σ τ : S ⟶ X) (hσ : σ ≫ f = 𝟙 _) (hτ : τ ≫ f = 𝟙 _) (s : S) :
    τ s ∈ sectionComponentLocus f σ hσ ↔
      sectionOnFiber f τ hτ s (IsLocalRing.closedPoint (S.residueField s)) ∈
        connectedComponent (sectionOnFiber f σ hσ s
          (IsLocalRing.closedPoint (S.residueField s))) := by
  have h := mem_sectionComponentLocus_fiberι_iff f σ hσ s
    (sectionOnFiber f τ hτ s (IsLocalRing.closedPoint (S.residueField s)))
  rw [sectionOnFiber_point_fiberι] at h
  exact h

/-- Over a field the original fibre inclusion is a surjective embedding, so
the original locus is precisely the component of the original rational point. -/
theorem sectionComponentLocus_eq_connectedComponent_of_field
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _) :
    sectionComponentLocus f σ hσ = connectedComponent (σ (IsLocalRing.closedPoint k)) := by
  let s : Spec (.of k) := IsLocalRing.closedPoint k
  let g := f.fiberι s
  have hg : Function.Surjective g := by
    intro x
    have h : x ∈ Set.range (f.fiberι s) := by
      rw [f.range_fiberι]
      exact Subsingleton.elim _ _
    exact h
  let e := g.isEmbedding.toHomeomorphOfSurjective hg
  let γ := sectionOnFiber f σ hσ s (IsLocalRing.closedPoint ((Spec (.of k)).residueField s))
  have hγ : g γ = σ s := sectionOnFiber_point_fiberι f σ hσ s
  have hγ' : e.symm (σ s) = γ := by
    rw [← hγ]
    exact e.symm_apply_apply γ
  ext x
  obtain ⟨z, rfl⟩ := hg x
  rw [mem_sectionComponentLocus_fiberι_iff]
  constructor
  · intro hz
    have h := g.continuous.mapsTo_connectedComponent γ hz
    rw [hγ] at h
    exact h
  · intro hz
    have h := e.symm.continuous.mapsTo_connectedComponent (σ s) hz
    change e.symm (e z) ∈ connectedComponent (e.symm (σ s)) at h
    simpa only [e.symm_apply_apply, hγ'] using h

end AlgebraicGeometry.Scheme
