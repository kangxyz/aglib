/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.SectionComponentLocusPoints

/-! # Recognizing the original locus from an actual clopen

An original clopen whose structural morphism is geometrically connected and
which contains the original section is precisely the original section-component
locus. The proof uses the actual fibre restriction square, not a supplied
locus equality or replacement connected model.
-/

@[expose] public noncomputable section
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme
universe u

/-- An actual clopen with geometrically connected fibres and the original
lifted section is exactly the fibrewise section-component locus. -/
theorem sectionComponentLocus_eq_clopen
    {X S : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 _)
    (V : X.Opens) (hV : IsClosed (V : Set X))
    (τ : S ⟶ V.toScheme) (hτ : τ ≫ V.ι = σ)
    [GeometricallyConnected (V.ι ≫ f)] :
    sectionComponentLocus f σ hσ = (V : Set X) := by
  have hσV (s : S) : σ s ∈ V := by
    have h := congrArg (fun a : S ⟶ X => a s) hτ
    change V.ι (τ s) = σ s at h
    exact h ▸ (τ s).property
  have hcomponent (s : S) :
      (f.fiberι s ⁻¹ᵁ V : Set (f.fiber s)) =
        connectedComponent (sectionOnFiber f σ hσ s
          (IsLocalRing.closedPoint (S.residueField s))) := by
    let g := f.fiberι s
    let q := f.fiberToSpecResidueField s
    let W := g ⁻¹ᵁ V
    have H : IsPullback (g ∣_ V) (W.ι ≫ q) (V.ι ≫ f)
        (S.fromSpecResidueField s) :=
      (isPullback_morphismRestrict g V).paste_vert (.of_hasPullback f _)
    let : ConnectedSpace W.toScheme :=
      GeometricallyConnected.geometrically_connectedSpace (S.fromSpecResidueField s)
        (g ∣_ V) (W.ι ≫ q) H
    have hp : _root_.IsPreconnected (W : Set (f.fiber s)) := by
      have h := isConnected_univ.image W.ι W.ι.continuous.continuousOn
      rw [Set.image_univ, Opens.range_ι] at h
      exact h.2
    have hW : IsClopen (W : Set (f.fiber s)) :=
      ⟨hV.preimage g.continuous, W.isOpen⟩
    have hm : sectionOnFiber f σ hσ s (IsLocalRing.closedPoint (S.residueField s)) ∈ W := by
      change f.fiberι s (sectionOnFiber f σ hσ s
        (IsLocalRing.closedPoint (S.residueField s))) ∈ V
      rw [sectionOnFiber_point_fiberι]
      exact hσV s
    exact (hp.connectedComponentIn hm).symm.trans (hW.connectedComponentIn_eq hm)
  ext x
  rw [mem_sectionComponentLocus_iff, ← hcomponent]
  change f.fiberι (f x) (f.asFiber x) ∈ V ↔ x ∈ V
  rw [Hom.fiberι_asFiber]

end AlgebraicGeometry.Scheme
