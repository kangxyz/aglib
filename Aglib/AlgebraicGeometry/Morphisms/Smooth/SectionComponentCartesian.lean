/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.SectionComponentFieldExtension

/-! # Section components in the original field cartesian square

Transport the single native field-extension construction through the original
cartesian square and its projection laws. The original sections, not merely
chosen points in isomorphic schemes, are compared.
-/

@[expose] public noncomputable section
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.SmoothSectionComponent
universe u

/-- The literal preimage under the original cartesian projection is the
connected component through the original compatible section. -/
theorem componentOpen_preimage_of_isPullback
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {Y Z : Scheme.{u}} (q : Y ⟶ Spec (.of k)) [Smooth q]
    (a : Z ⟶ Y) (r : Z ⟶ Spec (.of K))
    (H : IsPullback a r q (Spec.algebraMap k K))
    (o : Spec (.of k) ⟶ Y) (ho : o ≫ q = 𝟙 _)
    (o' : Spec (.of K) ⟶ Z) (ho' : o' ≫ r = 𝟙 _)
    (hsection : o' ≫ a = Spec.algebraMap k K ≫ o) :
    a ⁻¹' (componentOpen q o : Set Y) =
      connectedComponent (o' (IsLocalRing.closedPoint K)) := by
  let b := Spec.algebraMap k K
  let e := H.isoPullback
  let oK := fieldExtensionSection q o ho K
  let η := IsLocalRing.closedPoint K
  have hsection' : o' ≫ e.hom = oK := by
    apply pullback.hom_ext
    · rw [Category.assoc, H.isoPullback_hom_fst, hsection]
      exact (fieldExtensionSection_fst q o ho K).symm
    · rw [Category.assoc, H.isoPullback_hom_snd, ho']
      exact (fieldExtensionSection_snd q o ho K).symm
  have hpoint : e.hom (o' η) = oK η :=
    congrArg (fun t : Spec (.of K) ⟶ pullback q b => t η) hsection'
  have hnative : pullback.fst q b ⁻¹' (componentOpen q o : Set Y) =
      connectedComponent (oK η) := by
    have h := congrArg (fun U : (pullback q b).Opens =>
      (U : Set (pullback q b : Scheme.{u}))) (componentOpen_preimage_fieldExtension q o ho K)
    exact h.trans (componentOpen_eq_connectedComponent (pullback.snd q b) oK)
  have hproj (z : Z) : pullback.fst q b (e.hom z) = a z :=
    congrArg (fun t : Z ⟶ Y => t z) H.isoPullback_hom_fst
  ext z
  constructor
  · intro hz
    have hn : e.hom z ∈ connectedComponent (oK η) := by
      rw [← hnative]
      change pullback.fst q b (e.hom z) ∈ componentOpen q o
      rw [hproj]
      exact hz
    rw [← hpoint] at hn
    have hh := e.inv.continuous.mapsTo_connectedComponent (e.hom (o' η)) hn
    have hi (w : Z) : e.inv (e.hom w) = w :=
      congrArg (fun t : Z ⟶ Z => t w) e.hom_inv_id
    simpa only [hi] using hh
  · intro hz
    have hn := e.hom.continuous.mapsTo_connectedComponent (o' η) hz
    rw [hpoint, ← hnative] at hn
    change pullback.fst q b (e.hom z) ∈ componentOpen q o at hn
    rwa [hproj] at hn

end AlgebraicGeometry.Scheme.SmoothSectionComponent
