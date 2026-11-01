/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.ConnectedComponentsAlongSection

/-! # Original section components under field extension

The literal inverse image of the original smooth section component is the
component through the original base-changed section. The actual restriction
square and the original field pullback provide connectedness; no finiteness,
quasi-compactness, or Noetherian hypothesis is added.
-/

@[expose] public noncomputable section
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.SmoothSectionComponent
universe u

variable {k : Type u} [Field k] {Y : Scheme.{u}}
  (q : Y ⟶ Spec (.of k)) (o : Spec (.of k) ⟶ Y) (ho : o ≫ q = 𝟙 _)
  (K : Type u) [Field K] [Algebra k K]

/-- The original section in the native field-extension pullback. -/
def fieldExtensionSection : Spec (.of K) ⟶ pullback q (Spec.algebraMap k K) :=
  pullback.lift (Spec.algebraMap k K ≫ o) (𝟙 _) (by
    rw [Category.assoc, ho, Category.comp_id, Category.id_comp])

@[reassoc]
lemma fieldExtensionSection_fst : fieldExtensionSection q o ho K ≫
    pullback.fst q (Spec.algebraMap k K) = Spec.algebraMap k K ≫ o :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma fieldExtensionSection_snd : fieldExtensionSection q o ho K ≫
    pullback.snd q (Spec.algebraMap k K) = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The actual field-extension projection has literal component preimage,
not merely an abstract isomorphism of selected connected schemes. -/
theorem componentOpen_preimage_fieldExtension [Smooth q] :
    pullback.fst q (Spec.algebraMap k K) ⁻¹ᵁ componentOpen q o =
      componentOpen (pullback.snd q (Spec.algebraMap k K))
        (fieldExtensionSection q o ho K) := by
  let b := Spec.algebraMap k K
  let g := pullback.fst q b
  let qK := pullback.snd q b
  let U := componentOpen q o
  let W := g ⁻¹ᵁ U
  let oK := fieldExtensionSection q o ho K
  let : GeometricallyConnected (U.ι ≫ q) := componentMap_geometricallyConnected q o ho
  have H : IsPullback (g ∣_ U) (W.ι ≫ qK) (U.ι ≫ q) b :=
    (isPullback_morphismRestrict g U).paste_vert (.of_hasPullback q b)
  let : ConnectedSpace W.toScheme :=
    GeometricallyConnected.geometrically_connectedSpace b (g ∣_ U) (W.ι ≫ qK) H
  have hpre : _root_.IsPreconnected (W : Set (pullback q b : Scheme.{u})) := by
    have h := isConnected_univ.image W.ι W.ι.continuous.continuousOn
    rw [Set.image_univ, Opens.range_ι] at h
    exact h.2
  have hW : IsClopen (W : Set (pullback q b : Scheme.{u})) :=
    ⟨(componentOpen_isClosed q o).preimage g.continuous, W.isOpen⟩
  have hm : oK (IsLocalRing.closedPoint K) ∈ W := by
    change g (oK (IsLocalRing.closedPoint K)) ∈ U
    have he := congrArg (fun a : Spec (.of K) ⟶ Y => a (IsLocalRing.closedPoint K))
      (fieldExtensionSection_fst q o ho K)
    change g (oK (IsLocalRing.closedPoint K)) = o (b (IsLocalRing.closedPoint K)) at he
    rw [he, Subsingleton.elim (b (IsLocalRing.closedPoint K)) (IsLocalRing.closedPoint k)]
    exact mem_componentOpen q o
  have he : (W : Set (pullback q b : Scheme.{u})) =
      connectedComponent (oK (IsLocalRing.closedPoint K)) :=
    (hpre.connectedComponentIn hm).symm.trans (hW.connectedComponentIn_eq hm)
  apply TopologicalSpace.Opens.ext
  exact he.trans (componentOpen_eq_connectedComponent qK oK).symm

end AlgebraicGeometry.Scheme.SmoothSectionComponent
