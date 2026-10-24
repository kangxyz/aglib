/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.IdentityComponent.Basic
public import Aglib.AlgebraicGeometry.Properties.Noetherian.LocallyNoetherianOverBaseChange

/-!
# The identity component under field extension

Let `G` be a group scheme locally of finite type over a field `k`, and `K` a field extension of
`k`, with `b : Spec K ⟶ Spec k`. The base change `G_K = (Over.pullback b).obj G` carries the
monoid (or group) object structure of the image under the monoidal functor `Over.pullback b`
(Mathlib's `CategoryTheory.Functor.monObjObj` and `CategoryTheory.Functor.grpObjObj`, the
structures of Aglib's `AlgebraicGeometry.Scheme.Group.BaseChange.groupSchemeBaseChange`). Then
`(G_K)⁰` is the preimage of `G⁰` under the projection `G_K ⟶ G`
(`AlgebraicGeometry.Scheme.Group.identityComponent_pullback`): forming `G⁰` commutes with
extending `k` (Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Lemma 5.1(3), p. 37, by
geometric connectedness of `G⁰`).

The preimage of `G⁰` is clopen, and it is the underlying space of `(G⁰)_K`, which is connected
because `G⁰` is geometrically connected
(`AlgebraicGeometry.Scheme.Group.geometricallyConnected_identityComponentOver`). It contains the
unit point of `G_K`, which lies over the unit point of `G` (`pullback_fst_unitPoint`), so it is
the connected component of that point. As schemes, `(G⁰)_K ≅ (G_K)⁰`
(`pullbackIdentityComponentIso`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicGeometry.Scheme.Group

universe u

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [MonObj G] (K : Type u) [Field K]
  [Algebra k K]

/-- **The unit point of the base change lies over the unit point.** -/
theorem pullback_fst_unitPoint :
    pullback.fst G.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        (unitPoint ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)) =
      unitPoint G := by
  set b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  set ε := Functor.LaxMonoidal.ε (Over.pullback b)
  have h₁ : ((Over.pullback b).map η[G]).left ≫ pullback.fst G.hom b =
      pullback.fst (𝟙_ (Over (Spec (.of k)))).hom b ≫ η[G].left :=
    pullback.lift_fst _ _ _
  have h : η[(Over.pullback b).obj G].left ≫ pullback.fst G.hom b =
      ε.left ≫ pullback.fst (𝟙_ (Over (Spec (.of k)))).hom b ≫ η[G].left :=
    calc η[(Over.pullback b).obj G].left ≫ pullback.fst G.hom b
        = (ε ≫ (Over.pullback b).map η[G]).left ≫ pullback.fst G.hom b := rfl
      _ = ε.left ≫ ((Over.pullback b).map η[G]).left ≫ pullback.fst G.hom b := by
        rw [Over.comp_left, Category.assoc]
      _ = ε.left ≫ pullback.fst (𝟙_ (Over (Spec (.of k)))).hom b ≫ η[G].left := by rw [h₁]
  exact (congrArg (fun φ : (𝟙_ (Over (Spec (.of K)))).left ⟶ G.left =>
    φ (IsLocalRing.closedPoint K)) h).trans
    (one_left_apply G ((ε.left ≫ pullback.fst (𝟙_ (Over (Spec (.of k)))).hom b)
      (IsLocalRing.closedPoint K)))

variable [LocallyOfFiniteType G.hom]

/-- **The preimage of `G⁰` in `G_K` is the base change of `G⁰`**: the restriction of the
projection `G_K ⟶ G` over `G⁰` and the composite with `G_K ⟶ Spec K` form a pullback square over
`G⁰ ⟶ Spec k`. -/
theorem isPullback_preimage_identityComponent :
    IsPullback
      (pullback.fst G.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) ∣_ identityComponent G)
      ((pullback.fst G.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⁻¹ᵁ
          identityComponent G).ι ≫
        pullback.snd G.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (identityComponentOver G).hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
  (isPullback_morphismRestrict _ (identityComponent G)).paste_vert
    (IsPullback.of_hasPullback G.hom _)

/-- **The identity component commutes with field extension**: `(G_K)⁰` is the preimage of `G⁰`
under the projection `G_K ⟶ G` (Kleiman, Lemma 5.1(3), p. 37). -/
theorem identityComponent_pullback :
    identityComponent ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G) =
      pullback.fst G.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⁻¹ᵁ
        identityComponent G := by
  set b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  set π := pullback.fst G.hom b
  have hconn : ConnectedSpace (π ⁻¹ᵁ identityComponent G).toScheme :=
    GeometricallyConnected.geometrically_connectedSpace (f := (identityComponentOver G).hom) b
      (π ∣_ identityComponent G) ((π ⁻¹ᵁ identityComponent G).ι ≫ pullback.snd G.hom b)
      (isPullback_preimage_identityComponent G K)
  have hV : _root_.IsConnected (π ⁻¹ᵁ identityComponent G : Set (pullback G.hom b : Scheme.{u})) :=
    isConnected_iff_connectedSpace.mpr hconn
  have hclopen : IsClopen (π ⁻¹ᵁ identityComponent G : Set (pullback G.hom b : Scheme.{u})) :=
    (isClopen_identityComponent G).preimage π.continuous
  have hx : unitPoint ((Over.pullback b).obj G) ∈ π ⁻¹ᵁ identityComponent G := by
    have hm := unitPoint_mem_identityComponent G
    rw [← pullback_fst_unitPoint G K] at hm
    exact hm
  ext1
  exact (hclopen.connectedComponent_subset hx).antisymm
    (hV.isPreconnected.subset_connectedComponent hx)

/-- **The base change of `G⁰` is the identity component of the base change**, as schemes:
`(G⁰)_K ≅ (G_K)⁰`, from `isPullback_preimage_identityComponent` and
`identityComponent_pullback`. -/
noncomputable def pullbackIdentityComponentIso :
    (pullback (identityComponentOver G).hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
        Scheme.{u}) ≅
      (identityComponent
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)).toScheme :=
  (isPullback_preimage_identityComponent G K).isoPullback.symm ≪≫
    Scheme.isoOfEq _ (identityComponent_pullback G K).symm

end AlgebraicGeometry.Scheme.Group
