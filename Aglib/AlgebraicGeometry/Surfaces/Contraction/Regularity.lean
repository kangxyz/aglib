/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Contraction.FormalNeighborhood.LocalCoordinates
public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.RegularQuotient
public import Aglib.AlgebraicGeometry.Properties.Regular.ClosedPoints
public import Aglib.AlgebraicGeometry.Properties.Normal.Components
public import Aglib.AlgebraicGeometry.Properties.Normal.GlobalSections
public import Aglib.RingTheory.RegularLocalRing.Normal
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Regularity of the original local source of a Cartier contraction

`Aglib.AlgebraicGeometry.Surfaces.Contraction.Regularity` proves regularity and normality of
the actual local-spectrum pullback from a regular Cartier closed fibre. A connected original
closed fibre gives connectedness and integrality of this local source. Transfer of normality
to the original target stalk retains bijectivity of its actual structural map as an explicit
premise; it is not used in the regularity or connectedness arguments.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Surfaces.Contraction.FormalNeighborhood

namespace AlgebraicGeometry.Scheme.Surfaces.Contraction

universe u

variable {k : Type u} [Field k] {C X Z : Scheme.{u}}
  (c : Spec (.of k) ⟶ Z) [IsClosedImmersion c]
  (f : X ⟶ Z) [IsProper f] (i : C ⟶ X) [IsClosedImmersion i]
  (a : C ⟶ Spec (.of k)) (w : a ≫ c = i ≫ f)
  (hker : c.ker.comap f = i.ker)

include i a w hker

omit [IsProper f] in
private theorem exists_localExceptional_preimage_of_closedFibre
    (x : localSource f (imagePoint c))
    (hx : localSourceMap f (imagePoint c) x = IsLocalRing.closedPoint (pointLocalRing c)) :
    ∃ y : C, localExceptional c f i a w y = x := by
  let q := Spec.map (Scheme.stalkClosedPointTo c)
  let : IsClosedImmersion q :=
    IsClosedImmersion.spec_of_surjective _ (pointResidueHom_surjective c)
  have hq : q (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint (pointLocalRing c) :=
    @Scheme.image_closedPoint_eq_closedPoint (pointLocalRing c)
      (CommRingCat.commRing (pointLocalRing c))
      (Z.toLocallyRingedSpace.isLocalRing (imagePoint c)) (Spec (.of k)) q inferInstance
      (IsLocalRing.closedPoint k)
      (IsLocalRing.isClosed_singleton_closedPoint k)
  obtain ⟨p, hp, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := localSourceMap f (imagePoint c)) (g := q)
    x (IsLocalRing.closedPoint k) (hx.trans hq.symm)
  have hpb : IsPullback (localExceptional c f i a w) a
      (localSourceMap f (imagePoint c)) q :=
    localExceptional_isPullback c f i a w hker
  refine ⟨hpb.isoPullback.inv p, ?_⟩
  have hj : localExceptional c f i a w (hpb.isoPullback.inv p) =
      pullback.fst (localSourceMap f (imagePoint c)) q p := by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun m : pullback (localSourceMap f (imagePoint c)) q ⟶
          localSource f (imagePoint c) => m p) hpb.isoPullback_inv_fst
  exact hj.trans hp

private theorem exists_localExceptional_preimage_of_isClosed
    (x : localSource f (imagePoint c)) (hx : IsClosed ({x} : Set _)) :
    ∃ y : C, localExceptional c f i a w y = x := by
  let : IsProper (localSourceMap f (imagePoint c)) := by
    change IsProper (pullback.snd f (Z.fromSpecStalk (imagePoint c)))
    infer_instance
  exact exists_localExceptional_preimage_of_closedFibre c f i a w hker x
    (@Scheme.image_closedPoint_eq_closedPoint (pointLocalRing c)
      (CommRingCat.commRing (pointLocalRing c))
      (Z.toLocallyRingedSpace.isLocalRing (imagePoint c))
      (localSource f (imagePoint c)) (localSourceMap f (imagePoint c)) inferInstance x hx)

/-- A connected original closed fibre makes the actual proper local-spectrum source
connected. No regularity or hypothesis about its global sections is needed. -/
theorem localSource_connectedSpace [ConnectedSpace C] :
    ConnectedSpace (localSource f (imagePoint c)) := by
  let W := localSource f (imagePoint c)
  let j : C ⟶ W := localExceptional c f i a w
  let : IsProper (localSourceMap f (imagePoint c)) := by
    change IsProper (pullback.snd f (Z.fromSpecStalk (imagePoint c)))
    infer_instance
  let : CompactSpace W :=
    QuasiCompact.compactSpace_of_compactSpace (localSourceMap f (imagePoint c))
  have hdetect (s : Set W) (hs : IsClosed s) (he : j ⁻¹' s = ∅) : s = ∅ := by
    by_contra hsne
    obtain ⟨x, hxs, hx⟩ := hs.exists_closed_singleton (Set.nonempty_iff_ne_empty.mpr hsne)
    obtain ⟨y, hy⟩ := exists_localExceptional_preimage_of_isClosed c f i a w hker x hx
    have hymem : y ∈ j ⁻¹' s := by
      change j y ∈ s
      exact (show j y = x from hy).symm ▸ hxs
    have : y ∈ (∅ : Set C) := he ▸ hymem
    exact this
  apply connectedSpace_iff_clopen.mpr
  refine ⟨⟨j (Classical.choice (inferInstance : Nonempty C))⟩, ?_⟩
  intro s hs
  have hpre : IsClopen (j ⁻¹' s) := hs.preimage j.continuous
  rcases isClopen_iff.mp hpre with he | he
  · exact Or.inl (hdetect s hs.isClosed he)
  · right
    have hcomp : j ⁻¹' sᶜ = ∅ := by
      rw [Set.preimage_compl, he, Set.compl_univ]
    have hempty : sᶜ = ∅ := hdetect sᶜ hs.isOpen.isClosed_compl hcomp
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    have : x ∈ sᶜ := hx
    rw [hempty] at this
    exact this

variable [IsLocallyNoetherian Z]
  (hI : IsLocallyRankOne X (Hom.idealModule i)) (hC : RegularStalks C)

include hI hC

/-- A regular original Cartier closed fibre makes the actual local-spectrum source regular.
The original structural coefficient map is not assumed bijective here. -/
theorem localSource_regularStalks : RegularStalks (localSource f (imagePoint c)) := by
  let j := localExceptional c f i a w
  let : IsClosedImmersion j := localExceptional_isClosedImmersion c f i a w hker
  let : IsProper (localSourceMap f (imagePoint c)) := by
    change IsProper (pullback.snd f (Z.fromSpecStalk (imagePoint c)))
    infer_instance
  let : IsNoetherianRing (Z.presheaf.stalk (imagePoint c)) := inferInstance
  let : IsLocallyNoetherian (Spec (Z.presheaf.stalk (imagePoint c))) := inferInstance
  let : IsLocallyNoetherian (localSource f (imagePoint c)) :=
    LocallyOfFiniteType.isLocallyNoetherian (localSourceMap f (imagePoint c))
  refine @Scheme.regularStalks_of_regular_closedFibre (pointLocalRing c)
    (CommRingCat.commRing (pointLocalRing c))
    (Z.toLocallyRingedSpace.isLocalRing (imagePoint c))
    (localSource f (imagePoint c)) (localSourceMap f (imagePoint c)) inferInstance
    (fun x hx => ?_)
  obtain ⟨y, hy⟩ := exists_localExceptional_preimage_of_closedFibre c f i a w hker x hx
  have hyreg := j.isRegularLocalRing_stalk_image_of_cartier
    (localExceptional_locallyRankOne c f i a w hI) hC y
  exact hy ▸ hyreg

/-- The actual local source has normal domain stalks, by regular-local normality. -/
theorem localSource_normalStalks : NormalStalks (localSource f (imagePoint c)) := by
  intro x
  let : IsRegularLocalRing ((localSource f (imagePoint c)).presheaf.stalk x) :=
    localSource_regularStalks c f i a w hker hI hC x
  exact ⟨IsRegularLocalRing.isDomain_of_regularLocal _,
    IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _⟩

/-- A connected regular original Cartier fibre makes the actual local source integral. -/
theorem localSource_isIntegral [ConnectedSpace C] :
    IsIntegral (localSource f (imagePoint c)) := by
  let : ConnectedSpace (localSource f (imagePoint c)) :=
    localSource_connectedSpace c f i a w hker
  let : IsProper (localSourceMap f (imagePoint c)) := by
    change IsProper (pullback.snd f (Z.fromSpecStalk (imagePoint c)))
    infer_instance
  let : IsNoetherianRing (Z.presheaf.stalk (imagePoint c)) := inferInstance
  let : IsLocallyNoetherian (Spec (Z.presheaf.stalk (imagePoint c))) := inferInstance
  let : IsLocallyNoetherian (localSource f (imagePoint c)) :=
    LocallyOfFiniteType.isLocallyNoetherian (localSourceMap f (imagePoint c))
  exact Scheme.isIntegral_of_connected_normalStalks_actual (localSource f (imagePoint c))
    (localSource_normalStalks c f i a w hker hI hC)

/-- Bijectivity of the original structural map identifies the original target stalk with
the actual global sections of the normal integral local source. This conclusion retains
that bijectivity premise explicitly and makes no regularity or dimension claim about the stalk. -/
theorem pointLocalRing_isDomain_and_isIntegrallyClosed_of_localStructureHom_bijective
    [ConnectedSpace C]
    (hbij : Function.Bijective (localStructureHom f (imagePoint c))) :
    IsDomain (pointLocalRing c) ∧ IsIntegrallyClosed (pointLocalRing c) := by
  let W := localSource f (imagePoint c)
  let : IsIntegral W := localSource_isIntegral c f i a w hker hI hC
  have hN : NormalStalks W := localSource_normalStalks c f i a w hker hI hC
  let : IsIntegrallyClosed Γ(W, ⊤) :=
    NormalStalks.isIntegrallyClosed_globalSections W hN
  let e : pointLocalRing c ≃+* Γ(W, ⊤) :=
    RingEquiv.ofBijective (localStructureHom f (imagePoint c)) hbij
  exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩

end AlgebraicGeometry.Scheme.Surfaces.Contraction
