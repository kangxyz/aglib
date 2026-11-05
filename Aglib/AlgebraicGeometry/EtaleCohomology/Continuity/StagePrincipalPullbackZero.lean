/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.FinitePrincipalRefinement
public import Aglib.AlgebraicGeometry.Spec.PrincipalClosedComplement
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.OriginalClassZeroTransport

/-! # Original stage-open zero on the literal principal pullback

The actual localization stage has exactly the basic open of its original
denominator. Its inverse-image open and the literal pullback of that basic
open are canonically isomorphic over the original family. This comparison
transports the same original class zero, including after an arbitrary
precomposition of the family. No denominator is replaced and no domain or
nonvanishing assumption is needed for this comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open IsLocalization.PrincipalDiagram

namespace AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit

universe u

variable {S : Type u} [CommRing S] (D : Submonoid S) (t : Finset D)
    {Y : Scheme.{u}} (b : Y ⟶ Spec (.of S))

/-- The literal principal pullback has exactly the original stage source-open
image. This follows from the actual localization-away range theorem. -/
theorem principalPullback_range_eq_stageSourceOpen :
    Set.range (pullback.snd (principalSupportOpen S (denominator D t)).ι b) =
      Set.range (stageSourceOpen D b t).ι := by
  rw [Scheme.Opens.range_ι]
  change Set.range (pullback.snd (principalSupportOpen S (denominator D t)).ι b) =
    b ⁻¹' (stageBaseOpen D t : Set (Spec (.of S)))
  rw [stageBaseOpen_eq_basicOpen]
  have hr : (principalSupportOpen S (denominator D t)).ι.opensRange =
      principalSupportOpen S (denominator D t) :=
    Scheme.Opens.opensRange_ι (principalSupportOpen S (denominator D t))
  exact (IsOpenImmersion.range_pullbackSnd
    (principalSupportOpen S (denominator D t)).ι b).trans
      (congrArg (fun U : (Spec (.of S)).Opens => (b ⁻¹ᵁ U : Set Y)) hr)

/-- The native open-immersion comparison keeps the original pullback and the
original inverse-image stage open, not a different localization model. -/
def principalStagePullbackIso :
    pullback (principalSupportOpen S (denominator D t)).ι b ≅
      (stageSourceOpen D b t).toScheme :=
  IsOpenImmersion.isoOfRangeEq
    (pullback.snd (principalSupportOpen S (denominator D t)).ι b)
    (stageSourceOpen D b t).ι (principalPullback_range_eq_stageSourceOpen D t b)

@[reassoc (attr := simp)]
theorem principalStagePullbackIso_hom_over :
    (principalStagePullbackIso D t b).hom ≫ (stageSourceOpen D b t).ι =
      pullback.snd (principalSupportOpen S (denominator D t)).ι b :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

end AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

open PrincipalNeighborhoodLimit

universe u eT

attribute [local instance] hasSheafifyLarge HasExt.standard

variable {S : Type u} [CommRing S] (D : Submonoid S) (t : Finset D)
    {Y T : Scheme.{u}} [HasExt.{eT} (AbelianSheaf.{u, u + 1} T)]
    (b : Y ⟶ Spec (.of S)) (h : Y ⟶ T)
    (M : AbelianSheaf.{u, u + 1} T) (q : ℕ) (c : Sheaf.H.{eT} M q)

/-- The actual original stage-open zero gives zero on the literal principal
coefficient pullback used by closed-support induction. -/
theorem principalPullback_zero_of_stageOpen_zero
    (hc : cohomologyPullback.{u, eT, u + 2}
      ((stageSourceOpen D b t).ι ≫ h) M q c = 0) :
    cohomologyPullback.{u, eT, u + 2}
      (pullback.snd (principalSupportOpen S (denominator D t)).ι b ≫ h) M q c = 0 := by
  exact TwoFieldEffacement.original_class_zero_of_map_law
    (principalStagePullbackIso D t b).hom ((stageSourceOpen D b t).ι ≫ h)
    (pullback.snd (principalSupportOpen S (denominator D t)).ι b ≫ h)
    (by rw [← Category.assoc, principalStagePullbackIso_hom_over]) M q c hc

/-- The same original stage zero persists on the literal principal pullback
after any original family precomposition. Both original structural maps and
the original target class remain in the conclusion. -/
theorem principalPullback_precomp_zero_of_stageOpen_zero
    {Z : Scheme.{u}} (v : Z ⟶ Y)
    (hc : cohomologyPullback.{u, eT, u + 2}
      ((stageSourceOpen D b t).ι ≫ h) M q c = 0) :
    cohomologyPullback.{u, eT, u + 2}
      ((pullback.snd (principalSupportOpen S (denominator D t)).ι (v ≫ b) ≫ v) ≫ h)
      M q c = 0 := by
  let j := (principalSupportOpen S (denominator D t)).ι
  let k : pullback j (v ≫ b) ⟶ pullback j b :=
    pullback.lift (pullback.fst j (v ≫ b)) (pullback.snd j (v ≫ b) ≫ v)
      (by simpa only [Category.assoc] using (pullback.condition (f := j) (g := v ≫ b)))
  have hk : k ≫ pullback.snd j b = pullback.snd j (v ≫ b) ≫ v :=
    pullback.lift_snd ..
  exact TwoFieldEffacement.original_class_zero_of_map_law k (pullback.snd j b ≫ h)
    ((pullback.snd j (v ≫ b) ≫ v) ≫ h)
    ((Category.assoc k (pullback.snd j b) h).symm.trans
      (congrArg (fun a : pullback j (v ≫ b) ⟶ Y => a ≫ h) hk)) M q c
    (principalPullback_zero_of_stageOpen_zero D t b h M q c hc)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
