/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.MarkedFractionTargetExtension

/-! # The same marked generic cover on the actual principal target stage

The local cover and its actual principal descent determine the whole generic
reconstruction of that principal-stage cover. The original generic fibre, its
fraction-field arrow and its full marking are preserved. This supplies no
class zero and does not assume a new reconstruction certificate.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open IsLocalization.PrincipalDiagram
open AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

variable (A F : Type u) [CommRing A] [IsDomain A] [Field F]
  [Algebra A F] [IsFractionRing A F] (q : PrimeSpectrum A)
  {X : Scheme.{u}} (p : X ⟶ Spec (.of A))

local notation "L" => Localization.AtPrime q.asIdeal
local notation "l" => Spec.algebraMap A L
local notation "pq" => pullback.snd p l
local notation "γ" =>
  Scheme.fromSpecStalk (Spec (CommRingCat.of L)) (genericPoint (Spec (CommRingCat.of L)))
local notation "eK" => localizedGenericSpectrumIso A F q
local notation "eX" => localizedGenericFiberIso A F q p
local notation "D" => schemeDiagram q.asIdeal.primeCompl p
local notation "π" => baseChangeProjection q.asIdeal.primeCompl L p

/-- The existing generic comparison followed by its original local projection. -/
def fractionLocalTargetMap : pullback p (Spec.algebraMap A F) ⟶ pullback p l :=
  (eX).hom ≫ pullback.fst pq γ

/-- The actual fraction-field arrow into the original principal ring stage. -/
def principalFractionBaseMap (s : Finset q.asIdeal.primeCompl) :
    Spec (.of F) ⟶ Spec (.of (stage q.asIdeal.primeCompl s)) :=
  (eK).hom ≫ γ ≫ Spec.map (CommRingCat.ofHom (projection q.asIdeal.primeCompl L s))

/-- The original generic fibre maps to the same principal target stage. -/
def principalFractionTargetMap (s : Finset q.asIdeal.primeCompl) :
    pullback p (Spec.algebraMap A F) ⟶ ((D).obj (op s)).left :=
  fractionLocalTargetMap A F q p ≫ π (op s)

@[reassoc] theorem principalFractionTargetMap_original (s : Finset q.asIdeal.primeCompl) :
    principalFractionTargetMap A F q p s ≫ ((D).obj (op s)).hom =
      pullback.fst p (Spec.algebraMap A F) := by
  simp only [principalFractionTargetMap, fractionLocalTargetMap, Category.assoc,
    baseChangeProjection_base, localizedGenericFiberIso_hom_fst]

@[reassoc] theorem principalFractionBaseMap_original (s : Finset q.asIdeal.primeCompl) :
    principalFractionBaseMap A F q s ≫ Spec.algebraMap A (stage q.asIdeal.primeCompl s) =
      Spec.algebraMap A F := by
  have hp := baseStructure_fac q.asIdeal.primeCompl L (op s)
  change Spec.map (CommRingCat.ofHom (projection q.asIdeal.primeCompl L s)) ≫
    Spec.algebraMap A (stage q.asIdeal.primeCompl s) = l at hp
  simp only [principalFractionBaseMap, Category.assoc, hp]
  rw [← Category.assoc, localizedGenericSpectrumIso_hom_generic,
    localizedFraction_base_triangle]

@[reassoc] theorem principalFractionTargetMap_field (s : Finset q.asIdeal.primeCompl) :
    principalFractionTargetMap A F q p s ≫
        pullback.fst (Spec.algebraMap A (stage q.asIdeal.primeCompl s)) p =
      pullback.snd p (Spec.algebraMap A F) ≫ principalFractionBaseMap A F q s := by
  have hlocal : fractionLocalTargetMap A F q p ≫ pq =
      pullback.snd p (Spec.algebraMap A F) ≫ (eK).hom ≫ γ := by
    dsimp only [fractionLocalTargetMap]
    rw [Category.assoc, pullback.condition, ← Category.assoc,
      localizedGenericFiberIso_hom_snd]
    exact Category.assoc ..
  have hπ := baseChangeProjection_field q.asIdeal.primeCompl L p s
  have h := congrArg (fun m => fractionLocalTargetMap A F q p ≫ m) hπ
  rw [← Category.assoc (fractionLocalTargetMap A F q p) pq
    (Spec.map (CommRingCat.ofHom (projection q.asIdeal.primeCompl L s))), hlocal] at h
  exact (Category.assoc ..).trans h

/-- The complete principal-stage square is the original fraction fibre square,
not merely a commuting triangle or an isomorphic replacement source. -/
theorem principalFractionTargetMap_isPullback (s : Finset q.asIdeal.primeCompl) :
    IsPullback (principalFractionTargetMap A F q p s)
      (pullback.snd p (Spec.algebraMap A F))
      (pullback.fst (Spec.algebraMap A (stage q.asIdeal.primeCompl s)) p)
      (principalFractionBaseMap A F q s) := by
  have H : IsPullback
      (principalFractionTargetMap A F q p s ≫ ((D).obj (op s)).hom)
      (pullback.snd p (Spec.algebraMap A F)) p
      (principalFractionBaseMap A F q s ≫
        Spec.algebraMap A (stage q.asIdeal.primeCompl s)) := by
    rw [principalFractionTargetMap_original, principalFractionBaseMap_original]
    exact IsPullback.of_hasPullback p _
  exact H.of_right (principalFractionTargetMap_field A F q p s)
    (IsPullback.of_hasPullback (Spec.algebraMap A (stage q.asIdeal.primeCompl s)) p).flip

variable (s : Finset q.asIdeal.primeCompl)
  (G : FiniteEtale (pullback p (Spec.algebraMap A (Localization.AtPrime q.asIdeal))))
  (Gs : FiniteEtale ((schemeDiagram q.asIdeal.primeCompl p).obj (op s)).left)
  (Z : FiniteEtale (pullback p (Spec.algebraMap A F)))
  (es : (baseChange (baseChangeProjection q.asIdeal.primeCompl
    (Localization.AtPrime q.asIdeal) p (op s))).obj Gs ≅ G)
  (r : (baseChange (fractionLocalTargetMap A F q p)).obj G ≅ Z)

/-- Compose only the original descent isomorphism and the original generic
reconstruction, retaining the entire given generic cover. -/
def principalTargetCoverReconstruction :
    (baseChange (principalFractionTargetMap A F q p s)).obj Gs ≅ Z :=
  (baseChangeComp (π (op s)) (fractionLocalTargetMap A F q p)).app Gs ≪≫
    (baseChange (fractionLocalTargetMap A F q p)).mapIso es ≪≫ r

/-- The cover reconstruction lies over the same original generic fibre. -/
@[reassoc] theorem principalTargetCoverReconstruction_over :
    (principalTargetCoverReconstruction A F q p s G Gs Z es r).hom.hom.left ≫ Z.obj.hom =
      ((baseChange (principalFractionTargetMap A F q p s)).obj Gs).obj.hom :=
  Over.w (principalTargetCoverReconstruction A F q p s G Gs Z es r).hom.hom

variable (σ : Spec (.of A) ⟶ X) (hσ : σ ≫ p = 𝟙 _)
  (z : Fiber (fractionSectionPoint A F p σ hσ) Z)

/-- Pull back the full original marked point through the actual reconstruction. -/
def principalTargetCoverMark : Spec (.of F) ⟶
    ((baseChange (principalFractionTargetMap A F q p s)).obj Gs).obj.left :=
  z.left ≫ (principalTargetCoverReconstruction A F q p s G Gs Z es r).inv.hom.left

/-- The transported marking recovers the original cover point, not just its
ambient projection. -/
@[reassoc] theorem principalTargetCoverMark_original :
    principalTargetCoverMark A F q p s G Gs Z es r σ hσ z ≫
        (principalTargetCoverReconstruction A F q p s G Gs Z es r).hom.hom.left = z.left := by
  let i := principalTargetCoverReconstruction A F q p s G Gs Z es r
  have hi := congrArg (fun m => m.hom.left) i.inv_hom_id
  exact (Category.assoc ..).trans
    ((congrArg (fun m => z.left ≫ m) hi).trans (Category.comp_id z.left))

/-- The same marked lift has exactly the original section point as its base. -/
@[reassoc] theorem principalTargetCoverMark_section :
    principalTargetCoverMark A F q p s G Gs Z es r σ hσ z ≫
        ((baseChange (principalFractionTargetMap A F q p s)).obj Gs).obj.hom =
      fractionSectionPoint A F p σ hσ := by
  have h := Over.w (principalTargetCoverReconstruction A F q p s G Gs Z es r).inv.hom
  exact (Category.assoc ..).trans
    ((congrArg (fun m => z.left ≫ m) h).trans (Over.w z))

/-- Its projection on the actual principal-stage cover is a genuine lift of
that same section point through the original stage map. -/
theorem principalTargetCoverMark_stage :
    (principalTargetCoverMark A F q p s G Gs Z es r σ hσ z ≫
        pullback.fst Gs.obj.hom (principalFractionTargetMap A F q p s)) ≫ Gs.obj.hom =
      fractionSectionPoint A F p σ hσ ≫ principalFractionTargetMap A F q p s := by
  have h := congrArg
    (fun m => principalTargetCoverMark A F q p s G Gs Z es r σ hσ z ≫ m)
    (pullback.condition (f := Gs.obj.hom) (g := principalFractionTargetMap A F q p s))
  have hs := congrArg (fun m => m ≫ principalFractionTargetMap A F q p s)
    (principalTargetCoverMark_section A F q p s G Gs Z es r σ hσ z)
  exact (Category.assoc ..).trans
    (h.trans ((Category.assoc ..).symm.trans hs))

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
