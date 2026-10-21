/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Regularity
public import Aglib.AlgebraicGeometry.Stalk.FlatBaseChange

/-!
# Actual point blowups of regular schemes

The actual centre of a closed point pulls back to the maximal-ideal centre
on its original local spectrum. The flat blowup comparison identifies the
local blowup with the literal pullback. Its projection retains isomorphisms
on actual stalks, so the regular-local point theorem gives regularity over
the centre. The existing complement comparison gives regularity elsewhere.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

/-- Pulling back the original closed-point centre to the actual local spectrum
gives the original maximal-ideal centre, through the actual residue quotient. -/
theorem pointCentre_comap_fromSpecStalk (X : Scheme.{u}) (x : X)
    (hx : IsClosed ({x} : Set X)) :
    (X.fromSpecResidueField x).ker.comap (X.fromSpecStalk x) =
      affineCenter (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x)) := by
  let : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have H : IsPullback (Spec.map (X.residue x)) (𝟙 (Spec (X.residueField x)))
      (X.fromSpecStalk x) (X.fromSpecResidueField x) :=
    IsPullback.of_vert_isIso_mono ⟨by
      simp only [Scheme.fromSpecResidueField, Category.id_comp]⟩
  calc
    _ = (pullback.fst (X.fromSpecStalk x) (X.fromSpecResidueField x)).ker :=
      (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion
        (X.fromSpecResidueField x) (X.fromSpecStalk x)).symm
    _ = (Spec.map (X.residue x)).ker := by
      simpa only [Scheme.Hom.ker_comp_of_isIso] using
        congrArg Scheme.Hom.ker H.isoPullback_hom_fst
    _ = _ := rfl

/-- The original canonical base-change map from the local-ring blowup to the
actual blowup of the original closed point. -/
def stalkBlowupComparison (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X)) :
    (blowupDatum (affineCenter (X.presheaf.stalk x)
      (maximalIdeal (X.presheaf.stalk x)))).Y ⟶
        (blowupDatum (X.fromSpecResidueField x).ker).Y :=
  BaseChange.map (X.fromSpecStalk x) (pointCentre_comap_fromSpecStalk X x hx)
    (blowupDatum (X.fromSpecResidueField x).ker)
    (blowupDatum (affineCenter (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))))

/-- The canonical comparison square is the actual flat blowup base-change square. -/
theorem stalkBlowupComparison_isPullback (X : Scheme.{u}) (x : X)
    (hx : IsClosed ({x} : Set X)) :
    IsPullback (stalkBlowupComparison X x hx)
      (blowupDatum (affineCenter (X.presheaf.stalk x)
        (maximalIdeal (X.presheaf.stalk x)))).map
      (blowupDatum (X.fromSpecResidueField x).ker).map (X.fromSpecStalk x) :=
  BaseChange.isPullback_of_flat (X.fromSpecStalk x) (Scheme.fromSpecStalk_flat X x)
    (pointCentre_comap_fromSpecStalk X x hx) _ _

/-- The local-ring blowup is isomorphic to the literal pullback of the actual
point blowup, using its canonical flat-base-change comparison. -/
def stalkBlowupIso (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X)) :
    (blowupDatum (affineCenter (X.presheaf.stalk x)
      (maximalIdeal (X.presheaf.stalk x)))).Y ≅
        pullback (blowupDatum (X.fromSpecResidueField x).ker).map (X.fromSpecStalk x) :=
  (stalkBlowupComparison_isPullback X x hx).isoPullback

/-- The forward isomorphism retains the actual canonical map to the point blowup. -/
@[reassoc (attr := simp)]
theorem stalkBlowupIso_hom_fst (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X)) :
    (stalkBlowupIso X x hx).hom ≫
        pullback.fst (blowupDatum (X.fromSpecResidueField x).ker).map (X.fromSpecStalk x) =
      stalkBlowupComparison X x hx :=
  (stalkBlowupComparison_isPullback X x hx).isoPullback_hom_fst

/-- The other projection is the original blowdown over the original stalk spectrum. -/
@[reassoc (attr := simp)]
theorem stalkBlowupIso_hom_snd (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X)) :
    (stalkBlowupIso X x hx).hom ≫
        pullback.snd (blowupDatum (X.fromSpecResidueField x).ker).map (X.fromSpecStalk x) =
      (blowupDatum (affineCenter (X.presheaf.stalk x)
        (maximalIdeal (X.presheaf.stalk x)))).map :=
  (stalkBlowupComparison_isPullback X x hx).isoPullback_hom_snd

/-- Every actual stalk map of the literal base-change projection is an isomorphism. -/
theorem stalkBlowupProjection_isIso_stalkMap (X : Scheme.{u}) (x : X)
    (p : (pullback (blowupDatum (X.fromSpecResidueField x).ker).map
      (X.fromSpecStalk x) : Scheme.{u})) :
    IsIso ((pullback.fst (blowupDatum (X.fromSpecResidueField x).ker).map
      (X.fromSpecStalk x)).stalkMap p) := by
  let : Flat (X.fromSpecStalk x) := Scheme.fromSpecStalk_flat X x
  exact Scheme.Hom.isIso_stalkMap_of_flat_of_surjectiveOnStalks _ p

/-- Blowing up an original closed point with two-dimensional regular local ring
preserves regularity of all actual stalks of the original regular scheme. -/
theorem regularStalks_pointBlowup (X : Scheme.{u})
    (hX : Scheme.RegularStalks X) (x : X) (hx : IsClosed ({x} : Set X))
    (hd : ringKrullDim (X.presheaf.stalk x) = 2) :
    Scheme.RegularStalks (blowupDatum (X.fromSpecResidueField x).ker).Y := by
  let B := blowupDatum (X.fromSpecResidueField x).ker
  let R := X.presheaf.stalk x
  let : IsRegularLocalRing R := hX x
  let : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have hlocal : Scheme.RegularStalks (pullback B.map (X.fromSpecStalk x)) :=
    (regularStalks R hd).of_isOpenImmersion (stalkBlowupIso X x hx).inv
  intro z
  by_cases hz : B.map z = x
  · have hbase : B.map z ∈ Set.range (X.fromSpecStalk x) := by
      rw [hz]
      exact ⟨closedPoint R, Scheme.fromSpecStalk_closedPoint⟩
    have hlift : z ∈ Set.range (pullback.fst B.map (X.fromSpecStalk x)) := by
      rw [Scheme.Pullback.range_fst]
      exact hbase
    obtain ⟨p, rfl⟩ := hlift
    let : IsRegularLocalRing ((pullback B.map (X.fromSpecStalk x)).presheaf.stalk p) := hlocal p
    let : IsIso ((pullback.fst B.map (X.fromSpecStalk x)).stalkMap p) :=
      stalkBlowupProjection_isIso_stalkMap X x p
    exact IsRegularLocalRing.of_ringEquiv
      (asIso ((pullback.fst B.map (X.fromSpecStalk x)).stalkMap p)).commRingCatIsoToRingEquiv.symm
  · have haway : B.map z ∉ Set.range (X.fromSpecResidueField x) := by
      rw [Scheme.range_fromSpecResidueField]
      exact hz
    exact blowup_regular_away (X.fromSpecResidueField x) B (fun y _ => hX y) z haway

end AlgebraicGeometry.Scheme.Blowup.RegularPoint
