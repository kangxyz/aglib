/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.NormalizedPointBlowupChain.OrdinaryStages
public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Scheme
public import Aglib.AlgebraicGeometry.Stalk.Restriction
public import Aglib.AlgebraicGeometry.Surfaces.NormalPoints
public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Scheme.LocalRegularity

/-!
# Singular ancestors on the original supported normalized chain

The selected points are the images of ONE original singular terminal point
under the native suffix arrows. Actual ordinary normality makes the literal
normalizations isomorphisms. Original regular points stay regular under each
step, so native reverse induction makes every selected ancestor singular.
Closedness, dimension two, Nagata and genuine rationality are then derived.
No future singularity, canonical generation or Gorenstein premise is supplied.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Blowup.NormalizedPointBlowupChain

private theorem ordinaryPoint_regular_at_regular_image
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hX : NormalStalks X) (hdX : topologicalKrullDim X ≤ 2)
    (x : X) (hx : IsClosed ({x} : Set X)) (hxη : x ≠ genericPoint X)
    (y : (blowupDatum (X.fromSpecResidueField x).ker).Y)
    (hyreg : IsRegularLocalRing (X.presheaf.stalk
      ((blowupDatum (X.fromSpecResidueField x).ker).map y))) :
    IsRegularLocalRing ((blowupDatum (X.fromSpecResidueField x).ker).Y.presheaf.stalk y) := by
  let B := blowupDatum (X.fromSpecResidueField x).ker
  let : IsRegularLocalRing (X.presheaf.stalk (B.map y)) := hyreg
  by_cases hy : B.map y = x
  · by_cases hd : ringKrullDim (X.presheaf.stalk x) = 2
    · let : IsRegularLocalRing (X.presheaf.stalk x) := hy ▸ hyreg
      exact RegularPoint.regularLocalRing_pointBlowup_over_regularPoint X x hx hd y hy
    · let : IsIntegral B.Y := pointBlowup_isIntegral X x hx hxη
      let : IsProper B.map := B.isProper_of_isLocallyNoetherian
      let : IsDominant B.map := pointBlowup_isDominant X x hx hxη
      have hff : IsIso (CommRingCat.ofHom (functionFieldMap B.map)) :=
        B.functionFieldMap_isIso (genericPoint_not_mem_pointCentre x hx hxη)
      have hle : ringKrullDim (X.presheaf.stalk x) ≤ 2 :=
        (le_iSup (fun z : X => ringKrullDim (X.presheaf.stalk z)) x).trans
          ((topologicalKrullDim_eq_iSup_stalk X).symm.le.trans hdX)
      have hlt : ringKrullDim (X.presheaf.stalk x) < 2 := lt_of_le_of_ne hle hd
      have hsmall : ringKrullDim (X.presheaf.stalk x) ≤ 1 :=
        (ENat.WithBot.lt_add_one_iff (m := 1)).mp (by
          convert hlt using 1
          norm_num)
      have hcoheight : Order.coheight x ≤ 1 := by
        rw [ringKrullDim_stalk_eq_coheight] at hsmall
        exact WithBot.coe_le_coe.mp hsmall
      obtain ⟨U, hxU, hU⟩ :=
        exists_isIso_restrict_of_isProper_birational_at_coheight_le_one B.map hff hX x hcoheight
      let : IsIso (B.map ∣_ U) := hU
      let : IsIso (B.map.stalkMap y) :=
        Hom.isIso_stalkMap_of_isIso_morphismRestrict B.map U y (hy.symm ▸ hxU)
      exact IsRegularLocalRing.of_ringEquiv
        (asIso (B.map.stalkMap y)).commRingCatIsoToRingEquiv
  · let U := LocalModification.pointComplement x hx
    let : IsClosedImmersion (X.fromSpecResidueField x) :=
      isClosed_singleton_iff_isClosedImmersion.mp hx
    have hdisjoint : Disjoint (U : Set X)
        ((X.fromSpecResidueField x).ker.support : Set X) := by
      rw [Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField, hx.closure_eq]
      exact Set.disjoint_left.mpr fun z hz hz' => hz hz'
    let : IsIso (B.map ∣_ U) := B.restrict_isIso_of_disjoint U hdisjoint
    let : IsIso (B.map.stalkMap y) :=
      Hom.isIso_stalkMap_of_isIso_morphismRestrict B.map U y hy
    exact IsRegularLocalRing.of_ringEquiv
      (asIso (B.map.stalkMap y)).commRingCatIsoToRingEquiv

/-- Every original ancestor of a singular terminal point over the supported
point is genuinely singular, closed, dimension two, Nagata and rational.
The trajectory is the actual suffix image, not a supplied compatible list. -/
theorem singular_ancestor_properties_of_supported_rational_chain
    {Z X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {f : Z ⟶ X} (c : NormalizedPointBlowupChain f) [IsProper f]
    (x : X) (hx : IsClosed ({x} : Set X)) (hxη : x ≠ genericPoint X)
    (hU : IsIso (f ∣_ LocalModification.pointComplement x hx))
    (hX : NormalStalks X) (hdX : topologicalKrullDim X ≤ 2)
    (hS : IsNagataRing.{u, 0} (X.presheaf.stalk x))
    (hdS : ringKrullDim (X.presheaf.stalk x) = 2)
    (hRat : RationalSingularities.NormalModificationH1Vanishing (X.presheaf.stalk x))
    (z : Z) (hfz : f z = x) (hz : ¬ IsRegularLocalRing (Z.presheaf.stalk z)) :
    ∀ i : Fin (c.length + 1),
      letI : IsIntegral (c.stage i) := (c.«prefix» i).isIntegral inferInstance
      let yi := c.fromTop i z
      ¬ IsRegularLocalRing ((c.stage i).presheaf.stalk yi) ∧
        IsClosed ({yi} : Set (c.stage i)) ∧
        ringKrullDim ((c.stage i).presheaf.stalk yi) = 2 ∧
        yi ≠ genericPoint (c.stage i) ∧ c.toBase i yi = x ∧
        IsNagataRing.{u, 0} ((c.stage i).presheaf.stalk yi) ∧
        RationalSingularities.NormalModificationH1Vanishing ((c.stage i).presheaf.stalk yi) := by
  have hstep (j : Fin c.length) (q : c.stage j.succ)
      (hq : IsRegularLocalRing ((c.stage j.castSucc).presheaf.stalk (c.step j q))) :
      IsRegularLocalRing ((c.stage j.succ).presheaf.stalk q) := by
    let Xi := c.stage j.castSucc
    let B := c.ordinaryDatum j
    let ν := c.normalizationMap j
    obtain ⟨hXi, _, _, _, _, _, _, hNoeth, _, _, _, _, _, _, _, _, _, _, hdXi⟩ :=
      c.localStage_geometry x hx hxη hU hdX hS j.castSucc
    let : IsIntegral Xi := hXi
    let : IsLocallyNoetherian Xi := hNoeth
    have hXiN : NormalStalks Xi := (c.«prefix» j.castSucc).normalStalks hX
    let : IsIso ν :=
      (c.ordinaryDatum_normalStalks_and_normalizationMap_isIso
        x hx hxη hU hX hdX hS hdS hRat j).2
    have hpoint : B.map (ν q) = c.step j q := by
      change (c.normalizationMap j ≫ (c.ordinaryDatum j).map) q = c.step j q
      rw [c.normalizationMap_comp j]
    have hreg : IsRegularLocalRing (Xi.presheaf.stalk (B.map (ν q))) := by
      rw [hpoint]
      exact hq
    let : IsRegularLocalRing (B.Y.presheaf.stalk (ν q)) :=
      ordinaryPoint_regular_at_regular_image Xi hXiN hdXi (c.center j)
        (c.center_isClosed j) (c.center_ne_genericPoint j) (ν q) hreg
    exact IsRegularLocalRing.of_ringEquiv
      (asIso (ν.stalkMap q)).commRingCatIsoToRingEquiv
  have hsing (i : Fin (c.length + 1)) :
      ¬ IsRegularLocalRing ((c.stage i).presheaf.stalk (c.fromTop i z)) := by
    induction i using Fin.reverseInduction with
    | last =>
      intro hreg
      let : IsIso (c.fromTop (Fin.last c.length)) := by
        rw [c.fromTop_last]
        infer_instance
      let : IsRegularLocalRing ((c.stage (Fin.last c.length)).presheaf.stalk
          (c.fromTop (Fin.last c.length) z)) := hreg
      exact hz (IsRegularLocalRing.of_ringEquiv
        (asIso ((c.fromTop (Fin.last c.length)).stalkMap z)).commRingCatIsoToRingEquiv)
    | cast j ih =>
      intro hreg
      apply ih
      apply hstep j (c.fromTop j.succ z)
      have hpoint : c.step j (c.fromTop j.succ z) = c.fromTop j.castSucc z := by
        change (c.fromTop j.succ ≫ c.step j) z = c.fromTop j.castSucc z
        rw [c.fromTop_step j]
      exact hpoint.symm ▸ hreg
  intro i
  let Xi := c.stage i
  let fi := c.toBase i
  let yi := c.fromTop i z
  obtain ⟨hXi, _, hfiD, _, _, hfiP, _, hNoeth, _, _, _, _, _, hff, _, _, _, _, hdXi⟩ :=
    c.localStage_geometry x hx hxη hU hdX hS i
  let : IsIntegral Xi := hXi
  let : IsDominant fi := hfiD
  let : IsProper fi := hfiP
  let : IsLocallyNoetherian Xi := hNoeth
  have hXiN : NormalStalks Xi := (c.«prefix» i).normalStalks hX
  have hsingi : ¬ IsRegularLocalRing (Xi.presheaf.stalk yi) := hsing i
  have hclosed : IsClosed ({yi} : Set Xi) :=
    isClosed_singleton_of_singular_of_normal_dimension_le_two Xi hXiN hdXi yi hsingi
  have hdim : ringKrullDim (Xi.presheaf.stalk yi) = 2 :=
    stalk_dimension_eq_two_of_singular_of_normal_dimension_le_two Xi hXiN hdXi yi hsingi
  have hne : yi ≠ genericPoint Xi := by
    intro he
    apply hsingi
    rw [he]
    change IsRegularLocalRing Xi.functionField
    infer_instance
  have hto : fi yi = x := by
    change (c.fromTop i ≫ c.toBase i) z = x
    rw [c.fromTop_toBase i]
    exact hfz
  obtain ⟨hNagata, hRati⟩ :=
    RationalSingularities.stalk_isNagata_and_normalModificationH1Vanishing_of_target_stalk
      fi hXiN hff x hS hdS hRat yi hclosed hne hto
  exact ⟨hsingi, hclosed, hdim, hne, hto, hNagata, hRati⟩

end AlgebraicGeometry.Scheme.Blowup.NormalizedPointBlowupChain
