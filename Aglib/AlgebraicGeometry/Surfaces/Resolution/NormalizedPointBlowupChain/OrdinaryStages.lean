/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.NormalizedPointBlowupChain.LocalStages
public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.ModelLocalization
public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.Blowup.PointNormality
public import Aglib.AlgebraicGeometry.Surfaces.Birational.IsomorphismLocus
public import Aglib.AlgebraicGeometry.FunctionField.Normalization

/-!
# Ordinary normal stages of the original supported normalized chain

The actual ordinary blowup at each prescribed centre is normal. Over the
original point this follows from genuine stalk rationality in dimension two;
low-dimensional centres and centres outside the support give actual ordinary
blowdown isomorphisms. Hence the LITERAL normalization arrow at every step
is an isomorphism. No ordinary normality or off-support rationality is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Blowup.NormalizedPointBlowupChain

private theorem pointBlowup_isIso_of_isIso_neighborhood
    (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X))
    (U : X.Opens) (hxU : x ∈ U)
    (hU : IsIso ((blowupDatum (X.fromSpecResidueField x).ker).map ∣_ U)) :
    IsIso (blowupDatum (X.fromSpecResidueField x).ker).map := by
  let B := blowupDatum (X.fromSpecResidueField x).ker
  let C := LocalModification.pointComplement x hx
  let : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have hdisjoint : Disjoint (C : Set X)
      ((X.fromSpecResidueField x).ker.support : Set X) := by
    rw [Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField, hx.closure_eq]
    apply Set.disjoint_left.mpr
    intro y hy hyx
    exact (show y ∉ ({x} : Set X) from hy) hyx
  have haway : IsIso (B.map ∣_ C) := B.restrict_isIso_of_disjoint C hdisjoint
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme)
  intro y
  by_cases hy : y = x
  · subst y
    exact ⟨U, hxU, hU⟩
  · exact ⟨C, hy, haway⟩

private theorem normalStalks_of_original_iso
    {Y X : Scheme.{u}} (g : Y ⟶ X) [IsIso g] (hX : NormalStalks X) :
    NormalStalks Y := by
  intro y
  let : IsDomain (X.presheaf.stalk (g y)) := (hX (g y)).1
  let : IsIntegrallyClosed (X.presheaf.stalk (g y)) := (hX (g y)).2
  let e := (asIso (g.stalkMap y)).commRingCatIsoToRingEquiv
  exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩

/-- The single original ordinary-stage classification retains normality, the
literal normalization iso, and its proved blowdown isomorphism off support
or at a low-dimensional centre. No rationality at an arbitrary centre is used. -/
theorem ordinaryDatum_classification
    {Z X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {f : Z ⟶ X} (c : NormalizedPointBlowupChain f) [IsProper f]
    (x : X) (hx : IsClosed ({x} : Set X)) (hxη : x ≠ genericPoint X)
    (hU : IsIso (f ∣_ LocalModification.pointComplement x hx))
    (hX : NormalStalks X) (hdX : topologicalKrullDim X ≤ 2)
    (hS : IsNagataRing.{u, 0} (X.presheaf.stalk x))
    (hdS : ringKrullDim (X.presheaf.stalk x) = 2)
    (hRat : RationalSingularities.NormalModificationH1Vanishing (X.presheaf.stalk x))
    (j : Fin c.length) :
    (NormalStalks (c.ordinaryDatum j).Y ∧ IsIso (c.normalizationMap j)) ∧
      ((c.toBase j.castSucc (c.center j) ≠ x ∨
          ringKrullDim ((c.stage j.castSucc).presheaf.stalk (c.center j)) ≤ 1) →
        IsIso (c.ordinaryDatum j).map) := by
  let Xi := c.stage j.castSucc
  let fi := c.toBase j.castSucc
  let z := c.center j
  let B := c.ordinaryDatum j
  obtain ⟨hXi, _, hfiD, _, _, hfiP, _, hNoeth, _, hfiU,
    _, _, _, hff, _, _, _, _, hdXi⟩ :=
    c.localStage_geometry x hx hxη hU hdX hS j.castSucc
  let : IsIntegral Xi := hXi
  let : IsDominant fi := hfiD
  let : IsProper fi := hfiP
  let : IsLocallyNoetherian Xi := hNoeth
  have hXiN : NormalStalks Xi := (c.«prefix» j.castSucc).normalStalks hX
  have hz : IsClosed ({z} : Set Xi) := c.center_isClosed j
  have hzη : z ≠ genericPoint Xi := c.center_ne_genericPoint j
  let : IsIntegral B.Y := pointBlowup_isIntegral Xi z hz hzη
  let : IsProper B.map := B.isProper_of_isLocallyNoetherian
  let : IsDominant B.map := pointBlowup_isDominant Xi z hz hzη
  have hBff : IsIso (CommRingCat.ofHom (functionFieldMap B.map)) :=
    B.functionFieldMap_isIso (genericPoint_not_mem_pointCentre z hz hzη)
  have hB : NormalStalks B.Y ∧
      ((fi z ≠ x ∨ ringKrullDim (Xi.presheaf.stalk z) ≤ 1) → IsIso B.map) := by
    by_cases hover : fi z = x
    · by_cases hd : ringKrullDim (Xi.presheaf.stalk z) = 2
      · obtain ⟨hNagata, hRatz⟩ :=
          RationalSingularities.stalk_isNagata_and_normalModificationH1Vanishing_of_target_stalk
            fi hXiN hff x hS hdS hRat z hz hzη hover
        refine ⟨RationalSingularities.normalStalks_pointBlowup_of_rational_stalk
          Xi hXiN z hz hNagata hd hRatz, ?_⟩
        intro hguard
        rcases hguard with hoff | hsmall
        · exact False.elim (hoff hover)
        · rw [hd] at hsmall
          norm_num at hsmall
      · have hle : ringKrullDim (Xi.presheaf.stalk z) ≤ 2 :=
          (le_iSup (fun y : Xi => ringKrullDim (Xi.presheaf.stalk y)) z).trans
            ((topologicalKrullDim_eq_iSup_stalk Xi).symm.le.trans hdXi)
        have hlt : ringKrullDim (Xi.presheaf.stalk z) < 2 := lt_of_le_of_ne hle hd
        have hsmall : ringKrullDim (Xi.presheaf.stalk z) ≤ 1 :=
          (ENat.WithBot.lt_add_one_iff (m := 1)).mp (by
            convert hlt using 1
            norm_num)
        have hcoheight : Order.coheight z ≤ 1 := by
          rw [ringKrullDim_stalk_eq_coheight] at hsmall
          exact WithBot.coe_le_coe.mp hsmall
        obtain ⟨W, hzW, hBW⟩ :=
          exists_isIso_restrict_of_isProper_birational_at_coheight_le_one
            B.map hBff hXiN z hcoheight
        let : IsIso B.map := pointBlowup_isIso_of_isIso_neighborhood Xi z hz W hzW hBW
        exact ⟨normalStalks_of_original_iso B.map hXiN, fun _ => inferInstance⟩
    · let U := LocalModification.pointComplement x hx
      let W := fi ⁻¹ᵁ U
      let δ := c.step j
      let ν := c.normalizationMap j
      let : IsIntegral (c.stage j.succ) := (c.«prefix» j.succ).isIntegral inferInstance
      let : IsDominant (B.Y.fromSpecStalk (genericPoint B.Y)).fromNormalization :=
        genericNormalization_isDominant B.Y
      let : IsDominant ν := by
        dsimp only [ν, normalizationMap]
        infer_instance
      let : IsIso (fi ∣_ U) := hfiU
      have hnext : IsIso (c.toBase j.succ ∣_ U) :=
        c.isIso_toBase_restrict U ⟨⟨genericPoint X, hxη.symm⟩⟩ hU j.succ
      have hcomp : IsIso ((δ ≫ fi) ∣_ U) := by
        rw [show δ ≫ fi = c.toBase j.succ from c.step_toBase j]
        exact hnext
      rw [morphismRestrict_comp] at hcomp
      let : IsIso ((δ ∣_ W) ≫ (fi ∣_ U)) := hcomp
      let : IsIso (δ ∣_ W) := IsIso.of_isIso_comp_right (δ ∣_ W) (fi ∣_ U)
      have hzW : z ∈ W := hover
      let V := δ ⁻¹ᵁ W
      let w : W.toScheme := ⟨z, hzW⟩
      let v : V.toScheme := inv (δ ∣_ W) w
      have hVne : (V : Set (c.stage j.succ)).Nonempty := ⟨v.1, v.2⟩
      let : IsDominant V.ι := Opens.isDominant_ι (V.isOpen.dense hVne)
      let s : W.toScheme ⟶ B.Y := inv (δ ∣_ W) ≫ V.ι ≫ ν
      let : IsDominant s := by dsimp only [s]; infer_instance
      have hs : s ≫ B.map = W.ι := by
        change (inv (δ ∣_ W) ≫ V.ι ≫ ν) ≫ B.map = W.ι
        calc
          (inv (δ ∣_ W) ≫ V.ι ≫ ν) ≫ B.map = inv (δ ∣_ W) ≫ V.ι ≫ δ := by
            rw [Category.assoc, Category.assoc, c.normalizationMap_comp j]
          _ = inv (δ ∣_ W) ≫ (δ ∣_ W) ≫ W.ι :=
            congrArg (fun k => inv (δ ∣_ W) ≫ k) (morphismRestrict_ι δ W).symm
          _ = W.ι := IsIso.inv_hom_id_assoc (δ ∣_ W) W.ι
      have hBW : IsIso (B.map ∣_ W) := isIso_restrict_of_dominant_section B.map W s hs
      let : IsIso B.map := pointBlowup_isIso_of_isIso_neighborhood Xi z hz W hzW hBW
      exact ⟨normalStalks_of_original_iso B.map hXiN, fun _ => inferInstance⟩
  refine ⟨⟨hB.1, ?_⟩, hB.2⟩
  let (y : B.Y) : IsIntegrallyClosed (B.Y.presheaf.stalk y) := (hB.1 y).2
  dsimp only [normalizationMap]
  infer_instance

/-- Every actual ordinary post-blowup scheme in the supported chain is normal,
and its original generic-normalization arrow is an isomorphism. Rationality
is required only at the ONE original target stalk, not away from that point. -/
theorem ordinaryDatum_normalStalks_and_normalizationMap_isIso
    {Z X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {f : Z ⟶ X} (c : NormalizedPointBlowupChain f) [IsProper f]
    (x : X) (hx : IsClosed ({x} : Set X)) (hxη : x ≠ genericPoint X)
    (hU : IsIso (f ∣_ LocalModification.pointComplement x hx))
    (hX : NormalStalks X) (hdX : topologicalKrullDim X ≤ 2)
    (hS : IsNagataRing.{u, 0} (X.presheaf.stalk x))
    (hdS : ringKrullDim (X.presheaf.stalk x) = 2)
    (hRat : RationalSingularities.NormalModificationH1Vanishing (X.presheaf.stalk x))
    (j : Fin c.length) :
    NormalStalks (c.ordinaryDatum j).Y ∧ IsIso (c.normalizationMap j) := by
  exact (c.ordinaryDatum_classification x hx hxη hU hX hdX hS hdS hRat j).1

end AlgebraicGeometry.Scheme.Blowup.NormalizedPointBlowupChain
