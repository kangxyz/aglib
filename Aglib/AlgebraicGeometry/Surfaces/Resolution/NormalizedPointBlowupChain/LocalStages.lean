/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.NormalizedPointBlowupChain.SupportedStages
public import Aglib.AlgebraicGeometry.Stalk.ModelLocalization
public import Aglib.AlgebraicGeometry.FunctionField.LocalSpectrum.BaseChange
public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.AffineBaseCharts
public import Aglib.AlgebraicGeometry.Descent.LocalModification.Dimension

/-!
# Literal target-stalk pullbacks of the original supported prefixes

Each local model is the native pullback of the actual prefix along the
original target stalk spectrum. Properness, support and original field maps
are derived on these same schemes. Nagata of the ONE original target stalk
bounds each local model; the actual supported square then bounds its global
prefix. No later-stalk Nagata, rationality or ordinary normality is supplied.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Blowup.NormalizedPointBlowupChain

/-- The actual supported prefix and its literal target-stalk pullback have
proper original structure maps, the original birational field square, and
derived surface dimensions. No per-stage model or dimension is an input. -/
theorem localStage_geometry
    {Z X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {f : Z ⟶ X} (c : NormalizedPointBlowupChain f) [IsProper f]
    (x : X) (hx : IsClosed ({x} : Set X)) (hxη : x ≠ genericPoint X)
    (hU : IsIso (f ∣_ LocalModification.pointComplement x hx))
    (hdX : topologicalKrullDim X ≤ 2)
    (hS : IsNagataRing.{u, 0} (X.presheaf.stalk x))
    (i : Fin (c.length + 1)) :
    let Xi := c.stage i
    let fi := c.toBase i
    let Pi := pullback fi (X.fromSpecStalk x)
    let ai : Pi ⟶ Xi := pullback.fst fi (X.fromSpecStalk x)
    let pi : Pi ⟶ Spec (X.presheaf.stalk x) := pullback.snd fi (X.fromSpecStalk x)
    ∃ (hXi : IsIntegral Xi) (hPi : IsIntegral Pi)
      (hfiD : IsDominant fi) (haiD : IsDominant ai) (hpiD : IsDominant pi),
      letI := hXi
      letI := hPi
      letI := hfiD
      letI := haiD
      letI := hpiD
      letI := fromSpecStalk_isDominant X x
      IsProper fi ∧ IsProper (c.fromTop i) ∧ IsLocallyNoetherian Xi ∧
        IsProper pi ∧ IsIso (fi ∣_ LocalModification.pointComplement x hx) ∧
        c.fromTop i ≫ fi = f ∧ IsPullback ai pi fi (X.fromSpecStalk x) ∧
        ai ≫ fi = pi ≫ X.fromSpecStalk x ∧
        IsIso (CommRingCat.ofHom (functionFieldMap fi)) ∧
        IsIso (CommRingCat.ofHom (functionFieldMap ai)) ∧
        (functionFieldMap ai).comp (functionFieldMap fi) =
          (functionFieldMap pi).comp (functionFieldMap (X.fromSpecStalk x)) ∧
        IsIso (CommRingCat.ofHom (functionFieldMap pi)) ∧
        topologicalKrullDim Pi ≤ 2 ∧ topologicalKrullDim Xi ≤ 2 := by
  let Xi := c.stage i
  let fi := c.toBase i
  let hXi : IsIntegral Xi := (c.«prefix» i).isIntegral inferInstance
  let : IsIntegral Xi := hXi
  let hfiD : IsDominant fi := (c.«prefix» i).isDominant inferInstance
  let : IsDominant fi := hfiD
  have hp := c.isProper_toBase_and_fromTop i
  let : IsProper fi := hp.1
  have hNoeth : IsLocallyNoetherian Xi := LocallyOfFiniteType.isLocallyNoetherian fi
  have hfiU : IsIso (fi ∣_ LocalModification.pointComplement x hx) :=
    c.isIso_toBase_restrict (LocalModification.pointComplement x hx)
      ⟨⟨genericPoint X, hxη.symm⟩⟩ hU i
  have hff : IsIso (CommRingCat.ofHom (functionFieldMap fi)) :=
    (c.«prefix» i).functionFieldMap_isIso inferInstance
  let S := X.presheaf.stalk x
  let s := X.fromSpecStalk x
  let Pi := pullback fi s
  let ai : Pi ⟶ Xi := pullback.fst fi s
  let pi : Pi ⟶ Spec S := pullback.snd fi s
  have H : IsPullback ai pi fi s := IsPullback.of_hasPullback fi s
  let : Flat s := fromSpecStalk_flat X x
  let : IsDominant s := fromSpecStalk_isDominant X x
  let hPi : IsIntegral Pi := isIntegral_pullback_fromSpecStalk fi x
  let : IsIntegral Pi := hPi
  let haiD : IsDominant ai := isDominant_pullback_fst_fromSpecStalk fi x
  let : IsDominant ai := haiD
  let : Surjective fi :=
    surjective_of_isDominant_of_isClosed_range fi fi.isClosedMap.isClosed_range
  let : Surjective pi := inferInstance
  let hpiD : IsDominant pi := inferInstance
  let : IsDominant pi := hpiD
  let : IsProper pi := inferInstance
  have haff : IsIso (CommRingCat.ofHom (functionFieldMap ai)) :=
    functionFieldMap_isIso_of_flat_preimmersion ai
  have hpsquare := functionFieldMap_square_of_isPullback_fromSpecStalk fi x ai pi H
  have hpff : IsIso (CommRingCat.ofHom (functionFieldMap pi)) :=
    functionFieldMap_isIso_of_isPullback_fromSpecStalk fi x ai pi H hff
  have hdS : ringKrullDim S ≤ 2 := by
    have ht := le_iSup (fun x : X => ringKrullDim (X.presheaf.stalk x)) x
    rw [← topologicalKrullDim_eq_iSup_stalk X] at ht
    exact ht.trans hdX
  have hdSpec : topologicalKrullDim (Spec S) ≤ 2 := by
    change topologicalKrullDim (PrimeSpectrum S) ≤ 2
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact hdS
  have hdPi : topologicalKrullDim Pi ≤ 2 :=
    NormalizedPointDomination.dimension_le_two_of_birational pi
      (NormalizedPointDomination.affineCharts_isNagata_of_nagata S hS hdS) hdSpec hpff
  have hdXi : topologicalKrullDim Xi ≤ 2 :=
    LocalModification.topologicalKrullDim_le_of_local_replacement x hx ai pi fi H hfiU
      2 hdX hdPi
  exact ⟨hXi, hPi, hfiD, haiD, hpiD, hp.1, hp.2, hNoeth, inferInstance,
    hfiU, c.fromTop_toBase i, H, H.w, hff, haff, hpsquare, hpff, hdPi, hdXi⟩

end AlgebraicGeometry.Scheme.Blowup.NormalizedPointBlowupChain
