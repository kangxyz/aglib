/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Finiteness
public import Aglib.RingTheory.RegularLocalRing.FiniteProjectiveDimension
public import Aglib.RingTheory.RegularLocalRing.ResidueProjectiveDimension
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Regularity descent along flat local maps

Finite projective-dimension bounds on finite modules descend along faithfully
flat ring homomorphisms. Applied to a flat local map with regular target, this
bounds the projective dimension of the original residue field. The proved
residue-field criterion then gives regularity of the source. The final ring
theorem allows independent source and target universes.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits IsLocalRing
open scoped TensorProduct

namespace ModuleCat

/-- Finite projective-dimension bounds on finite modules descend along the
same faithfully flat homomorphism used for native scalar extension. -/
theorem hasProjectiveDimensionLE_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S] [IsNoetherianRing R]
    (f : R →+* S) (hf : f.FaithfullyFlat)
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ)
    [HasProjectiveDimensionLE ((extendScalars f).obj M) n] :
    HasProjectiveDimensionLE M n := by
  algebraize [f]
  let F := extendScalars f
  have : PreservesFiniteLimits F := preservesFiniteLimits_extendScalars_of_flat hf.flat
  induction n generalizing M with
  | zero =>
    have : Projective (F.obj M) :=
      (projective_iff_hasProjectiveDimensionLE_zero (F.obj M)).mpr inferInstance
    have : Module.Projective S (F.obj M) := inferInstance
    have : Module.Flat S (S ⊗[R] M) := inferInstanceAs (Module.Flat S (F.obj M))
    have : Module.Flat R M := Module.Flat.of_flat_tensorProduct R M S
    have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
    have : Module.Projective R M := Module.Flat.projective_of_finitePresentation
    exact (projective_iff_hasProjectiveDimensionLE_zero M).mp inferInstance
  | succ n ih =>
    obtain ⟨P, _, _, _, _, p, hp⟩ := Module.exists_finite_presentation R M
    let T := p.shortComplexKer
    have hT : T.ShortExact := LinearMap.shortExact_shortComplexKer hp
    have : Module.Finite R T.X₁ := inferInstanceAs (Module.Finite R (LinearMap.ker p))
    have : Module.Projective S (F.obj T.X₂) := projective_extendScalars f T.X₂
    have hTF : (T.map F).ShortExact := hT.map_of_exact F
    have hPF : Projective (T.map F).X₂ := by
      change Projective (F.obj T.X₂)
      infer_instance
    have hMF : HasProjectiveDimensionLE (T.map F).X₃ (n + 1) := by
      change HasProjectiveDimensionLE ((extendScalars f).obj M) (n + 1)
      infer_instance
    have : HasProjectiveDimensionLE (F.obj T.X₁) n :=
      (hTF.hasProjectiveDimensionLT_X₃_iff n hPF).mp hMF
    have : HasProjectiveDimensionLE T.X₁ n := ih T.X₁
    exact (hT.hasProjectiveDimensionLT_X₃_iff n inferInstance).mpr inferInstance

end ModuleCat

namespace IsRegularLocalRing

/-- For a flat local map with regular target, every finite module over the
source has projective dimension bounded by the target dimension. -/
theorem projectiveDimension_le_of_flat_local
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing S]
    (f : R →+* S) [IsLocalHom f] (hf : f.Flat)
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    projectiveDimension M ≤ ringKrullDim S := by
  algebraize [f]
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hfaith : f.FaithfullyFlat := by
    change Module.FaithfullyFlat R S
    infer_instance
  let d := (maximalIdeal S).spanFinrank
  have hd : ringKrullDim S = (d : ℕ) := spanFinrank_maximalIdeal.symm
  have : Module.Finite S ((ModuleCat.extendScalars f).obj M) :=
    ModuleCat.finite_extendScalars f M
  have : HasProjectiveDimensionLE ((ModuleCat.extendScalars f).obj M) d :=
    (projectiveDimension_le_iff _ d).mp (projectiveDimension_le_dimension d S hd _)
  rw [hd, projectiveDimension_le_iff]
  exact ModuleCat.hasProjectiveDimensionLE_of_faithfullyFlat f hfaith M d

/-- In particular, the actual residue field of the source has finite
projective dimension, with no finite-type or unramifiedness hypothesis. -/
theorem residueField_hasProjectiveDimensionLE_of_flat_local
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing S]
    (f : R →+* S) [IsLocalHom f] (hf : f.Flat) :
    HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R))
      (maximalIdeal S).spanFinrank := by
  apply (projectiveDimension_le_iff _ _).mp
  rw [spanFinrank_maximalIdeal]
  exact projectiveDimension_le_of_flat_local f hf _

/-- Regularity descends along an actual flat local homomorphism of Noetherian
local rings. Source and target universes are independent, and flatness uses
the module structure determined by that same homomorphism. -/
@[stacks 00OF]
theorem of_flat_local
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing S]
    (f : R →+* S) [IsLocalHom f] (hf : f.Flat) : IsRegularLocalRing R := by
  let R' := ULift.{v} R
  let S' := ULift.{u} S
  let eR : R' ≃+* R := ULift.ringEquiv
  let eS : S' ≃+* S := ULift.ringEquiv
  have : IsLocalRing R' := eR.symm.isLocalRing
  have : IsNoetherianRing R' := isNoetherianRing_of_ringEquiv R eR.symm
  have : IsRegularLocalRing S' := of_ringEquiv eS.symm
  let f' : R' →+* S' := f.ulift
  have : IsLocalHom f' := by
    refine ⟨fun a ha => ?_⟩
    have hbase : IsUnit (eR a) :=
      isUnit_of_map_unit f (eR a) (eS.toRingHom.isUnit_map ha)
    have hunit := eR.symm.toRingHom.isUnit_map hbase
    change IsUnit (eR.symm (eR a)) at hunit
    simpa only [RingEquiv.symm_apply_apply] using hunit
  have hf' : f'.Flat := RingHom.Flat.ulift_iff.mpr hf
  have hpd : HasProjectiveDimensionLE (ModuleCat.of R' (ResidueField R'))
      (maximalIdeal S').spanFinrank :=
    residueField_hasProjectiveDimensionLE_of_flat_local f' hf'
  have : IsRegularLocalRing R' :=
    @of_residueField_hasProjectiveDimensionLE R' _ _ _ (maximalIdeal S').spanFinrank hpd
  exact of_ringEquiv eR

end IsRegularLocalRing
