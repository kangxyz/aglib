/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Support.Powers
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Descent
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Support
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Annihilator
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineOpenSections

/-!
# Actual section annihilation from module-sheaf support

The native module support of sections on an actual affine open is detected
by the original sheaf stalk support. Thus support in a native ideal-sheaf
support gives an actual positive annihilating ideal power on every affine
chart with finite sections and finitely generated ideal. These comparisons
retain the original affine section ring and its original module action.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u v

namespace AlgebraicGeometry.Scheme.Modules

open QuasiCoherent.AffineOpenSections

variable {X : Scheme.{u}} (I : X.IdealSheafData) (M : X.Modules) [M.IsQuasicoherent]

/-- Original stalk support containment detects the native module support of
the actual sections on any affine open. -/
theorem support_affineSections_subset_zeroLocus (hM : support M ⊆ I.support)
    (U : X.affineOpens) :
    Module.support Γ(X, U.1) Γ(M, U.1) ⊆ PrimeSpectrum.zeroLocus (I.ideal U : Set Γ(X, U.1)) := by
  let hU : IsAffineOpen U.1 := U.2
  let N := M.restrict hU.fromSpec
  rw [(toSpecTopSectionsLinearEquiv M hU).support_eq]
  change Module.support Γ(X, U.1) (moduleSpecΓFunctor.obj N) ⊆ _
  rw [← support_eq_support_globalSections N]
  intro p hp
  change p ∈ support (M.restrict hU.fromSpec) at hp
  rw [support_restrict] at hp
  have hxU : hU.fromSpec p ∈ U.1 := (hU.isoSpec.inv p).property
  have hz := (Scheme.IdealSheafData.mem_support_iff_of_mem
    (I := I) (U := U) hxU).mp (hM hp)
  have hz' : p ∈ hU.fromSpec ⁻¹' X.zeroLocus (I.ideal U : Set Γ(X, U.1)) := hz
  simpa only [hU.fromSpec_preimage_zeroLocus] using hz'

/-- Finite actual affine sections supported in the given ideal support are
annihilated by a positive power of that actual affine ideal. -/
theorem exists_pos_pow_le_annihilator_affineSections (hM : support M ⊆ I.support)
    (U : X.affineOpens) [Module.Finite Γ(X, U.1) Γ(M, U.1)] (hI : (I.ideal U).FG) :
    ∃ n : ℕ, 0 < n ∧ (I.ideal U) ^ n ≤ Module.annihilator Γ(X, U.1) Γ(M, U.1) :=
  Module.exists_pos_pow_le_annihilator_of_support_subset Γ(M, U.1) (I.ideal U) hI
    (support_affineSections_subset_zeroLocus I M hM U)

/-- Annihilation on an actual affine open cover implies annihilation on
all original affine section modules. No finiteness of the cover is needed. -/
theorem killedByIdealSheaf_of_affineCover {ι : Type v} (U : ι → X.affineOpens)
    (hcover : ∀ x : X, ∃ i, x ∈ (U i).1)
    (hAnn : ∀ i, I.ideal (U i) ≤ Module.annihilator Γ(X, (U i).1) Γ(M, (U i).1)) :
    killedByIdealSheaf I M := by
  intro V a ha m
  apply TopCat.Presheaf.section_ext ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)
    V.1 (a • m) 0
  intro x hxV
  obtain ⟨i, hxi⟩ := hcover x
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ V.1 ⊓ (U i).1 from ⟨hxV, hxi⟩) (V.1 ⊓ (U i).1).isOpen
  let hWV : W ≤ V.1 := hWle.trans inf_le_left
  let hWUi : W ≤ (U i).1 := hWle.trans inf_le_right
  have hAnnW : I.ideal ⟨W, hW⟩ ≤ Module.annihilator Γ(X, W) Γ(M, W) := by
    rw [← I.map_ideal hWUi]
    exact (Ideal.map_mono (hAnn i)).trans (map_annihilator_affineSections_le M (U i).2 hWUi)
  have haW : X.presheaf.map (homOfLE hWV).op a ∈ I.ideal ⟨W, hW⟩ :=
    I.ideal_le_comap_ideal hWV ha
  have hzero : M.presheaf.map (homOfLE hWV).op (a • m) = 0 := by
    change M.val.map (homOfLE hWV).op (a • m) = 0
    rw [M.val.map_smul]
    exact (Module.mem_annihilator.mp (hAnnW haW)) _
  calc
    M.presheaf.germ V.1 x hxV (a • m) =
        M.presheaf.germ W x hxW (M.presheaf.map (homOfLE hWV).op (a • m)) :=
      (M.presheaf.germ_res_apply (homOfLE hWV) x hxW (a • m)).symm
    _ = M.presheaf.germ V.1 x hxV 0 := by rw [hzero, map_zero, map_zero]

/-- A finite affine subcover makes the actual chartwise annihilating powers
uniform. Only compactness, finite actual sections and finitely generated
actual chart ideals are used. -/
theorem exists_pos_pow_killedByIdealSheaf_of_support_subset [CompactSpace X]
    (hM : support M ⊆ I.support) (hI : ∀ U : X.affineOpens, (I.ideal U).FG)
    (hfinite : ∀ U : X.affineOpens, Module.Finite Γ(X, U.1) Γ(M, U.1)) :
    ∃ n : ℕ, 0 < n ∧ killedByIdealSheaf (I ^ n) M := by
  classical
  have hpow (U : X.affineOpens) :
      ∃ n : ℕ, 0 < n ∧ (I.ideal U) ^ n ≤ Module.annihilator Γ(X, U.1) Γ(M, U.1) := by
    let := hfinite U
    exact exists_pos_pow_le_annihilator_affineSections I M hM U (hI U)
  choose n hnpos hn using hpow
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens => (U.1 : Set X)) (fun U => U.1.isOpen) (by
      intro x hx
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hx isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩)
  refine ⟨s.sup n + 1, Nat.succ_pos _, ?_⟩
  apply killedByIdealSheaf_of_affineCover (I ^ (s.sup n + 1)) M
    (fun U : {U : X.affineOpens // U ∈ s} => U.val)
  · intro x
    obtain ⟨U, hUs, hxU⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact ⟨⟨U, hUs⟩, hxU⟩
  · intro U
    change (I.ideal U.val) ^ (s.sup n + 1) ≤ _
    exact (Ideal.pow_le_pow_right
      ((Finset.le_sup U.property).trans (Nat.le_succ (s.sup n)))).trans (hn U.val)

end AlgebraicGeometry.Scheme.Modules
