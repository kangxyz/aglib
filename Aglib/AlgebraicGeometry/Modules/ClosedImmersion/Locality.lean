/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Killed

/-!
# Affine and stalk detection of actual ideal annihilation

The original affine annihilation condition acts on arbitrary module stalks.
It forces vanishing off the native ideal support. For an inducing
quasi-compact scheme map, every kernel element of the original stalk ring
map has an affine representative in the actual kernel ideal. These results
retain all original germs and actions, without quasicoherence or finiteness.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (I : X.IdealSheafData) (M : X.Modules)

/-- A germ of an actual affine ideal section annihilates every module-stalk
element when that ideal annihilates the original section sheaves. -/
theorem killedByIdealSheaf_germ_smul_eq_zero (hM : killedByIdealSheaf I M)
    (U : X.affineOpens) (x : X) (hxU : x ∈ U.1) (a : Γ(X, U.1)) (ha : a ∈ I.ideal U)
    (m : (moduleStalk X x).obj M) : X.presheaf.germ U.1 x hxU a • m = 0 := by
  obtain ⟨V, hVU, hxV, s, rfl⟩ := M.presheaf.exists_le_germ_eq m hxU
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
  let hWU : W ≤ U.1 := hWV.trans hVU
  let a' : Γ(X, W) := X.presheaf.map (homOfLE hWU).op a
  let s' : Γ(M, W) := M.presheaf.map (homOfLE hWV).op s
  have ha' : a' ∈ I.ideal ⟨W, hW⟩ := I.ideal_le_comap_ideal hWU ha
  have haeq := X.presheaf.germ_res_apply (homOfLE hWU) x hxW a
  have hseq := M.presheaf.germ_res_apply (homOfLE hWV) x hxW s
  calc
    _ = X.presheaf.germ W x hxW a' • M.presheaf.germ W x hxW s' := by
      dsimp only [a', s']
      erw [haeq, hseq]
    _ = M.presheaf.germ W x hxW (a' • s') :=
      (PresheafOfModules.germ_smul M.val x W hxW a' s').symm
    _ = 0 := by rw [hM ⟨W, hW⟩ a' ha' s', map_zero]

/-- Original affine annihilation can be detected by its original germ
actions on every actual stalk. -/
theorem killedByIdealSheaf_iff_germ_smul_eq_zero :
    killedByIdealSheaf I M ↔
      ∀ (U : X.affineOpens) (x : X) (hx : x ∈ U.1) (a : Γ(X, U.1)),
        a ∈ I.ideal U → ∀ m : (moduleStalk X x).obj M,
          X.presheaf.germ U.1 x hx a • m = 0 := by
  constructor
  · exact killedByIdealSheaf_germ_smul_eq_zero I M
  · intro h U a ha m
    apply TopCat.Presheaf.section_ext ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)
      U.1 (a • m) 0
    intro x hx
    erw [PresheafOfModules.germ_smul M.val x U.1 hx a m, map_zero]
    exact h U x hx a ha (M.presheaf.germ U.1 x hx m)

/-- An annihilated arbitrary module sheaf vanishes at every stalk off the
native ideal support. No finite-type support theorem is assumed. -/
theorem killedByIdealSheaf_isZero_stalk_of_not_mem_support
    (hM : killedByIdealSheaf I M) (x : X) (hx : x ∉ I.support) :
    IsZero ((moduleStalk X x).obj M) := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hn : x ∉ X.zeroLocus (U := U) (I.ideal ⟨U, hU⟩) :=
    fun h => hx ((Scheme.IdealSheafData.mem_support_iff_of_mem
      (I := I) (U := ⟨U, hU⟩) hxU).mpr h)
  simp only [X.mem_zeroLocus_iff] at hn
  push Not at hn
  obtain ⟨a, ha, hxa⟩ := hn
  have hu : IsUnit (X.presheaf.germ U x hxU a) := (X.mem_basicOpen a x hxU).mp hxa
  have hz (m : (moduleStalk X x).obj M) : m = 0 := by
    apply hu.smul_left_cancel.mp
    rw [smul_zero]
    exact killedByIdealSheaf_germ_smul_eq_zero I M hM ⟨U, hU⟩ x hxU a ha m
  let : Subsingleton ((moduleStalk X x).obj M) := ⟨fun m n => (hz m).trans (hz n).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- For an inducing quasi-compact map, each element of the original stalk
ring-map kernel has an actual affine representative in the native kernel
ideal sheaf. -/
theorem exists_affine_germ_mem_ker_of_stalkMap_eq_zero (f : X ⟶ Y)
    [QuasiCompact f] (hf : Topology.IsInducing f) (x : X)
    (a : Y.presheaf.stalk (f x)) (ha : f.stalkMap x a = 0) :
    ∃ (U : Y.affineOpens) (hx : f x ∈ U.1) (s : Γ(Y, U.1)),
      s ∈ f.ker.ideal U ∧ Y.presheaf.germ U.1 (f x) hx s = a := by
  obtain ⟨U, hxU, s, rfl⟩ := Y.presheaf.exists_germ_eq a
  rw [f.germ_stalkMap_apply] at ha
  obtain ⟨V, w, hxV, hsV⟩ := X.toRingedSpace.exists_res_eq_zero_of_germ_eq_zero
    (f ⁻¹ᵁ U) (f.app U s) ⟨x, hxU⟩ ha
  obtain ⟨V₀, hV₀, heq⟩ := hf.isOpen_iff.mp V.isOpen
  let W₀ : Y.Opens := ⟨V₀, hV₀⟩
  have hW₀ : f ⁻¹ᵁ W₀ = V := SetLike.ext' heq
  have hxW₀ : f x ∈ W₀ := by
    change x ∈ f ⁻¹ᵁ W₀
    rw [hW₀]
    exact hxV
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWle⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (show f x ∈ W₀ ⊓ U from ⟨hxW₀, hxU⟩) (W₀ ⊓ U).isOpen
  let hWU : W ≤ U := hWle.trans inf_le_right
  let t : Γ(Y, W) := Y.presheaf.map (homOfLE hWU).op s
  refine ⟨⟨W, hW⟩, hxW, t, ?_, ?_⟩
  · rw [f.ker_apply]
    change (f.app W).hom t = 0
    have hn := ConcreteCategory.congr_hom (f.naturality (homOfLE hWU).op) s
    change (f.app W).hom t =
      X.presheaf.map (homOfLE (f.preimage_mono hWU)).op (f.app U s) at hn
    rw [hn]
    have hpre : f ⁻¹ᵁ W ≤ V := by
      rw [← hW₀]
      exact f.preimage_mono (hWle.trans inf_le_left)
    rw [show (homOfLE (f.preimage_mono hWU)).op = w.op ≫ (homOfLE hpre).op from
      Subsingleton.elim _ _, X.presheaf.map_comp, ConcreteCategory.comp_apply, hsV, map_zero]
  · exact Y.presheaf.germ_res_apply (homOfLE hWU) (f x) hxW s

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Affine kernel-ideal annihilation implies annihilation by the original
stalk-map kernel, for every coefficient module sheaf. -/
theorem killedByIdealSheaf_ker_le_annihilator_stalk (f : X ⟶ Y)
    [QuasiCompact f] (hf : Topology.IsInducing f) (M : Y.Modules)
    (hM : killedByIdealSheaf f.ker M) (x : X) :
    RingHom.ker (f.stalkMap x).hom ≤
      Module.annihilator (Y.presheaf.stalk (f x)) ((moduleStalk Y (f x)).obj M) := by
  intro a ha
  rw [Module.mem_annihilator]
  intro m
  obtain ⟨U, hxU, s, hs, he⟩ :=
    f.exists_affine_germ_mem_ker_of_stalkMap_eq_zero hf x a (RingHom.mem_ker.mp ha)
  rw [← he]
  exact killedByIdealSheaf_germ_smul_eq_zero f.ker M hM U (f x) hxU s hs m

end AlgebraicGeometry.Scheme.Modules
