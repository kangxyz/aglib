/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Surjective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Morphisms of projective modules over a square-zero extension

Maps killed by scalar reduction compose to zero. Thus an endomorphism
reducing to the identity is invertible. Fullness on projective sources then
lifts a prescribed reduced isomorphism, retaining its original forward map.
Projectives need not be finite, and the scalar rings need not be Noetherian.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory

namespace ModuleCat

universe u
variable {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (hsurj : Function.Surjective f)

include hsurj

/-- A map killed by scalar reduction has image in the scalar kernel times
the actual target module. -/
theorem range_le_ker_smul_of_extendScalars_map_eq_zero
    {M N : ModuleCat.{u} R} (g : M ⟶ N) (hg : (extendScalars f).map g = 0) :
    LinearMap.range g.hom ≤ RingHom.ker f • (⊤ : Submodule R N) := by
  rw [← ker_extendRestrictScalarsAdj_unit f hsurj N]
  apply LinearMap.range_le_ker_iff.mpr
  have h : g ≫ (extendRestrictScalarsAdj f).unit.app N = 0 := by
    change (𝟭 (ModuleCat R)).map g ≫ (extendRestrictScalarsAdj f).unit.app N = 0
    rw [(extendRestrictScalarsAdj f).unit.naturality g]
    simp [hg]
  exact congrArg ModuleCat.Hom.hom h

/-- Two actual module maps killed by a square-zero scalar reduction have
zero composite. This does not require projective or flat modules. -/
theorem comp_eq_zero_of_extendScalars_map_eq_zero
    (hf : RingHom.ker f ^ 2 = ⊥) {M N P : ModuleCat.{u} R}
    (g : M ⟶ N) (h : N ⟶ P)
    (hg : (extendScalars f).map g = 0) (hh : (extendScalars f).map h = 0) :
    g ≫ h = 0 := by
  have hg' := range_le_ker_smul_of_extendScalars_map_eq_zero f hsurj g hg
  have hh' := range_le_ker_smul_of_extendScalars_map_eq_zero f hsurj h hh
  have hr : LinearMap.range (h.hom.comp g.hom) ≤ ⊥ := by
    calc
      LinearMap.range (h.hom.comp g.hom) = (LinearMap.range g.hom).map h.hom :=
        LinearMap.range_comp _ _
      _ ≤ (RingHom.ker f • (⊤ : Submodule R N)).map h.hom := Submodule.map_mono hg'
      _ = RingHom.ker f • LinearMap.range h.hom := by
        rw [Submodule.map_smul'', Submodule.map_top]
      _ ≤ RingHom.ker f • (RingHom.ker f • (⊤ : Submodule R P)) :=
        Submodule.smul_mono le_rfl hh'
      _ = ⊥ := by rw [← Submodule.mul_smul, ← pow_two, hf, Submodule.bot_smul]
  apply ModuleCat.hom_ext
  exact LinearMap.range_eq_bot.mp (le_antisymm hr bot_le)

/-- An actual endomorphism reducing to the identity is invertible over a
square-zero scalar extension. -/
theorem isIso_of_extendScalars_map_eq_id (hf : RingHom.ker f ^ 2 = ⊥)
    {M : ModuleCat.{u} R} (g : M ⟶ M)
    (hg : (extendScalars f).map g = 𝟙 ((extendScalars f).obj M)) : IsIso g := by
  have hd : (extendScalars f).map (g - 𝟙 M) = 0 := by
    rw [Functor.map_sub, hg, (extendScalars f).map_id M, sub_self]
  have hnil : IsNilpotent (g.hom - LinearMap.id : Module.End R M) := by
    refine ⟨2, ?_⟩
    change (g.hom - LinearMap.id).comp (g.hom - LinearMap.id) = 0
    exact congrArg ModuleCat.Hom.hom
      (comp_eq_zero_of_extendScalars_map_eq_zero f hsurj hf (g - 𝟙 M) (g - 𝟙 M) hd hd)
  have hu : IsUnit g.hom := by
    have h := hnil.isUnit_one_add
    change IsUnit ((1 : Module.End R M) + (g.hom - 1)) at h
    rw [add_comm, sub_add_cancel] at h
    exact h
  exact (ConcreteCategory.isIso_iff_bijective g).mpr ((Module.End.isUnit_iff g.hom).mp hu)

/-- The actual scalar extension reflects invertibility of maps to a
projective target over a square-zero scalar kernel. -/
theorem isIso_of_extendScalars_map_isIso_of_projective
    (hf : RingHom.ker f ^ 2 = ⊥) {M N : ModuleCat.{u} R}
    [Module.Projective R N] (g : M ⟶ N)
    [IsIso ((extendScalars f).map g)] : IsIso g := by
  obtain ⟨h, hh⟩ := extendScalars_map_surjective_of_projective f hsurj N M
    (inv ((extendScalars f).map g))
  change (extendScalars f).map h = inv ((extendScalars f).map g) at hh
  have : IsIso (g ≫ h) := isIso_of_extendScalars_map_eq_id f hsurj hf _ (by
    rw [Functor.map_comp, hh, IsIso.hom_inv_id])
  have : IsIso (h ≫ g) := isIso_of_extendScalars_map_eq_id f hsurj hf _ (by
    rw [Functor.map_comp, hh, IsIso.inv_hom_id])
  have : Mono g := mono_of_mono g h
  have : Epi g := epi_of_epi h g
  exact isIso_of_mono_of_epi g

/-- Every prescribed reduced isomorphism between projective modules lifts
to an actual isomorphism with exactly that reduced forward map. -/
theorem exists_iso_lift_of_square_zero (hf : RingHom.ker f ^ 2 = ⊥)
    (M N : ModuleCat.{u} R) [Module.Projective R M] [Module.Projective R N]
    (e : (extendScalars f).obj M ≅ (extendScalars f).obj N) :
    ∃ e' : M ≅ N, (extendScalars f).map e'.hom = e.hom := by
  obtain ⟨g, hg⟩ := extendScalars_map_surjective_of_projective f hsurj M N e.hom
  change (extendScalars f).map g = e.hom at hg
  have : IsIso ((extendScalars f).map g) := by rw [hg]; infer_instance
  have : IsIso g := isIso_of_extendScalars_map_isIso_of_projective f hsurj hf g
  exact ⟨asIso g, hg⟩

end ModuleCat
