/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.CompatibleSystemHom
public import Aglib.RingTheory.AdicCompletion.CompatibleSystemEffectivity

/-! # Uniform bounds on maps of compatible sections

Ordinary stage kernels and cokernels determine uniform bounds on the original
limit map. No kernel tower is assumed compatible. The cokernel conclusion
retains separation of the actual cokernel, not merely of the target.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AdicCompletion.IsCompatibleSystem

universe u v w
variable {R : Type u} [CommRing R] {I : Ideal R}
  {F : ℕᵒᵖ ⥤ ModuleCat.{v} R} {G : ℕᵒᵖ ⥤ ModuleCat.{w} R}
  (hF : IsCompatibleSystem I F) (hG : IsCompatibleSystem I G)
  (φ : ∀ j, F.obj j →ₗ[R] G.obj j)
  (hφ : ∀ {j k} (a : j ⟶ k) x, φ k (F.map a x) = G.map a (φ j x))

/-- A uniform annihilator of the stage kernels kills the original limit kernel. -/
theorem sectionsMap_smul_ker_eq_bot (J : Ideal R)
    (h : ∀ n : ℕ, J • (φ (op n)).ker = ⊥) :
    J • (ModuleCat.sectionsMapOfLinearMaps φ hφ).ker = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.smul_le.mpr
  intro a ha x hx
  change a • x = 0
  apply Subtype.ext
  funext j
  have hxj : φ j (x.val j) = 0 :=
    congrArg (fun z : ModuleCat.sectionsSubmodule G => z.val j) hx
  have hz := Submodule.smul_mem_smul ha (show x.val j ∈ (φ j).ker from hxj)
  rw [h j.unop] at hz
  exact hz

include hF hG in
/-- The actual separated cokernel detects a uniform stage range bound. -/
theorem sectionsMap_smul_top_le_range (hI : I.FG) (J : Ideal R)
    [IsHausdorff I (ModuleCat.sectionsSubmodule G ⧸
      (ModuleCat.sectionsMapOfLinearMaps φ hφ).range)]
    (h : ∀ n : ℕ, J • (⊤ : Submodule R (G.obj (op n))) ≤ (φ (op n)).range) :
    J • (⊤ : Submodule R (ModuleCat.sectionsSubmodule G)) ≤
      (ModuleCat.sectionsMapOfLinearMaps φ hφ).range := by
  let f := ModuleCat.sectionsMapOfLinearMaps φ hφ
  apply Submodule.smul_le.mpr
  intro a ha y _
  apply (Submodule.Quotient.mk_eq_zero _).mp
  apply IsHausdorff.haus' (I := I)
  intro n
  obtain ⟨x, hx⟩ := h n (Submodule.smul_mem_smul ha
    (Submodule.mem_top : ModuleCat.sectionsEval G n y ∈ ⊤))
  obtain ⟨z, hz⟩ := hF.sectionsEval_surjective n x
  have he : ModuleCat.sectionsEval G n (a • y - f z) = 0 := by
    rw [map_sub, map_smul]
    change a • ModuleCat.sectionsEval G n y - φ (op n)
      (ModuleCat.sectionsEval F n z) = 0
    rw [hz, hx, sub_self]
  have hd : a • y - f z ∈ I ^ n • (⊤ : Submodule R (ModuleCat.sectionsSubmodule G)) := by
    rw [← hG.sectionsEval_ker_eq hI n]
    exact he
  have hq := Submodule.smul_top_le_comap_smul_top (I ^ n) f.range.mkQ hd
  have hfz : f.range.mkQ (f z) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨z, rfl⟩
  apply SModEq.zero.mpr
  simpa only [Submodule.mem_comap, map_sub, hfz, sub_zero,
    Submodule.mkQ_apply] using hq

end AdicCompletion.IsCompatibleSystem
