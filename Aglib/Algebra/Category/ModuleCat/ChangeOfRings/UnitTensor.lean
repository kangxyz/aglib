/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Unit pure tensors through composite and congruent scalar extensions

* `ModuleCat.extendScalarsComp_hom_app_comp_map_comp_one_tmul`: the composite
  `C ⊗_A M ≅ C ⊗_B (B ⊗_A M) ⟶ C ⊗_B N ⟶ P` of `ModuleCat.extendScalarsComp` with two maps that
  are given on unit pure tensors, evaluated on a unit pure tensor, at variable modules;
* `ModuleCat.extendScalarsCongrIso`: extension of scalars along equal ring maps, with
  `ModuleCat.extendScalarsCongrIso_hom_one_tmul` on unit pure tensors.

The three rings share one universe, as in Mathlib's `extendScalarsComp`, and the modules live in
the next one, as module cohomology groups do.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Extension of scalars along equal ring maps. -/
def extendScalarsCongrIso {f g : R →+* S} (h : f = g) (M : ModuleCat.{u + 1} R) :
    (extendScalars f).obj M ≅ (extendScalars g).obj M :=
  eqToIso (by rw [h])

/-- The comparison `extendScalarsCongrIso` retains the unit pure tensors. -/
theorem extendScalarsCongrIso_hom_one_tmul {f g : R →+* S} (h : f = g)
    (M : ModuleCat.{u + 1} R) (m : M) :
    (extendScalarsCongrIso h M).hom ((1 : S) ⊗ₜ[R,f] m) = (1 : S) ⊗ₜ[R,g] m := by
  subst h
  rfl

-- Pure tensors in `(extendScalars f).obj M` are typed through `restrictScalars`; rewriting with
-- them needs the module-category presentation, which is not reducible.
set_option backward.isDefEq.respectTransparency false in
/-- The composite `C ⊗_A M ≅ C ⊗_B (B ⊗_A M) ⟶ C ⊗_B N ⟶ P` on a unit pure tensor, for maps
given on unit pure tensors, at variable modules. -/
theorem extendScalarsComp_hom_app_comp_map_comp_one_tmul {R₁ R₂ R₃ : Type u}
    [CommRing R₁] [CommRing R₂] [CommRing R₃] (f₁₂ : R₁ →+* R₂) (f₂₃ : R₂ →+* R₃)
    {M : ModuleCat.{u + 1} R₁} {N : ModuleCat.{u + 1} R₂} {P : ModuleCat.{u + 1} R₃}
    (g : (ModuleCat.extendScalars f₁₂).obj M ⟶ N) (h : (ModuleCat.extendScalars f₂₃).obj N ⟶ P)
    (φ : M → N) (hg : ∀ m : M, g ((1 : R₂) ⊗ₜ[R₁, f₁₂] m) = φ m)
    (ψ : N → P) (hh : ∀ n : N, h ((1 : R₃) ⊗ₜ[R₂, f₂₃] n) = ψ n) (m : M) :
    ((ModuleCat.extendScalarsComp.{u, u + 1} f₁₂ f₂₃).hom.app M ≫
        (ModuleCat.extendScalars f₂₃).map g ≫ h)
        ((1 : R₃) ⊗ₜ[R₁, f₂₃.comp f₁₂] m) = ψ (φ m) := by
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ModuleCat.extendScalarsComp_hom_app_one_tmul]
  change h ((1 : R₃) ⊗ₜ[R₂, f₂₃] g ((1 : R₂) ⊗ₜ[R₁, f₁₂] m)) = _
  rw [hg, hh]

end ModuleCat
