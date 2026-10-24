/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ZeroLocus.ImageFactorisation

/-!
# Image ideals and the order of closed subschemes

For closed subschemes `W ≤ W'` of a scheme `X` (ideal inclusion `I_W ⊆ I_{W'}`, so
`V(W') ⊆ V(W)`) and module-to-unit maps `φ : M ⟶ 𝒪_X`:

* `IdealSheafData.idealInclusion_comp_toQuotientModule_eq_zero_of_le`: `I_W ⟶ 𝒪_X ⟶ 𝒪_X / I_{W'}`
  vanishes. The closed immersion of `W'` factors through that of `W`
  (`IdealSheafData.inclusion_subschemeι`), so `I_W` is killed by the structure map of `W'`
  (`Scheme.Hom.structureModuleMap_comp`) and lifts to `I_{W'}`.
* `Hom.comp_toQuotientModule_eq_zero_of_imageIdealData_le`: for quasi-coherent `M`, if the image
  ideal of `φ` is contained in `W`, then `φ` vanishes on `𝒪_X / I_W`; `φ` factors through its
  image ideal (`Hom.zeroIdealFactor_inclusion`). This generalizes
  `Hom.comp_toQuotientModule_imageIdealData_eq_zero` (`Modules/ZeroLocus/ImageFactorisation`), the
  case `W = I(φ)`.
* `Hom.imageIdealData_comp_le`: the image ideal of `a ≫ φ` is contained in that of `φ`.
* `Hom.imageIdealData_eq_bot_iff`: for quasi-coherent `M`, the image ideal of `φ` is zero if and
  only if `φ = 0`, by the sections over affine opens (`Hom.imageIdealData_eq`).

No quasi-coherence is needed for the first and third statements.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

namespace IdealSheafData

variable {X : Scheme.{u}}

/-- For `W ≤ W'`, the ideal module of `W` is killed by the structure map of `W'`. -/
theorem idealInclusion_comp_structureModuleMap_eq_zero_of_le {W W' : X.IdealSheafData}
    (h : W ≤ W') :
    Scheme.Hom.idealInclusion W.subschemeι ≫ Scheme.Hom.structureModuleMap W'.subschemeι = 0 := by
  rw [← Scheme.Hom.structureModuleMap_congr (inclusion_subschemeι h),
    Scheme.Hom.structureModuleMap_comp_assoc, Scheme.Hom.idealInclusion_structureMap_assoc,
    zero_comp]

/-- **Smaller ideals vanish on larger quotients**: for `W ≤ W'`, the composite
`I_W ⟶ 𝒪_X ⟶ 𝒪_X / I_{W'}` is zero. -/
theorem idealInclusion_comp_toQuotientModule_eq_zero_of_le {W W' : X.IdealSheafData}
    (h : W ≤ W') : Scheme.Hom.idealInclusion W.subschemeι ≫ W'.toQuotientModule = 0 := by
  have hk := kernel.lift_ι (Scheme.Hom.structureModuleMap W'.subschemeι)
    (Scheme.Hom.idealInclusion W.subschemeι)
    (idealInclusion_comp_structureModuleMap_eq_zero_of_le h)
  rw [← hk, Category.assoc,
    show kernel.ι (Scheme.Hom.structureModuleMap W'.subschemeι) ≫ W'.toQuotientModule = 0 from
      cokernel.condition _, comp_zero]

end IdealSheafData

namespace Modules.Hom

variable {X : Scheme.{u}} {M N : X.Modules}

/-- **A map whose image lies in `W` vanishes on `𝒪_X / I_W`**: for quasi-coherent `M` and
`φ : M ⟶ 𝒪_X` with image ideal contained in `W`, `φ ≫ (𝒪_X ⟶ 𝒪_X / I_W) = 0`. -/
theorem comp_toQuotientModule_eq_zero_of_imageIdealData_le [M.IsQuasicoherent]
    (φ : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)) {W : X.IdealSheafData}
    (h : imageIdealData φ ≤ W) : φ ≫ W.toQuotientModule = 0 := by
  rw [← zeroIdealFactor_inclusion φ (imageIdealLocalizes_of_isQuasicoherent φ), Category.assoc,
    show Scheme.Hom.idealInclusion (zeroInclusion φ) ≫ W.toQuotientModule = 0 from
      IdealSheafData.idealInclusion_comp_toQuotientModule_eq_zero_of_le h, comp_zero]

/-- **Image ideals shrink under precomposition**: `I(a ≫ φ) ≤ I(φ)`. -/
theorem imageIdealData_comp_le (a : M ⟶ N)
    (φ : N ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)) :
    imageIdealData (a ≫ φ) ≤ imageIdealData φ := by
  unfold imageIdealData
  apply IdealSheafData.ofIdeals_mono
  intro U
  rintro x ⟨m, rfl⟩
  exact ⟨a.val.app (op U.1) m, rfl⟩

/-- **A map vanishes exactly when its image ideal does**: for quasi-coherent `M` and
`φ : M ⟶ 𝒪_X`, `I(φ) = ⊥` if and only if `φ = 0`. -/
theorem imageIdealData_eq_bot_iff [M.IsQuasicoherent]
    (φ : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)) :
    imageIdealData φ = ⊥ ↔ φ = 0 := by
  constructor
  · intro h
    apply moduleHom_ext_affine
    intro U
    ext m
    have hm : (φ.val.app (op U.1)).hom m ∈ (imageIdealData φ).ideal U := by
      rw [imageIdealData_eq φ (imageIdealLocalizes_of_isQuasicoherent φ) U]
      exact ⟨m, rfl⟩
    rw [h] at hm
    change _ ∈ (⊥ : Ideal Γ(X, U)) at hm
    rw [Scheme.Modules.Hom.zero_app]
    exact (Submodule.mem_bot _).mp hm
  · rintro rfl
    refine le_bot_iff.mp fun U => ?_
    rw [imageIdealData_eq _ (imageIdealLocalizes_of_isQuasicoherent _) U]
    rintro x ⟨m, rfl⟩
    exact zero_mem _

end Modules.Hom

end AlgebraicGeometry.Scheme
