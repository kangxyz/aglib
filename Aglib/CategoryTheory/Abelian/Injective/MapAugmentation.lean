/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.CochainComplex.Augmentation
public import Aglib.Algebra.Homology.Embedding.MapExtend
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.Injective.Extend

/-!
# The original augmentation after an additive functor

The native single-zero universal property gives the actual mapped
augmentation of any supplied injective resolution. Left exactness alone
proves its degree-zero quasi-isomorphism. Vanishing of the original higher
derived objects for this coefficient then proves that this same arrow is
a quasi-isomorphism, and that the original integer resolution inclusion
remains a quasi-isomorphism after the functor. No target resolution or
derived category is chosen, and the functor need not preserve homology.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v u' v'

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] {M : C} (I : InjectiveResolution M)

/-- The original mapped resolution augmentation, using the native single-zero property. -/
def mapAugmentation :
    (CochainComplex.single₀ D).obj (F.obj M) ⟶
      (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨F.map (I.ι.f 0), by
      change F.map (I.ι.f 0) ≫ F.map (I.cocomplex.d 0 1) = 0
      rw [← Functor.map_comp, I.ι_f_zero_comp_complex_d, Functor.map_zero]⟩

/-- Its degree-zero component is the literal image of the original resolution map. -/
@[simp]
theorem mapAugmentation_f_zero : (I.mapAugmentation F).f 0 = F.map (I.ι.f 0) :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- The augmentation is the original single comparison followed by the mapped inclusion. -/
theorem mapAugmentation_eq :
    I.mapAugmentation F =
      (singleMapHomologicalComplex F (.up ℕ) 0).inv.app M ≫
        (F.mapHomologicalComplex (.up ℕ)).map I.ι := by
  apply from_single_hom_ext
  simp

/-- Every supplied native resolution lift preserves the actual mapped augmentation. -/
@[reassoc]
theorem mapAugmentation_naturality {N : C} {J : InjectiveResolution N} {f : M ⟶ N}
    (φ : InjectiveResolution.Hom I J f) :
    I.mapAugmentation F ≫ (F.mapHomologicalComplex (.up ℕ)).map φ.hom =
      (CochainComplex.single₀ D).map (F.map f) ≫ J.mapAugmentation F := by
  apply from_single_hom_ext
  simp only [comp_f, Functor.mapHomologicalComplex_map_f, mapAugmentation_f_zero,
    CochainComplex.single₀_map_f_zero, ← Functor.map_comp]
  congr 1
  simpa only [CochainComplex.single₀_map_f_zero] using φ.ι_f_zero_comp_hom_f_zero

variable [PreservesFiniteLimits F]

/-- Preserving the original kernel proves degree-zero exactness for every coefficient. -/
theorem mapAugmentation_quasiIsoAt_zero : QuasiIsoAt (I.mapAugmentation F) 0 := by
  let : Mono ((I.mapAugmentation F).f 0) := by
    rw [mapAugmentation_f_zero]
    infer_instance
  apply CochainComplex.quasiIsoAtZero_of_augmentation_exact
  simpa only [mapAugmentation_f_zero, Functor.mapHomologicalComplex_obj_X,
    Functor.mapHomologicalComplex_obj_d, CochainComplex.single₀_obj_zero] using
    (ShortComplex.exact_of_f_is_kernel
      (ShortComplex.mk (F.map (I.ι.f 0)) (F.map (I.cocomplex.d 0 1)) (by
        rw [← F.map_comp, I.ι_f_zero_comp_complex_d, F.map_zero]))
      (KernelFork.mapIsLimit _ I.isLimitKernelFork F))

variable [EnoughInjectives C]

/-- Coefficient-specific higher vanishing makes the same original augmentation a
quasi-isomorphism. No exactness assertion about the functor on other objects is used. -/
theorem mapAugmentation_quasiIso_of_isZero_rightDerived_succ
    (hM : ∀ n : ℕ, IsZero ((F.rightDerived (n + 1)).obj M)) :
    QuasiIso (I.mapAugmentation F) := by
  constructor
  intro n
  cases n with
  | zero => exact I.mapAugmentation_quasiIsoAt_zero F
  | succ n =>
    rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ _)]
    rw [exactAt_iff_isZero_homology]
    exact (hM n).of_iso (I.isoRightDerivedObj F (n + 1)).symm

/-- The literal image of the original integer resolution inclusion is a
quasi-isomorphism under coefficient-specific higher vanishing. -/
theorem map_ι'_quasiIso_of_isZero_rightDerived_succ
    (hM : ∀ n : ℕ, IsZero ((F.rightDerived (n + 1)).obj M)) :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map I.ι') := by
  have : QuasiIso (I.mapAugmentation F) :=
    I.mapAugmentation_quasiIso_of_isZero_rightDerived_succ F hM
  have hnat : QuasiIso ((F.mapHomologicalComplex (.up ℕ)).map I.ι) := by
    rw [← quasiIso_iff_comp_left ((singleMapHomologicalComplex F (.up ℕ) 0).inv.app M)]
    rw [← mapAugmentation_eq]
    infer_instance
  have hext : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map
      (extendMap I.ι ComplexShape.embeddingUpNat)) := by
    rw [← quasiIso_iff_comp_right _
      (I.cocomplex.mapExtendIso F ComplexShape.embeddingUpNat).hom]
    rw [mapExtendIso_hom_naturality]
    infer_instance
  dsimp only [InjectiveResolution.ι']
  rw [Functor.map_comp, ComplexShape.Embedding.extendFunctor_map]
  exact quasiIso_comp _ _

end CategoryTheory.InjectiveResolution
