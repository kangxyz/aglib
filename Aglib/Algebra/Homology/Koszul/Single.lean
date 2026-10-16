/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Motivic Cohomology contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.Algebra.Regular.SMul

/-!
# The one-element Koszul complex

Multiplication by a scalar defines an actual chain complex in degrees zero and
one. Its augmentation to the literal principal module quotient induces an
isomorphism on degree-zero homology. Regularity proves that this augmentation
is a quasi-isomorphism, giving a projective resolution when the module is
projective. These constructions supply the factors of finite Koszul complexes.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M] (a : R)

/-- The terms of the one-element multiplication complex. -/
noncomputable def singleX : ℕ → ModuleCat.{v} R
  | 0 => ModuleCat.of R M
  | 1 => ModuleCat.of R M
  | _ + 2 => 0

/-- Its only possibly nonzero differential is multiplication by the scalar. -/
noncomputable def singleD : (n : ℕ) → singleX (R := R) M (n + 1) ⟶ singleX (R := R) M n
  | 0 => ModuleCat.ofHom (LinearMap.lsmul R M a)
  | _ + 1 => 0

/-- The actual one-element Koszul complex of a module. -/
noncomputable def singleComplex : ChainComplex (ModuleCat.{v} R) ℕ :=
  ChainComplex.of (singleX (R := R) M) (singleD M a) (by
    intro n
    cases n <;> exact zero_comp)

@[simp]
theorem singleComplex_X_zero : (singleComplex M a).X 0 = ModuleCat.of R M := rfl

@[simp]
theorem singleComplex_X_one : (singleComplex M a).X 1 = ModuleCat.of R M := rfl

@[simp]
theorem singleComplex_X_add_two (n : ℕ) : (singleComplex M a).X (n + 2) = 0 := rfl

@[simp]
theorem singleComplex_d_one_zero :
    (singleComplex M a).d 1 0 = ModuleCat.ofHom (LinearMap.lsmul R M a) :=
  ChainComplex.of_d (singleX (R := R) M) (singleD M a) 0

@[simp]
theorem singleComplex_d_add_two (n : ℕ) : (singleComplex M a).d (n + 2) (n + 1) = 0 :=
  ChainComplex.of_d (singleX (R := R) M) (singleD M a) (n + 1)

/-- The literal quotient of a module by scalar multiplication. -/
abbrev SingleQuotient := M ⧸ LinearMap.range (LinearMap.lsmul R M a)

/-- Degree-zero homology is the literal principal module quotient. -/
noncomputable def singleHomologyZeroIso :
    (singleComplex M a).homology 0 ≅ ModuleCat.of R (SingleQuotient M a) :=
  (singleComplex M a).isoHomologyι₀ ≪≫
    (singleComplex M a).opcyclesIsoSc' 1 0 0 (by simp) (by simp) ≪≫
    ((singleComplex M a).sc' 1 0 0).moduleCatOpcyclesIso

/-- Degree-one homology is the kernel of scalar multiplication. -/
noncomputable def singleHomologyOneIso :
    (singleComplex M a).homology 1 ≅
      ModuleCat.of R (LinearMap.ker (LinearMap.lsmul R M a)) :=
  ((singleComplex M a).isoHomologyπ 2 1 (by simp)
    (singleComplex_d_add_two M a 0)).symm ≪≫
    (singleComplex M a).cyclesIsoSc' 2 1 0 (by simp) (by simp) ≪≫
    ((singleComplex M a).sc' 2 1 0).moduleCatCyclesIso

/-- Terms above degree one, hence their homology, vanish. -/
theorem singleExactAt_add_two (n : ℕ) : (singleComplex M a).ExactAt (n + 2) :=
  HomologicalComplex.ExactAt.of_isZero (isZero_zero _)

/-- Regular scalar multiplication makes degree one exact. -/
theorem singleExactAt_one_of_regular (ha : IsSMulRegular M a) :
    (singleComplex M a).ExactAt 1 := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have : Subsingleton (LinearMap.ker (LinearMap.lsmul R M a)) :=
    ⟨fun x y => Subtype.ext (ha (x.property.trans y.property.symm))⟩
  exact (ModuleCat.isZero_of_subsingleton
    (ModuleCat.of R (LinearMap.ker (LinearMap.lsmul R M a)))).of_iso
      (singleHomologyOneIso M a)

/-- The quotient projection used as the augmentation in degree zero. -/
def singleAugmentationMap : ModuleCat.of R M ⟶ ModuleCat.of R (SingleQuotient M a) :=
  ModuleCat.ofHom (LinearMap.range (LinearMap.lsmul R M a)).mkQ

@[reassoc]
theorem single_d_augmentationMap :
    (singleComplex M a).d 1 0 ≫ singleAugmentationMap M a = 0 :=
  ModuleCat.hom_ext
    (LinearMap.exact_map_mkQ_range (LinearMap.lsmul R M a)).linearMap_comp_eq_zero

/-- The augmentation chain map to the principal quotient in degree zero. -/
noncomputable def singleAugmentation :
    singleComplex M a ⟶ (ChainComplex.single₀ (ModuleCat.{v} R)).obj
      (ModuleCat.of R (SingleQuotient M a)) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨singleAugmentationMap M a, single_d_augmentationMap M a⟩

@[simp]
theorem singleAugmentation_f_zero :
    (singleAugmentation M a).f 0 = singleAugmentationMap M a :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- Exactness at the augmentation needs no regularity assumption. -/
theorem singleAugmentation_exact :
    (ShortComplex.mk ((singleComplex M a).d 1 0) (singleAugmentationMap M a)
      (single_d_augmentationMap M a)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  exact LinearMap.exact_map_mkQ_range (LinearMap.lsmul R M a)

instance singleAugmentationMap_epi : Epi (singleAugmentationMap M a) :=
  (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)

/-- The literal augmentation always computes degree-zero homology. -/
theorem singleAugmentation_quasiIsoAt_zero : QuasiIsoAt (singleAugmentation M a) 0 := by
  rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
  · exact ⟨singleAugmentation_exact M a, singleAugmentationMap_epi M a⟩
  · exact (singleComplex M a).shape _ _ (by simp)
  · rfl
  · rfl

/-- A regular scalar gives an actual quasi-isomorphism to its quotient. -/
theorem singleAugmentation_quasiIso_of_regular (ha : IsSMulRegular M a) :
    QuasiIso (singleAugmentation M a) := by
  constructor
  intro n
  obtain (_ | _ | n) := n
  · exact singleAugmentation_quasiIsoAt_zero M a
  · rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)]
    exact singleExactAt_one_of_regular M a ha
  · rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)]
    exact singleExactAt_add_two M a n

instance singleComplex_projective [Module.Projective R M] (n : ℕ) :
    Projective ((singleComplex M a).X n) := by
  obtain (_ | _ | n) := n
  · change Projective (ModuleCat.of R M)
    infer_instance
  · change Projective (ModuleCat.of R M)
    infer_instance
  · exact (isZero_zero _).projective

/-- The genuine projective resolution for one regular scalar on a projective module. -/
noncomputable def singleProjectiveResolution [Module.Projective R M]
    (ha : IsSMulRegular M a) :
    CategoryTheory.ProjectiveResolution (ModuleCat.of R (SingleQuotient M a)) where
  complex := singleComplex M a
  π := singleAugmentation M a
  quasiIso := singleAugmentation_quasiIso_of_regular M a ha

end ChainComplex.Koszul
