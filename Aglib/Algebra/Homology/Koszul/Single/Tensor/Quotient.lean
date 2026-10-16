/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Motivic Cohomology contributors
-/
module

public import Aglib.Algebra.Homology.Koszul.Single.Quotient
public import Aglib.Algebra.Homology.Koszul.Single.Tensor.Elements
public import Aglib.Algebra.Homology.ShortComplex.ModuleQuasiIso

/-!
# The quotient comparison for a one-element Koszul tensor

The old-column quotient projection defines a chain map from the actual tensor
complex to the literal degreewise scalar quotient. If scalar multiplication is
injective on every term, quotient cycles lift and boundaries are reflected, so
the map is a quasi-isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R] (a : R) (K : ChainComplex (ModuleCat.{u} R) ℕ)

@[reassoc (attr := simp)]
theorem scalar_quotientProjection (n : ℕ) :
    ModuleCat.ofHom (LinearMap.lsmul R (K.X n) a) ≫ (quotientProjection a K).f n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (quotientProjection_eq_zero_iff a K n (a • x)).mpr ⟨x, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- The actual augmentation from a one-element tensor to the degreewise scalar quotient. -/
noncomputable def tensorAugmentation :
    HomologicalComplex.tensorObj (singleComplex R a) K ⟶ quotientComplex a K where
  f n := singleTensorπZero a K n ≫ (quotientProjection a K).f n
  comm' i j h := by
    have hij : j + 1 = i := h
    subst i
    rw [Category.assoc, (quotientProjection a K).comm,
      ← Category.assoc _ (singleTensorπZero a K j), singleTensor_d_πZero,
      Preadditive.add_comp]
    simp

@[reassoc (attr := simp)]
theorem singleTensorιZero_tensorAugmentation (n : ℕ) :
    singleTensorιZero a K n ≫ (tensorAugmentation a K).f n =
      (quotientProjection a K).f n := by
  simp [tensorAugmentation, ← Category.assoc]

@[reassoc (attr := simp)]
theorem singleTensorιOne_tensorAugmentation (n : ℕ) :
    singleTensorιOne a K n ≫ (tensorAugmentation a K).f (n + 1) = 0 := by
  simp [tensorAugmentation, ← Category.assoc]


@[simp]
theorem tensorAugmentation_apply (n : ℕ)
    (x : (HomologicalComplex.tensorObj (singleComplex R a) K).X n) :
    (tensorAugmentation a K).f n x =
      (quotientProjection a K).f n (singleTensorπZero a K n x) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- A quotient cycle lifts to a genuine cycle in the two-column tensor. -/
theorem tensorAugmentation_lift_cycle
    (ha : ∀ n, IsSMulRegular (K.X n) a) (n : ℕ)
    (y : (quotientComplex a K).X (n + 1))
    (hy : (quotientComplex a K).d (n + 1) n y = 0) :
    ∃ x : (HomologicalComplex.tensorObj (singleComplex R a) K).X (n + 1),
      (HomologicalComplex.tensorObj (singleComplex R a) K).d (n + 1) n x = 0 ∧
        (tensorAugmentation a K).f (n + 1) x = y := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (scalarRange a K (n + 1)) y
  obtain ⟨z, hz⟩ := (quotientProjection_eq_zero_iff a K n (K.d (n + 1) n x)).mp hy
  refine ⟨singleTensorιZero a K (n + 1) x - singleTensorιOne a K n z, ?_, ?_⟩
  · cases n with
    | zero =>
      apply singleTensor_ext_zero a K
      simp [hz]
    | succ n =>
      have hd : K.d (n + 1) n z = 0 := by
        apply ha n
        change a • K.d (n + 1) n z = a • (0 : K.X n)
        rw [smul_zero]
        calc
          a • K.d (n + 1) n z = K.d (n + 1) n (a • z) :=
            ((K.d (n + 1) n).hom.map_smul a z).symm
          _ = K.d (n + 1) n (K.d (n + 2) (n + 1) x) := congrArg (K.d (n + 1) n) hz
          _ = 0 := ConcreteCategory.congr_hom (K.d_comp_d (n + 2) (n + 1) n) x
      apply singleTensor_ext a K n
      · simp [hz]
      · simp [hd]
  · simp

set_option backward.isDefEq.respectTransparency false in
/-- A cycle mapping to a quotient boundary is already a tensor boundary. -/
theorem tensorAugmentation_reflect_boundary
    (ha : ∀ n, IsSMulRegular (K.X n) a) (n : ℕ)
    (z : (HomologicalComplex.tensorObj (singleComplex R a) K).X n)
    (hz : (HomologicalComplex.tensorObj (singleComplex R a) K).d n (n - 1) z = 0)
    (y : (quotientComplex a K).X (n + 1))
    (hy : (quotientComplex a K).d (n + 1) n y = (tensorAugmentation a K).f n z) :
    ∃ w : (HomologicalComplex.tensorObj (singleComplex R a) K).X (n + 1),
      (HomologicalComplex.tensorObj (singleComplex R a) K).d (n + 1) n w = z := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (scalarRange a K (n + 1)) y
  have hq : (quotientProjection a K).f n
      (singleTensorπZero a K n z - K.d (n + 1) n x) = 0 := by
    change (quotientProjection a K).f n (K.d (n + 1) n x) =
      (quotientProjection a K).f n (singleTensorπZero a K n z) at hy
    rw [map_sub, hy, sub_self]
  obtain ⟨t, ht⟩ := (quotientProjection_eq_zero_iff a K n _).mp hq
  refine ⟨singleTensorιZero a K (n + 1) x + singleTensorιOne a K n t, ?_⟩
  cases n with
  | zero =>
    apply singleTensor_ext_zero a K
    simp only [singleTensorπZero_d_apply, map_add, singleTensorπZero_ιZero_apply,
      singleTensorπZero_ιOne_apply, singleTensorπOne_ιZero_apply,
      singleTensorπOne_ιOne_apply]
    simp only [add_zero, zero_add, map_zero, smul_zero]
    rw [ht]
    abel
  | succ n =>
    have hc : K.d (n + 1) n (singleTensorπZero a K (n + 1) z) +
        a • singleTensorπOne a K n z = 0 := by
      have h := congrArg (singleTensorπZero a K n) hz
      simpa using h
    have he : -(K.d (n + 1) n t) = singleTensorπOne a K n z := by
      apply ha n
      change a • (-(K.d (n + 1) n t)) = a • singleTensorπOne a K n z
      rw [smul_neg, ← (K.d (n + 1) n).hom.map_smul, ht, map_sub]
      have hdd : K.d (n + 1) n (K.d (n + 2) (n + 1) x) = 0 :=
        ConcreteCategory.congr_hom (K.d_comp_d (n + 2) (n + 1) n) x
      rw [hdd, sub_zero]
      exact neg_eq_iff_add_eq_zero.mpr hc
    apply singleTensor_ext a K n
    · simp only [singleTensorπZero_d_apply, map_add, singleTensorπZero_ιZero_apply,
        singleTensorπZero_ιOne_apply, singleTensorπOne_ιZero_apply,
        singleTensorπOne_ιOne_apply]
      simp only [add_zero, zero_add, map_zero, smul_zero]
      rw [ht]
      abel
    · simpa using he

set_option backward.isDefEq.respectTransparency false in
/-- Termwise regular multiplication makes the actual tensor augmentation a quasi-isomorphism. -/
theorem tensorAugmentation_quasiIso_of_regular
    (ha : ∀ n, IsSMulRegular (K.X n) a) : QuasiIso (tensorAugmentation a K) := by
  constructor
  intro n
  rw [quasiIsoAt_iff' _ (n + 1) n (n - 1) (by simp) (by cases n <;> simp)]
  apply ShortComplex.quasiIso_of_liftCycles_of_reflectBoundaries
  · intro y hy
    cases n with
    | zero =>
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (scalarRange a K 0) y
      refine ⟨singleTensorιZero a K 0 x, ?_, ?_⟩
      · change (HomologicalComplex.tensorObj (singleComplex R a) K).d 0 0 _ = 0
        rw [(HomologicalComplex.tensorObj (singleComplex R a) K).shape _ _ (by simp)]
        rfl
      · change (tensorAugmentation a K).f 0 (singleTensorιZero a K 0 x) = _
        simp
    | succ n => exact tensorAugmentation_lift_cycle a K ha n y hy
  · intro z hz h
    obtain ⟨y, hy⟩ := h
    exact tensorAugmentation_reflect_boundary a K ha n z hz y hy

end ChainComplex.Koszul
