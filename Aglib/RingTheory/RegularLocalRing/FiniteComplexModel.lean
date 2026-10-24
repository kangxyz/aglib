/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.MinimalFiniteFreeResolution
public import Aglib.RingTheory.RegularLocalRing.FiniteProjectiveDimension
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import Mathlib.RingTheory.Finiteness.Small

/-!
# Actual finite-projective models of finite modules

Over a regular Noetherian local ring of finite dimension d, every finite
module in the chosen carrier universe has a finite-projective cochain
model of its native single in degree n, supported in [n-d,n]. The map is
the original finite-resolution augmentation, transported through the
native Shrink and ULift linear equivalences and the native single shift.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v

namespace IsRegularLocalRing

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- Shrink the actual finite module, resolve it in the ring universe, and
lift the original augmentation back to the chosen carrier universe. -/
theorem exists_finiteProjective_single_zero_model
    (d : ℕ) (hd : ringKrullDim R = (d : ℕ))
    (M : ModuleCat.{max u v} R) [Module.Finite R M] :
    ∃ P : CochainComplex (ModuleCat.{max u v} R) ℤ,
      P.IsStrictlyGE (-(d : ℤ)) ∧ P.IsStrictlyLE 0 ∧
      (∀ i, Module.Finite R (P.X i)) ∧
      (∀ i, Module.Projective R (P.X i)) ∧
      ∃ q : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj M,
        QuasiIso q := by
  let : Small.{u} M := Module.Finite.small (R := R) (M := M)
  let M₀ : ModuleCat.{u} R := ModuleCat.of R (Shrink.{u} M)
  let : Module.Finite R M₀ := inferInstance
  let : HasProjectiveDimensionLE M₀ d :=
    (projectiveDimension_le_iff M₀ d).mp (projectiveDimension_le_dimension d R hd M₀)
  obtain ⟨Q, hQfinite, _, hQzero, _⟩ :=
    ModuleCat.exists_minimal_finite_free_resolution M₀ d
  let (i : ℕ) : Module.Finite R (Q.complex.X i) := hQfinite i
  have hfinite (i : ℤ) : Module.Finite R (Q.cochainComplex.X i) := by
    by_cases hi : i ≤ 0
    · obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat hi
      exact Module.Finite.equiv (Q.cochainComplexXIso (-k) k).symm.toLinearEquiv
    · let := ModuleCat.subsingleton_of_isZero
        (Q.cochainComplex.isZero_of_isStrictlyLE 0 i (by omega))
      infer_instance
  let (i : ℤ) : Module.Finite R (Q.cochainComplex.X i) := hfinite i
  let (i : ℤ) : Module.Projective R (Q.cochainComplex.X i) := inferInstance
  have hge : Q.cochainComplex.IsStrictlyGE (-(d : ℤ)) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat (show i ≤ 0 by omega)
    exact IsZero.of_iso (hQzero k (by omega)) (Q.cochainComplexXIso (-k) k)
  let : Q.cochainComplex.IsStrictlyGE (-(d : ℤ)) := hge
  let F : ModuleCat.{u} R ⥤ ModuleCat.{max u v} R :=
    ModuleCat.uliftFunctor.{v, u, u} R
  let P : CochainComplex (ModuleCat.{max u v} R) ℤ :=
    (F.mapHomologicalComplex (.up ℤ)).obj Q.cochainComplex
  let eM : F.obj M₀ ≅ M :=
    ((show F.obj M₀ ≃ₗ[R] M₀ from ULift.moduleEquiv).trans
      (Shrink.linearEquiv R M)).toModuleIso
  let q : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj M :=
    (F.mapHomologicalComplex (.up ℤ)).map Q.π' ≫
      (F.mapCochainComplexSingleFunctor 0).hom.app M₀ ≫
      (CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).map eM.hom
  refine ⟨P, inferInstance, inferInstance, ?_, ?_, q, inferInstance⟩
  · intro i
    exact Module.Finite.equiv
      (show Q.cochainComplex.X i ≃ₗ[R] P.X i from ULift.moduleEquiv.symm)
  · intro i
    exact Module.Projective.of_equiv'
      (show Q.cochainComplex.X i ≃ₗ[R] P.X i from ULift.moduleEquiv.symm)

/-- The model uses the native universal single/shift comparison; single n
means placement in degree n and the resolution bounds are [n-d,n]. -/
theorem exists_finiteProjective_single_model
    (d : ℕ) (hd : ringKrullDim R = (d : ℕ))
    (M : ModuleCat.{max u v} R) [Module.Finite R M] (n : ℤ) :
    ∃ P : CochainComplex (ModuleCat.{max u v} R) ℤ,
      P.IsStrictlyGE (n - d) ∧ P.IsStrictlyLE n ∧
      (∀ i, Module.Finite R (P.X i)) ∧
      (∀ i, Module.Projective R (P.X i)) ∧
      ∃ q : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{max u v} R) n).obj M,
        QuasiIso q := by
  obtain ⟨P, hge, hle, hf, hp, q, hq⟩ :=
    exists_finiteProjective_single_zero_model d hd M
  let : P.IsStrictlyGE (-(d : ℤ)) := hge
  let : P.IsStrictlyLE 0 := hle
  let (i : ℤ) : Module.Finite R (P.X i) := hf i
  let (i : ℤ) : Module.Projective R (P.X i) := hp i
  let : QuasiIso q := hq
  let e := ((CochainComplex.singleFunctors (ModuleCat.{max u v} R)).shiftIso
    (-n) n 0 (neg_add_cancel n)).app M
  refine ⟨P⟦-n⟧,
    CochainComplex.isStrictlyGE_shift P (-(d : ℤ)) (-n) (n - d) (by omega),
    CochainComplex.isStrictlyLE_shift P 0 (-n) n (by omega),
    fun i => Module.Finite.equiv
      (P.shiftFunctorObjXIso (-n) i (i + (-n)) rfl).symm.toLinearEquiv,
    fun i => Module.Projective.of_equiv'
      (P.shiftFunctorObjXIso (-n) i (i + (-n)) rfl).symm.toLinearEquiv,
    q⟦-n⟧' ≫ e.hom, inferInstance⟩

end IsRegularLocalRing
