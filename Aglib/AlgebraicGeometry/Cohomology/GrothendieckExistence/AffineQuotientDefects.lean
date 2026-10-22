/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineQuotient
public import Aglib.RingTheory.AdicCompletion.BoundedDefect
public import Aglib.LinearAlgebra.DefectIdealBound

/-! # Independent quotient bounds in original affine coordinates

The defining ideal of the quotient and the ideal bounding defects are
independent. The square of the original bound kills the reduced kernel;
the same square bounds the cokernel. No flatness assumption is made.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {B : CommRingCat.{u}} {M N : (Spec B).Modules}
  [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)

/-- Actual quotient coordinates intertwine the original coefficient map. -/
theorem affineQuotientEquiv_map (K : (Spec B).IdealSheafData) (n : ℕ)
    (x : moduleSpecΓFunctor.obj M ⧸
      (affineIdeal B K ^ n • (⊤ : Submodule B (moduleSpecΓFunctor.obj M)))) :
    moduleSpecΓFunctor.map ((idealSheafQuotientFunctor (Spec B) (K ^ n)).map f)
        (affineQuotientEquiv B K M n x) =
      affineQuotientEquiv B K N n
        (Submodule.mapQ
          (affineIdeal B K ^ n • (⊤ : Submodule B (moduleSpecΓFunctor.obj M)))
          (affineIdeal B K ^ n • (⊤ : Submodule B (moduleSpecΓFunctor.obj N)))
          (moduleSpecΓFunctor.map f).hom
          (Submodule.smul_top_le_comap_smul_top _ _) x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    rw [Submodule.mapQ_apply, affineQuotientEquiv_mk, affineQuotientEquiv_mk]
    have h := congrArg (fun g => moduleSpecΓFunctor.map g)
      ((idealSheafQuotientUnit (Spec B) (K ^ n)).naturality f)
    have hx := ConcreteCategory.congr_hom h x
    simpa only [Functor.id_map, Functor.map_comp, ConcreteCategory.comp_apply] using hx.symm

private theorem quotient_bounds_transport
    {R U V P Q : Type*} [CommRing R]
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (f : U →ₗ[R] V) (g : P →ₗ[R] Q) (J K : Ideal R) (t n : ℕ)
    (e : (U ⧸ (K ^ n • (⊤ : Submodule R U))) ≃ₗ[R] P)
    (d : (V ⧸ (K ^ n • (⊤ : Submodule R V))) ≃ₗ[R] Q)
    (h : ∀ x, g (e x) = d (Submodule.mapQ
      (K ^ n • (⊤ : Submodule R U)) (K ^ n • (⊤ : Submodule R V)) f
      (Submodule.smul_top_le_comap_smul_top _ _) x))
    (hk : J ^ t • f.ker = ⊥) (hc : J ^ t • (⊤ : Submodule R V) ≤ f.range) :
    J ^ (t * 2) • g.ker = ⊥ ∧ J ^ (t * 2) • (⊤ : Submodule R Q) ≤ g.range := by
  let q := Submodule.mapQ (K ^ n • (⊤ : Submodule R U))
    (K ^ n • (⊤ : Submodule R V)) f (Submodule.smul_top_le_comap_smul_top _ _)
  apply LinearMap.defectBounds_of_equiv q g e d h (J ^ (t * 2))
  · simpa only [pow_mul] using f.sq_smul_ker_mapQ_eq_bot (J ^ t) (K ^ n) hk hc
  · exact (Submodule.smul_mono
      (Ideal.pow_le_pow_right (show t ≤ t * 2 by omega)) le_rfl).trans
      (f.smul_top_le_range_mapQ (J ^ t) (K ^ n) hc)

private theorem quotient_bounds_of_comparisons
    {R : Type*} [CommRing R] {C : Type*} [Category C]
    (Γ : C ⥤ ModuleCat R) (Q : C ⥤ C) (η : 𝟭 C ⟶ Q) {M N : C} (f : M ⟶ N)
    (J K : Ideal R) (t n : ℕ)
    (e : {d : (Γ.obj M ⧸ (K ^ n • (⊤ : Submodule R (Γ.obj M)))) ≃ₗ[R]
        Γ.obj (Q.obj M) // ∀ x, d (Submodule.Quotient.mk x) = Γ.map (η.app M) x})
    (d : {d : (Γ.obj N ⧸ (K ^ n • (⊤ : Submodule R (Γ.obj N)))) ≃ₗ[R]
        Γ.obj (Q.obj N) // ∀ x, d (Submodule.Quotient.mk x) = Γ.map (η.app N) x})
    (hk : J ^ t • (Γ.map f).hom.ker = ⊥)
    (hc : J ^ t • (⊤ : Submodule R (Γ.obj N)) ≤ (Γ.map f).hom.range) :
    J ^ (t * 2) • (Γ.map (Q.map f)).hom.ker = ⊥ ∧
      J ^ (t * 2) • (⊤ : Submodule R (Γ.obj (Q.obj N))) ≤
        (Γ.map (Q.map f)).hom.range := by
  apply quotient_bounds_transport (Γ.map f).hom (Γ.map (Q.map f)).hom
    J K t n e.val d.val _ hk hc
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    rw [Submodule.mapQ_apply, e.property, d.property]
    have hh := congrArg (fun z => Γ.map z) (η.naturality f)
    have hx := ConcreteCategory.congr_hom hh x
    simpa only [Functor.id_map, Functor.map_comp, ConcreteCategory.comp_apply] using hx.symm

/-- A uniform original affine bound survives an independent quotient.
This statement concerns the actual section map, not a replacement quotient map. -/
theorem affineQuotient_sections_bounds (J K : (Spec B).IdealSheafData) (t n : ℕ)
    (hker : affineIdeal B J ^ t • (moduleSpecΓFunctor.map f).hom.ker = ⊥)
    (hcoker : affineIdeal B J ^ t • (⊤ : Submodule B (moduleSpecΓFunctor.obj N)) ≤
      (moduleSpecΓFunctor.map f).hom.range) :
    affineIdeal B J ^ (t * 2) •
        (moduleSpecΓFunctor.map ((idealSheafQuotientFunctor (Spec B) (K ^ n)).map f)).hom.ker =
      ⊥ ∧
    affineIdeal B J ^ (t * 2) •
        (⊤ : Submodule B (moduleSpecΓFunctor.obj
          ((idealSheafQuotientFunctor (Spec B) (K ^ n)).obj N))) ≤
      (moduleSpecΓFunctor.map ((idealSheafQuotientFunctor (Spec B) (K ^ n)).map f)).hom.range := by
  exact quotient_bounds_of_comparisons moduleSpecΓFunctor
    (idealSheafQuotientFunctor (Spec B) (K ^ n))
    (idealSheafQuotientUnit (Spec B) (K ^ n)) f
    (affineIdeal B J) (affineIdeal B K) t n
    (affineQuotientComparison B K M n) (affineQuotientComparison B K N n) hker hcoker

end AlgebraicGeometry.Scheme.Modules.Coherent
