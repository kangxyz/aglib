/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.FrobeniusKernel.Tower
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Generic finite etale representation of the original semilinear fixed kernel

A finite module over a Noetherian domain becomes free after a nonzero
localization. The actual coordinate algebra of its original scalar-extended
operator becomes finite after a second shrinking. Native localization
composition identifies the unchanged twice-localized ring as one nonzero
principal localization of the original base, with its original structural map.
The basis is internal to the proof. The conclusion retains a natural Hom/fixed
point equivalence on the original tensor modules, including zero test algebras.
This is the algebraic representation theorem, not a scheme/sheaf comparison.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Module

namespace Algebra.FrobeniusKernel

universe u v w

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
  {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
  (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
  (Φ : M →ₛₗ[RingHom.frobeniusOfPrimeCastEqZero p hp hA] M)

/-- After one actual nonzero principal localization, the fixed kernel of the
original semilinear operator is naturally represented by a finite etale algebra.
All test-algebra actions are the supplied compatible actions; no basis or
alternate module model occurs in the conclusion. -/
theorem exists_finite_etale_fixedRepresentative_and_free :
    ∃ (r : A), r ≠ 0 ∧
      ∃ (R : Type u) (_ : CommRing R) (_ : Algebra A R) (_ : IsLocalization.Away r R)
        (C : Type u) (_ : CommRing C) (_ : Algebra R C),
        Module.Free R (R ⊗[A] M) ∧ Module.Finite R C ∧ Algebra.Etale R C ∧
        ∃ e : ∀ (S : Type w) [CommRing S] [Algebra A S] [Algebra R S]
          [IsScalarTower A R S], (C →ₐ[R] S) ≃
            {z : S ⊗[A] M // LinearMap.frobeniusBaseChange p hp hA Φ S z = z},
          ∀ (S T : Type w) [CommRing S] [CommRing T] [Algebra A S] [Algebra A T]
            [Algebra R S] [Algebra R T] [IsScalarTower A R S] [IsScalarTower A R T]
            (f : S →ₐ[R] T) (h : C →ₐ[R] S),
            (e T (f.comp h)).val =
              _root_.TensorProduct.map (f.restrictScalars A).toLinearMap LinearMap.id
                (e S h).val := by
  obtain ⟨a, ha, hfree⟩ :=
    Module.Finite.exists_free_localizedModule_away_of_isNoetherianRing (A := A) M
  let R₀ := Localization.Away a
  let M₀ := R₀ ⊗[A] M
  let : IsDomain R₀ := Localization.Away.isDomain ha
  let := hfree
  let : Module.Free R₀ M₀ :=
    Module.free_of_isLocalizedModule_of_free_isLocalizedModule (Submonoid.powers a) R₀
      (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
      (_root_.TensorProduct.mk A R₀ M 1)
  let b := (Module.Free.chooseBasis R₀ M₀).reindex
    (Fintype.equivFin (Module.Free.ChooseBasisIndex R₀ M₀))
  let hR₀ := LinearMap.primeCast_eq_zero_baseChange p hA R₀
  let Φ₀ := LinearMap.frobeniusBaseChange p hp hA Φ R₀
  obtain ⟨s, hs, hfinite, hetale⟩ :=
    exists_ne_zero_finite_etale_baseChange p hp hR₀ Φ₀ b
  let R := Localization.Away s
  let C := R ⊗[R₀] CoordinateAlgebra p (coefficientMatrix p hp hR₀ Φ₀ b)
  let : Module.Free R (R ⊗[A] M) :=
    Module.Free.of_equiv
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A R₀ R R M)
  let c := (IsLocalization.Away.sec a s).1
  have hassoc : Associated (algebraMap A R₀ c) s :=
    IsLocalization.Away.associated_sec_fst a s
  have hc : c ≠ 0 := by
    intro h
    apply hs
    exact hassoc.eq_zero_iff.mp (by rw [h, map_zero])
  have hloc : IsLocalization.Away (a * c) R :=
    IsLocalization.Away.mul_of_associated a c s hassoc
  let e : ∀ (S : Type w) [CommRing S] [Algebra A S] [Algebra R S]
      [IsScalarTower A R S], (C →ₐ[R] S) ≃
        {z : S ⊗[A] M // LinearMap.frobeniusBaseChange p hp hA Φ S z = z} := by
    intro S _ _ _ _
    let : Algebra R₀ S := Algebra.compHom S (algebraMap R₀ R)
    let : IsScalarTower R₀ R S :=
      IsScalarTower.of_algebraMap_eq (R := R₀) (S := R) (A := S) fun _ => rfl
    let : IsScalarTower A R₀ S :=
      IsScalarTower.of_algebraMap_eq (R := A) (S := R₀) (A := S) fun x => by
        change algebraMap A S x = algebraMap R S (algebraMap R₀ R (algebraMap A R₀ x))
        rw [← IsScalarTower.algebraMap_apply A R₀ R, ← IsScalarTower.algebraMap_apply A R S]
    exact homIteratedBaseChangeEquivFixed p hp hA Φ R₀ b R S
  refine ⟨a * c, mul_ne_zero ha hc, R, inferInstance, inferInstance, hloc,
    C, inferInstance, inferInstance, inferInstance, hfinite, hetale, e, ?_⟩
  intro S T _ _ _ _ _ _ _ _ f h
  let : Algebra R₀ S := Algebra.compHom S (algebraMap R₀ R)
  let : Algebra R₀ T := Algebra.compHom T (algebraMap R₀ R)
  let : IsScalarTower R₀ R S :=
      IsScalarTower.of_algebraMap_eq (R := R₀) (S := R) (A := S) fun _ => rfl
  let : IsScalarTower R₀ R T :=
    IsScalarTower.of_algebraMap_eq (R := R₀) (S := R) (A := T) fun _ => rfl
  let : IsScalarTower A R₀ S :=
      IsScalarTower.of_algebraMap_eq (R := A) (S := R₀) (A := S) fun x => by
        change algebraMap A S x = algebraMap R S (algebraMap R₀ R (algebraMap A R₀ x))
        rw [← IsScalarTower.algebraMap_apply A R₀ R, ← IsScalarTower.algebraMap_apply A R S]
  let : IsScalarTower A R₀ T :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := R₀) (A := T) fun x => by
      change algebraMap A T x = algebraMap R T (algebraMap R₀ R (algebraMap A R₀ x))
      rw [← IsScalarTower.algebraMap_apply A R₀ R, ← IsScalarTower.algebraMap_apply A R T]
  exact homIteratedBaseChangeEquivFixed_naturality p hp hA Φ R₀ b R f h

/-- Forget only the retained freeness witness from the complete generic
representation construction. The representative, localization and maps are unchanged. -/
theorem exists_finite_etale_fixedRepresentative :
    ∃ (r : A), r ≠ 0 ∧
      ∃ (R : Type u) (_ : CommRing R) (_ : Algebra A R) (_ : IsLocalization.Away r R)
        (C : Type u) (_ : CommRing C) (_ : Algebra R C),
        Module.Finite R C ∧ Algebra.Etale R C ∧
        ∃ e : ∀ (S : Type w) [CommRing S] [Algebra A S] [Algebra R S]
          [IsScalarTower A R S], (C →ₐ[R] S) ≃
            {z : S ⊗[A] M // LinearMap.frobeniusBaseChange p hp hA Φ S z = z},
          ∀ (S T : Type w) [CommRing S] [CommRing T] [Algebra A S] [Algebra A T]
            [Algebra R S] [Algebra R T] [IsScalarTower A R S] [IsScalarTower A R T]
            (f : S →ₐ[R] T) (h : C →ₐ[R] S),
            (e T (f.comp h)).val =
              _root_.TensorProduct.map (f.restrictScalars A).toLinearMap LinearMap.id
                (e S h).val := by
  obtain ⟨r, hr, R, hR, hAR, hloc, C, hC, hRC, _, hfinite, hetale, e, he⟩ :=
    exists_finite_etale_fixedRepresentative_and_free p hp hA Φ
  exact ⟨r, hr, R, hR, hAR, hloc, C, hC, hRC, hfinite, hetale, e, he⟩

end Algebra.FrobeniusKernel
