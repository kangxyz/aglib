/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Aglib.Algebra.Homology.ModuleCat.LaurentModuleCech

/-!
# Finite homology and signed Laurent cokernels

Over a field, degreewise finiteness passes to actual homology and through a given
homotopy equivalence. The finite-projective Laurent model supplies the signed
cokernel of the original module difference map.

Source: `lean/R5Lab/Aglib/Algebra/Homology/ModuleCat/FiniteHomology.lean`.
Frozen R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `70e93920349206bb327ed40d52a10350143164892a965708df82f9242c82849b`.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v
namespace ModuleCat
variable {K : Type u} [Field K]
/-- A finite middle module has finite homology over a field. -/
theorem finite_shortComplex_homology (S : ShortComplex (ModuleCat.{v} K))
    [Module.Finite K S.X₂] : Module.Finite K S.homology := by
  have : Module.Finite K S.moduleCatLeftHomologyData.H := by
    change Module.Finite K (S.g.hom.ker ⧸ S.moduleCatToCycles.range)
    infer_instance
  exact Module.Finite.equiv S.moduleCatHomologyIso.toLinearEquiv.symm

/-- Homology in a finite degree of a complex over a field is finite. -/
theorem finite_complex_homology (P : CochainComplex (ModuleCat.{v} K) ℤ) (n : ℤ)
    [Module.Finite K (P.X n)] : Module.Finite K (P.homology n) :=
  by
    let : Module.Finite K (P.sc n).X₂ := inferInstanceAs (Module.Finite K (P.X n))
    exact finite_shortComplex_homology (P.sc n)

/-- Transfer degreewise finiteness through an actual homotopy equivalence. -/
theorem finite_homology_of_homotopyEquiv
    {P Q : CochainComplex (ModuleCat.{v} K) ℤ} (h : HomotopyEquiv P Q)
    (n : ℤ) [Module.Finite K (Q.X n)] : Module.Finite K (P.homology n) := by
  have : Module.Finite K (Q.homology n) := finite_complex_homology Q n
  exact Module.Finite.equiv (h.toHomologyIso n).toLinearEquiv.symm

variable {A B : ModuleCat.{v} K}
/-- The actual first homology of a two-term presentation is its signed cokernel. -/
def twoTermHomologyOneIsoCokernel (d : A ⟶ B)
    (P : CochainComplex (ModuleCat.{v} K) ℤ)
    (e₀ : A ≅ P.X 0) (e₁ : B ≅ P.X 1)
    (he : e₀.hom ≫ P.d 0 1 = d ≫ e₁.hom)
    (h₂ : IsZero (P.X 2)) : P.homology 1 ≅ cokernel d := by
  let e : P.homology 1 ≅ cokernel (P.d 0 1) :=
    P.isoHomologyι 1 2 (by simp) (h₂.eq_of_tgt _ _) ≪≫
      P.opcyclesIsoSc' 0 1 2 (by simp) (by simp) ≪≫
      (P.sc' 0 1 2).opcyclesIsoCokernel
  exact e ≪≫ (cokernel.mapIso d (P.d 0 1) e₀ e₁ he.symm).symm

open ModuleCat.LaurentCech LaurentPolynomial.Projector

/-- First homology of the original linear-map Cech complex. -/
def linearMapCechHomologyOneIsoCokernel
    {A B : Type v} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    (d : A →ₗ[K] B) :
    (linearMapCechComplex d).homology 1 ≅ cokernel (ModuleCat.ofHom d) :=
  twoTermHomologyOneIsoCokernel (ModuleCat.ofHom d) (linearMapCechComplex d)
    (linearMapCechSourceIso d) (linearMapCechTargetIso d)
    (linearMapCechSource_d d) (linearMapCechComplex_isZero_X d 2 (by decide) (by decide))

/-- A finite model gives finiteness of the original linear-map cokernel. -/
theorem finite_cokernel_of_cech_homotopyEquiv
    {A B : Type v} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    (d : A →ₗ[K] B) (P : CochainComplex (ModuleCat.{v} K) ℤ)
    (h : HomotopyEquiv (linearMapCechComplex d) P) [Module.Finite K (P.X 1)] :
    Module.Finite K (↑(cokernel (ModuleCat.ofHom d) : ModuleCat.{v} K)) := by
  have : Module.Finite K ((linearMapCechComplex d).homology 1) :=
    finite_homology_of_homotopyEquiv h 1
  exact Module.Finite.equiv (linearMapCechHomologyOneIsoCokernel d).toLinearEquiv

open Polynomial LaurentPolynomial ModuleCat

/-- Finite projective polynomial modules have a finite signed Laurent cokernel. -/
theorem moduleDifference_cokernel_finite
    (M N : ModuleCat.{u} K[X]) [Module.Finite K[X] M] [Module.Projective K[X] M]
    [Module.Finite K[X] N] [Module.Projective K[X] N]
    (e : (extendScalars (negativeScalarMap K)).obj N ≅
      (extendScalars (Polynomial.toLaurent (R := K))).obj M) :
    Module.Finite K
      (↑(cokernel (ModuleCat.ofHom (moduleDifference (R := K) M N e)) : ModuleCat.{u} K)) := by
  obtain ⟨P, _, hfin, ⟨h⟩⟩ := exists_moduleDifference_model_of_finite_projective M N e
  let : Module.Finite K (P.X 1) := (hfin 1).1
  exact finite_cokernel_of_cech_homotopyEquiv _ P h


end ModuleCat
