/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# Etale maps from the original differential coordinates

A bijective original Kähler base-change map, together with formal smoothness
of the target over the original base, makes the intermediate map formally
etale. The native Jacobi-Zariski arrows prove both required vanishing
statements.

In particular, a displayed basis `b i = D(x i)` makes the ORIGINAL
`MvPolynomial.aeval x` formally etale. For finite coordinate type and a
smooth target, that same map is etale. Its scalar-extension action is the
original aeval action, and its Kähler comparison uses the original
`mapBaseChange`, polynomial differential basis and base-changed basis.
Rings and coordinate types have independent universes. No field,
Noetherian, nontriviality, or public Fintype choice is required; empty
coordinate types and zero rings are included.
-/

@[expose] public section
noncomputable section
open KaehlerDifferential TensorProduct

namespace Algebra.FormallyEtale

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- The original Jacobi-Zariski maps detect formal etaleness of the intermediate map. -/
theorem of_bijective_mapBaseChange [Algebra.FormallySmooth R T]
    (h : Function.Bijective (KaehlerDifferential.mapBaseChange R S T)) :
    Algebra.FormallyEtale S T := by
  have hd (x : Ω[T⁄S]) : x = 0 := by
    obtain ⟨y, rfl⟩ := KaehlerDifferential.map_surjective R S T x
    obtain ⟨z, rfl⟩ := h.2 y
    exact (KaehlerDifferential.exact_mapBaseChange_map R S T).apply_apply_eq_zero z
  have hδ (x : Algebra.H1Cotangent S T) : Algebra.H1Cotangent.δ R S T x = 0 := by
    apply h.1
    simpa only [map_zero] using
      (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T).apply_apply_eq_zero x
  have hh (x : Algebra.H1Cotangent S T) : x = 0 := by
    obtain ⟨y, hy⟩ := (Algebra.H1Cotangent.exact_map_δ R S T x).mp (hδ x)
    calc
      x = Algebra.H1Cotangent.map R S T T y := hy.symm
      _ = Algebra.H1Cotangent.map R S T T 0 := congrArg _ (Subsingleton.elim y 0)
      _ = 0 := map_zero _
  exact ⟨⟨fun x y => (hd x).trans (hd y).symm⟩,
    ⟨fun x y => (hh x).trans (hh y).symm⟩⟩

end Algebra.FormallyEtale

namespace MvPolynomial

variable {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]

/-- The actual aeval map is formally etale in its displayed differential basis. -/
theorem formallyEtale_aeval_of_basis {I : Type*} [Algebra.FormallySmooth R T]
    (x : I → T) (b : Module.Basis I T Ω[T⁄R]) (hb : ∀ i, b i = D R T (x i)) :
    (MvPolynomial.aeval x : MvPolynomial I R →ₐ[R] T).toRingHom.FormallyEtale := by
  let P := MvPolynomial I R
  let φ : P →ₐ[R] T := MvPolynomial.aeval x
  let : Algebra P T := φ.toRingHom.toAlgebra
  let : IsScalarTower R P T := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let bP := (KaehlerDifferential.mvPolynomialBasis R I).baseChange T
  have hm : KaehlerDifferential.mapBaseChange R P T =
      (bP.equiv b (Equiv.refl I)).toLinearMap := by
    apply bP.ext
    intro i
    simp only [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply]
    simp only [bP, Module.Basis.baseChange_apply, KaehlerDifferential.mvPolynomialBasis_apply]
    change KaehlerDifferential.mapBaseChange R P T
      (1 ⊗ₜ[P] D R P (MvPolynomial.X i)) = b i
    rw [mapBaseChange_tmul, one_smul, map_D]
    change D R T ((MvPolynomial.aeval x) (MvPolynomial.X i)) = b i
    rw [MvPolynomial.aeval_X]
    exact (hb i).symm
  change Algebra.FormallyEtale P T
  apply Algebra.FormallyEtale.of_bijective_mapBaseChange (R := R)
  rw [hm]
  exact (bP.equiv b (Equiv.refl I)).bijective

/-- The same original finite coordinate map is etale for a smooth target. -/
theorem etale_aeval_of_basis {I : Type*} [Finite I] [Algebra.Smooth R T]
    (x : I → T) (b : Module.Basis I T Ω[T⁄R]) (hb : ∀ i, b i = D R T (x i)) :
    (MvPolynomial.aeval x : MvPolynomial I R →ₐ[R] T).toRingHom.Etale := by
  let P := MvPolynomial I R
  let φ : P →ₐ[R] T := MvPolynomial.aeval x
  let : Algebra P T := φ.toRingHom.toAlgebra
  let : IsScalarTower R P T := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have hE : Algebra.FormallyEtale P T := formallyEtale_aeval_of_basis x b hb
  let : Algebra.FinitePresentation P T :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R P T
  exact ⟨hE, inferInstance⟩

end MvPolynomial
