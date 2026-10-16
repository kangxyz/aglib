/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import Aglib.Algebra.Homology.CochainComplex.Cycles
public import Aglib.Algebra.Homology.MappingCone.Acyclicity
public import Aglib.Algebra.Homology.MappingCone.ShortExact
public import Aglib.RingTheory.Flat.Exact
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Pi

/-!
# Arbitrary scalar extension of bounded-above acyclic flat complexes

The native short exact cycle sequences prove flatness of the actual cycles
by descending induction from the strict upper term bound. Tensoring those
original sequences then proves exactness of the original differential pair
after every module tensor product. Consequently every ring scalar extension
of the original acyclic complex is acyclic. No flatness of the ring map or
Noetherian hypothesis is needed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- Actual cycles above which a bounded-above flat complex is exact are
flat, by descent through the original short exact cycle sequences. -/
theorem flat_cycles_of_exact_above (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (b n : ℤ) [K.IsStrictlyLE b] [∀ i, Module.Flat R (K.X i)]
    (h : ∀ i, n < i → K.ExactAt i) : Module.Flat R (K.cycles n) := by
  let b' := max b n
  let : K.IsStrictlyLE b' := K.isStrictlyLE_of_le b b' (le_max_left _ _)
  have hb : Module.Flat R (K.cycles (b' + 1)) := by
    have hz : IsZero (K.cycles (b' + 1)) := IsZero.of_mono (K.iCycles (b' + 1))
      (K.isZero_of_isStrictlyLE b' (b' + 1) (by omega))
    let := ModuleCat.subsingleton_of_isZero hz
    infer_instance
  have hd : ∀ i, i ≤ b' + 1 → n ≤ i → Module.Flat R (K.cycles i) :=
    Int.leInductionDown (motive := fun i _ => n ≤ i → Module.Flat R (K.cycles i))
      (fun _ => hb) (fun i hi ih hni => by
        let j := i - 1
        let S := ShortComplex.mk (K.iCycles j) (K.toCycles j (j + 1)) (by
          rw [← cancel_mono (K.iCycles (j + 1)), Category.assoc, toCycles_i,
            iCycles_d, zero_comp])
        have hS : S.ShortExact := K.shortExact_cycles j (h (j + 1) (by dsimp [j]; omega))
        let : Module.Flat R S.X₃ := by
          change Module.Flat R (K.cycles (j + 1))
          rw [show j + 1 = i by dsimp [j]; omega]
          exact ih (by omega)
        let : Module.Flat R S.X₂ := inferInstanceAs (Module.Flat R (K.X j))
        let := Module.Flat.ker_of_surjective S.g.hom hS.moduleCat_surjective_g
        let : Module.Flat R (ModuleCat.kernelCone S.g).pt := by
          change Module.Flat R (LinearMap.ker S.g.hom)
          infer_instance
        let e := hS.fIsKernel.conePointUniqueUpToIso (ModuleCat.kernelIsLimit S.g)
        exact Module.Flat.of_linearEquiv e.toLinearEquiv)
  exact hd n (by dsimp [b']; omega) le_rfl

/-- Good truncation of a bounded-above flat complex above whose cutoff the
original homology vanishes has flat terms, including its actual boundary. -/
theorem flat_truncLE_X_of_exact_above (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (b n : ℤ) [K.IsStrictlyLE b] [∀ i, Module.Flat R (K.X i)]
    (h : ∀ i, n < i → K.ExactAt i) (q : ℤ) :
    Module.Flat R ((K.truncLE n).X q) := by
  obtain hq | hq | hq := lt_trichotomy q n
  · exact Module.Flat.of_linearEquiv (K.truncLEXIso n q hq).toLinearEquiv
  · subst q
    let := K.flat_cycles_of_exact_above b n h
    exact Module.Flat.of_linearEquiv (K.truncLEXIsoCycles n).toLinearEquiv
  · let := ModuleCat.subsingleton_of_isZero ((K.truncLE n).isZero_of_isStrictlyLE n q hq)
    infer_instance

/-- Tensoring the literal differential pair of a bounded-above acyclic
flat complex with any module remains exact. The cycle flatness is proved
from the upper bound, not assumed as a separate family. -/
theorem universally_lTensor_exact_of_acyclic
    (K : CochainComplex (ModuleCat.{v} R) ℤ) (b : ℤ)
    [K.IsStrictlyLE b] [∀ i, Module.Flat R (K.X i)] (hK : K.Acyclic)
    (i : ℤ) (N : Type w) [AddCommGroup N] [Module R N] :
    Function.Exact ((K.d (i - 1) i).hom.lTensor N)
      ((K.d i (i + 1)).hom.lTensor N) := by
  let (j : ℤ) : Module.Flat R (K.cycles j) :=
    K.flat_cycles_of_exact_above b j (fun k _ => hK k)
  have h₀ := K.shortExact_cycles (i - 1) (by simpa only [sub_add_cancel] using hK i)
  have h₁ := K.shortExact_cycles i (hK (i + 1))
  have h₂ := K.shortExact_cycles (i + 1) (hK ((i + 1) + 1))
  have hE : Function.Exact ((K.iCycles i).hom.lTensor N)
      ((K.toCycles i (i + 1)).hom.lTensor N) :=
    lTensor_exact N
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp h₁.exact)
      h₁.moduleCat_surjective_g
  have hsurj : Function.Surjective ((K.toCycles (i - 1) i).hom.lTensor N) := by
    apply LinearMap.lTensor_surjective N
    have hsurj₀ : Function.Surjective (K.toCycles (i - 1) ((i - 1) + 1)).hom :=
      h₀.moduleCat_surjective_g
    rw [show (i - 1) + 1 = i by omega] at hsurj₀
    exact hsurj₀
  have hinj : Function.Injective ((K.iCycles (i + 1)).hom.lTensor N) :=
    LinearMap.lTensor_injective_of_exact_of_flat (K.toCycles (i + 1) ((i + 1) + 1)).hom
      h₂.moduleCat_surjective_g (K.iCycles (i + 1)).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp h₂.exact) N
  have hprev : (K.d (i - 1) i).hom =
      (K.iCycles i).hom.comp (K.toCycles (i - 1) i).hom := by
    exact congrArg (fun f => f.hom) (K.toCycles_i (i - 1) i).symm
  have hnext : (K.d i (i + 1)).hom =
      (K.iCycles (i + 1)).hom.comp (K.toCycles i (i + 1)).hom := by
    exact congrArg (fun f => f.hom) (K.toCycles_i i (i + 1)).symm
  rw [hprev, hnext, LinearMap.lTensor_comp, LinearMap.lTensor_comp]
  exact hinj.comp_exact_iff_exact.mpr (hsurj.comp_exact_iff_exact.mpr hE)

/-- Every native ring scalar extension of a bounded-above acyclic flat
complex is acyclic, with the original mapped differentials. -/
theorem acyclic_extendScalars_of_flat {B : Type w} [CommRing B] (σ : R →+* B)
    (K : CochainComplex (ModuleCat.{v} R) ℤ) (b : ℤ)
    [K.IsStrictlyLE b] [∀ i, Module.Flat R (K.X i)] (hK : K.Acyclic) :
    (((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj K).Acyclic := by
  let N := (ModuleCat.restrictScalars σ).obj (ModuleCat.of B B)
  intro i
  apply (exactAt_iff' _ (i - 1) i (i + 1) (by simp) (by simp)).mpr
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  exact K.universally_lTensor_exact_of_acyclic b hK i N

/-- Every term of an original signed cone of flat module complexes is flat.
The native cone comparison is with the actual two endpoint terms. -/
theorem flat_X_mappingCone {K L : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : K ⟶ L) [∀ i, Module.Flat R (K.X i)] [∀ i, Module.Flat R (L.X i)]
    (n : ℤ) : Module.Flat R ((mappingCone f).X n) := by
  let T : Fin 2 → ModuleCat.{v} R := ![K.X (n + 1), L.X n]
  let (j : Fin 2) : Module.Flat R (T j) := by
    fin_cases j <;> dsimp [T] <;> infer_instance
  let e : (Π₀ j, T j) ≃ₗ[R] (K.X (n + 1) × L.X n) :=
    (DFinsupp.linearEquivFunOnFintype (R := R)).trans
      (LinearEquiv.piFinTwo R (fun j => T j))
  have hP : Module.Flat R (K.X (n + 1) × L.X n) :=
    (Module.Flat.equiv_iff e).mp inferInstance
  exact (Module.Flat.equiv_iff
    (mappingConeTermIso f n ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv).mpr hP

/-- The literal scalar-extended map of a quasi-isomorphism between
bounded-above flat module complexes remains a quasi-isomorphism after
every ring map. No flatness of the ring map, lower bound or Noetherianity
is needed. The proof tensors the original acyclic flat cone. -/
theorem quasiIso_extendScalars_of_flat {B : Type w} [CommRing B] (σ : R →+* B)
    {K L : CochainComplex (ModuleCat.{v} R) ℤ} (f : K ⟶ L)
    (a b : ℤ) [K.IsStrictlyLE a] [L.IsStrictlyLE b]
    [∀ i, Module.Flat R (K.X i)] [∀ i, Module.Flat R (L.X i)] [QuasiIso f] :
    QuasiIso (((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).map f) := by
  let (i : ℤ) : Module.Flat R ((mappingCone f).X i) := flat_X_mappingCone f i
  let : (mappingCone f).IsStrictlyLE (max a b) := by
    rw [isStrictlyLE_iff]
    intro i hi
    apply (mappingCone.isZero_X_iff f i).mpr
    exact ⟨K.isZero_of_isStrictlyLE a (i + 1) (by omega),
      L.isZero_of_isStrictlyLE b i (by omega)⟩
  have h := acyclic_extendScalars_of_flat σ (mappingCone f) (max a b)
    (mappingCone_acyclic_of_quasiIso f)
  apply quasiIso_of_mappingCone_acyclic
  intro i
  exact (h i).of_iso (mappingCone.mapHomologicalComplexIso f (ModuleCat.extendScalars σ))

end CochainComplex
