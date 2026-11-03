/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Excellent.RegularMap
public import Aglib.RingTheory.RegularLocalRing.Localization
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Bounded stability laws for actual regular maps

The source rings and residue-field tests remain in one explicit universe.
Finite-algebra base change and source/target localization are proved using
original residue towers and native tensor comparisons. These are regular-map
laws, not a claim of general finite-type stability of G-rings.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Algebra.IsRegularMap

/-- A quasi-finite residue tower provides legitimate finite residue-field
tests for the original regular map. All given coefficient actions are kept. -/
theorem regular_residueExtension_of_quasiFinite
    (R S B : Type u) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [Algebra.QuasiFinite R B]
    (h : Algebra.IsRegularMap R S) (q : Ideal B) [q.IsPrime]
    (E : Type u) [Field E] [Algebra R E] [Algebra B E]
    [IsScalarTower R B E] [Algebra q.ResidueField E]
    [IsScalarTower B q.ResidueField E] [FiniteDimensional q.ResidueField E] :
    IsRegularRing (S ⊗[R] E) := by
  let p := q.under R
  let : q.LiesOver p := ⟨rfl⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  let : Module.Finite p.ResidueField q.ResidueField := inferInstance
  let : IsScalarTower R q.ResidueField E := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R B E,
      IsScalarTower.algebraMap_apply R B q.ResidueField,
      ← IsScalarTower.algebraMap_apply B q.ResidueField E]
  let φ : p.ResidueField →ₐ[R] E :=
    (IsScalarTower.toAlgHom R q.ResidueField E).comp
      (IsScalarTower.toAlgHom R p.ResidueField q.ResidueField)
  let : Algebra p.ResidueField E := φ.toRingHom.toAlgebra
  let : IsScalarTower R p.ResidueField E := IsScalarTower.of_algHom φ
  let : IsScalarTower p.ResidueField q.ResidueField E :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : FiniteDimensional p.ResidueField E := Module.Finite.trans q.ResidueField E
  exact h.2 p E

/-- Finite algebra base change preserves the original regular-map tests.
The finite algebra and base source live in the same test universe. -/
theorem baseChange_of_finite
    (R S B : Type u) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [Module.Finite R B]
    (h : Algebra.IsRegularMap R S) : Algebra.IsRegularMap B (B ⊗[R] S) := by
  let : Module.Flat R S := h.1
  refine ⟨inferInstance, ?_⟩
  intro q hq E _ _ _ _ _
  let : Algebra R E := ((algebraMap B E).comp (algebraMap R B)).toAlgebra
  let : IsScalarTower R B E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsRegularRing (S ⊗[R] E) :=
    h.regular_residueExtension_of_quasiFinite R S B q E
  let e : ((B ⊗[R] S) ⊗[B] E) ≃+* S ⊗[R] E :=
    (Algebra.TensorProduct.comm B (B ⊗[R] S) E).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange R B B E S).toRingEquiv.trans
        (Algebra.TensorProduct.comm R E S).toRingEquiv)
  exact IsRegularRing.of_ringEquiv e.symm

/-- Localizing the target preserves regularity of an actual algebra map. -/
theorem localization_target
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (M : Submonoid S) [IsLocalization M T] (h : Algebra.IsRegularMap R S) :
    Algebra.IsRegularMap R T := by
  let : Module.Flat R S := h.1
  let : Module.Flat S T := IsLocalization.flat T M
  let : Module.Flat R T := Module.Flat.trans R S T
  refine ⟨inferInstance, ?_⟩
  intro p hp E _ _ _ _ _
  let : IsRegularRing (S ⊗[R] E) := h.2 p E
  let f : (S ⊗[R] E) →ₐ[R] T ⊗[R] E :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S T) (AlgHom.id R E)
  let : Algebra (S ⊗[R] E) (T ⊗[R] E) := f.toRingHom.toAlgebra
  let : IsScalarTower S (S ⊗[R] E) (T ⊗[R] E) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsLocalization (Algebra.algebraMapSubmonoid (S ⊗[R] E) M) (T ⊗[R] E) :=
    IsLocalization.tensorProduct_tensorProduct R E M T (by
      ext x
      change f (1 ⊗ₜ[R] x) = 1 ⊗ₜ[R] x
      simp [f])
  exact IsRegularRing.regular_localization (S ⊗[R] E) (T ⊗[R] E)
    (Algebra.algebraMapSubmonoid (S ⊗[R] E) M)

/-- If the original action extends to a localization of the source, a regular
map remains regular over that localization. No finite-type hypothesis is put
on the localization. -/
theorem localization_source
    (R B S : Type u) [CommRing R] [CommRing B] [CommRing S]
    [Algebra R B] [Algebra R S] [Algebra B S] [IsScalarTower R B S]
    (M : Submonoid R) [IsLocalization M B] (h : Algebra.IsRegularMap R S) :
    Algebra.IsRegularMap B S := by
  let : Module.Flat R S := h.1
  let : Module.Flat B S := (Module.flat_iff_of_isLocalization B M S).mpr inferInstance
  let : Algebra.QuasiFinite R B := Algebra.QuasiFinite.of_isLocalization M
  refine ⟨inferInstance, ?_⟩
  intro q hq E _ _ _ _ _
  let : Algebra R E := ((algebraMap B E).comp (algebraMap R B)).toAlgebra
  let : IsScalarTower R B E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsRegularRing (S ⊗[R] E) :=
    h.regular_residueExtension_of_quasiFinite R S B q E
  let e : (S ⊗[B] E) ≃ₐ[B] S ⊗[R] E := IsLocalization.algebraTensorEquiv M B S E
  exact IsRegularRing.of_ringEquiv e.toRingEquiv.symm

end Algebra.IsRegularMap
