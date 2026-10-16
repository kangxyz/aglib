/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Flat.PrincipalQuotient.BaseChange
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.RingTheory.Localization.Submodule

/-!
# Localization and local tests for regularity and quotient flatness

## Extraction basis

Transferred from `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FibrewiseRegularity.lean`
at frozen dirty R5Lab revision `79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`79621aa63046ca16c5f98424d77f16bc8cd45b99a84ddc8bc561fc8f9ccfe923`.
Source line ranges: 2589–2609, 2752–2796, 3180–3218.
The original rings, modules, canonical maps, universes and hypotheses are retained.
-/

@[expose] public section

noncomputable section
open TensorProduct LinearMap

namespace Algebra
open Module.Flat
section QuotientLocalization
variable {C W T : Type*} [CommRing C] [CommRing W] [CommRing T]
  [Algebra C W] [Algebra C T] [Algebra W T] [IsScalarTower C W T]

/-- Compatibility of the natural quotient map with the smaller coefficient base. -/
theorem quotientLocalization_isScalarTower (J : Ideal W) :
    IsScalarTower C (W ⧸ J) (T ⧸ J.map (algebraMap W T)) := by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change Ideal.Quotient.mk _ (algebraMap C T c) =
    Ideal.Quotient.mk _ (algebraMap W T (algebraMap C W c))
  rw [← IsScalarTower.algebraMap_apply C W T]

/-- Localization and quotient use the actual mapped ideal and denominator monoid. -/
theorem quotientLocalization_isLocalization
    (V : Submonoid W) [IsLocalization V T] (J : Ideal W) :
    IsLocalization (V.map (Ideal.Quotient.mk J)) (T ⧸ J.map (algebraMap W T)) := by
  change IsLocalization (Algebra.algebraMapSubmonoid (W ⧸ J) V)
    (T ⧸ J.map (algebraMap W T))
  infer_instance
end QuotientLocalization

end Algebra

namespace Algebra
open Module.Flat
section Localization
variable {R U V : Type*} [CommRing R] [CommRing U] [CommRing V]
  [Algebra R U] [Algebra R V] [Algebra U V] [IsScalarTower R U V]

/-- Regularity and base-flatness of a principal quotient persist under
localization of the algebra. -/
theorem regular_and_flat_localization (M : Submonoid U) [IsLocalization M V]
    (a : U) (ha : IsSMulRegular U a) [Module.Flat R (U ⧸ Ideal.span {a})] :
    IsSMulRegular V (algebraMap U V a) ∧
      Module.Flat R (V ⧸ Ideal.span {algebraMap U V a}) := by
  have : Module.Flat U V := IsLocalization.flat V M
  refine ⟨ha.of_flat, ?_⟩
  let J := Ideal.span {a}
  have : IsLocalization (M.map (Ideal.Quotient.mk J))
      (V ⧸ J.map (algebraMap U V)) := quotientLocalization_isLocalization M J
  have : IsScalarTower R (U ⧸ J) (V ⧸ J.map (algebraMap U V)) :=
    quotientLocalization_isScalarTower J
  have : Module.Flat (U ⧸ J) (V ⧸ J.map (algebraMap U V)) :=
    IsLocalization.flat _ (M.map (Ideal.Quotient.mk J))
  have hflat : Module.Flat R (V ⧸ J.map (algebraMap U V)) :=
    Module.Flat.trans R (U ⧸ J) _
  let e : (V ⧸ J.map (algebraMap U V)) ≃ₐ[R]
      (V ⧸ Ideal.span {algebraMap U V a}) :=
    Ideal.quotientEquivAlgOfEq R (by simp [J, Ideal.map_span])
  exact Module.Flat.of_linearEquiv e.symm.toLinearEquiv

end Localization

section Combined
variable {D R T V : Type*} [CommRing D] [CommRing R] [CommRing T] [CommRing V]
  [Algebra D R] [Algebra D T] [Algebra R V]
  [Algebra (R ⊗[D] T) V] [IsScalarTower R (R ⊗[D] T) V]

/-- Transport from the Noetherian local model all the way to a further
localization of its arbitrary scalar extension. -/
theorem regular_and_flat_baseChange_localization
    (M : Submonoid (R ⊗[D] T)) [IsLocalization M V]
    (a : T) (ha : IsSMulRegular T a) [Module.Flat D (T ⧸ Ideal.span {a})] :
    IsSMulRegular V (algebraMap (R ⊗[D] T) V ((1 : R) ⊗ₜ[D] a)) ∧
      Module.Flat R (V ⧸ Ideal.span {algebraMap (R ⊗[D] T) V ((1 : R) ⊗ₜ[D] a)}) := by
  obtain ⟨hreg, hflat⟩ := regular_and_flat_baseChange (D := D) (R := R) a ha
  let := hflat
  exact regular_and_flat_localization M ((1 : R) ⊗ₜ[D] a) hreg

end Combined

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Flatness of an actual ideal quotient can be tested at localizations of the
coefficient algebra, using the actual mapped ideals. -/
theorem flat_quotient_of_localized_maximal (I : Ideal S)
    (h : ∀ (q : Ideal S) [q.IsMaximal],
      Module.Flat R (Localization.AtPrime q ⧸ I.map (algebraMap S (Localization.AtPrime q)))) :
    Module.Flat R (S ⧸ I) := by
  let T (q : Ideal S) [q.IsMaximal] := Localization.AtPrime q
  let J (q : Ideal S) [q.IsMaximal] := I.localized' (T q) q.primeCompl (Algebra.linearMap S (T q))
  let Q (q : Ideal S) [q.IsMaximal] := T q ⧸ J q
  let j (q : Ideal S) [q.IsMaximal] : (S ⧸ I) →ₗ[S] Q q :=
    I.toLocalizedQuotient' (T q) q.primeCompl (Algebra.linearMap S (T q))
  apply Module.flat_of_isLocalized_maximal S (S ⧸ I) Q j
  intro q hq
  have hJ : J q = I.map (algebraMap S (T q)) := by
    simp only [J, Submodule.localized'_eq_span, Ideal.map, Ideal.span, Algebra.coe_linearMap]
  change Module.Flat R (T q ⧸ J q)
  rw [hJ]
  exact h q

/-- A regular equation in every actual local ring is globally regular. -/
theorem regular_of_localized_maximal (a : S)
    (h : ∀ (q : Ideal S) [q.IsMaximal],
      IsSMulRegular (Localization.AtPrime q) (algebraMap S (Localization.AtPrime q) a)) :
    IsSMulRegular S a := by
  let T (q : Ideal S) [q.IsMaximal] := Localization.AtPrime q
  let j (q : Ideal S) [q.IsMaximal] := Algebra.linearMap S (T q)
  apply injective_of_isLocalized_maximal T j T j (LinearMap.mulLeft S a)
  intro q hq
  have heq : IsLocalizedModule.map q.primeCompl (j q) (j q) (LinearMap.mulLeft S a) =
      LinearMap.mulLeft S (algebraMap S (T q) a) := by
    apply IsLocalizedModule.linearMap_ext q.primeCompl (j q) (j q)
    rw [IsLocalizedModule.map_comp]
    ext
    simp [j]
  rw [heq]
  exact h q

end Algebra
