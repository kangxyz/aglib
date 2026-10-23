/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Nagata.Basic
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Japanese and Nagata properties of finite algebras

Finite generation of the original algebra supplies finite degree of the
actual fraction-field extension. Japanese ascent then uses the same ambient
field and the literal integral-model comparison. Nagata ascent applies this
argument to every actual prime quotient and proves Noetherianity separately.

These results concern finite algebras, not arbitrary finite-type algebras.
All rings and fields lie in one ambient universe, with auxiliary test
universe zero.
-/

@[expose] public noncomputable section

universe u

/-- A finite injective domain algebra gives finite degree of the actual
fraction-field extension, under its supplied compatible coefficient maps. -/
theorem IsFractionRing.finite_of_finite_algebra
    (R S K L : Type u) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [Module.Finite R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra S L] [IsFractionRing S L] [Algebra R L]
    [IsScalarTower R S L] [Algebra K L] [IsScalarTower R K L] :
    FiniteDimensional K L := by
  let : Algebra.IsIntegral R S := inferInstance
  let : Algebra.IsAlgebraic R S :=
    ⟨fun s => (Algebra.IsIntegral.isIntegral (R := R) s).isAlgebraic⟩
  have hRL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  obtain ⟨s, hsfin, hs⟩ := Submodule.fg_def.mp
    (Module.finite_def.mp (inferInstance : Module.Finite R S))
  have hspan : (Ideal.span ({1} : Set S) : Set S) ⊆ Submodule.span R s := by
    intro z hz
    rw [hs]
    trivial
  have hfield := IsFractionRing.ideal_span_singleton_map_subset R
    (K := K) (L := L) (a := (1 : S)) (b := s) hRL hspan
  change Module.Finite K L
  rw [Module.finite_def, Submodule.fg_def]
  refine ⟨algebraMap S L '' s, hsfin.image _, eq_top_iff.mpr ?_⟩
  intro x hx
  exact hfield (by simp)

/-- Japanese ascent through a finite injective algebra of domains.
No normality of the upper domain or separability is assumed. -/
theorem IsJapaneseRing.of_finite
    {R S : Type u} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [Module.Finite R S] (h : IsJapaneseRing.{u, 0} R)
    (hinj : Function.Injective (algebraMap R S)) : IsJapaneseRing.{u, 0} S := by
  intro L hL hFL hSL hT hfin
  let K := FractionRing R
  let F := FractionRing S
  let : Module.IsTorsionFree R F := Module.isTorsionFree_iff_algebraMap_injective.mpr (by
    rw [IsScalarTower.algebraMap_eq R S F]
    exact (IsFractionRing.injective S F).comp hinj)
  let : Algebra K F := FractionRing.liftAlgebra R F
  let : IsScalarTower R K F := FractionRing.isScalarTower_liftAlgebra R F
  let : FiniteDimensional K F := IsFractionRing.finite_of_finite_algebra R S K F
  let : Algebra R L := ((algebraMap S L).comp (algebraMap R S)).toAlgebra
  let : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower R F L := IsScalarTower.to₁₃₄ R S F L
  let : Algebra K L := ((algebraMap F L).comp (algebraMap K F)).toAlgebra
  let : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower R K L := IsScalarTower.to₁₂₄ R K F L
  let : FiniteDimensional K L := Module.Finite.trans F L
  let : Algebra.IsIntegral R S := inferInstance
  let : Module.Finite R (integralClosure R L) := h.finite_integralClosure L
  let : Module.Finite R (integralClosure S L) :=
    Module.Finite.equiv (integralClosure.equivOfIntegral R S L).symm.toLinearEquiv
  exact Module.Finite.of_restrictScalars_finite R S (integralClosure S L)

/-- Every finite algebra of a Nagata ring is Nagata, by the actual finite
injective maps between its prime quotients. -/
theorem IsNagataRing.of_finite
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (h : IsNagataRing.{u, 0} R) : IsNagataRing.{u, 0} S := by
  let : IsNoetherianRing R := h.isNoetherianRing
  let : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  refine ⟨inferInstance, ?_⟩
  intro q hq
  let p : Ideal R := q.comap (algebraMap R S)
  let : p.IsPrime := inferInstance
  let : Algebra (R ⧸ p) (S ⧸ q) := inferInstance
  let : IsScalarTower R (R ⧸ p) (S ⧸ q) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Module.Finite R (S ⧸ q) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R q).toLinearMap
      Ideal.Quotient.mk_surjective
  let : Module.Finite (R ⧸ p) (S ⧸ q) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ p) (S ⧸ q)
  exact (h.isJapaneseRing_quotient p).of_finite
    (Ideal.algebraMap_quotient_injective (R := R) (I := q))

/-- Every actual quotient of a Nagata ring is Nagata. -/
theorem IsNagataRing.quotient
    {R : Type u} [CommRing R] (h : IsNagataRing.{u, 0} R) (I : Ideal R) :
    IsNagataRing.{u, 0} (R ⧸ I) :=
  h.of_finite
