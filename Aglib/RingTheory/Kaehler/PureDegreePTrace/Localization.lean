/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kaehler.PureDegreePTrace.IntegralClosure
public import Aglib.RingTheory.IntegralClosure.Localization
public import Aglib.RingTheory.Reflexive.EvaluationLocalization
public import Aglib.RingTheory.Reflexive.DoubleDualFraction.Uniqueness

/-!
# Localization of the original integral differential trace

The original scalar-extension inclusion of integral closures localizes the
raw trace. The target map is the native twice-dual localization map. Its
generic comparison follows from original evaluation, so the same original
field differential trace proves naturality without another height-one proof.
-/

@[expose] public noncomputable section

open Polynomial
open scoped nonZeroDivisors

attribute [local instance 2000] Algebra.toSMul

universe uΛ uA uD uK uL uM uMs uN uNs

private theorem IsLocalizedModule.mapExtendScalars_eq_of_comp
    {R : Type uA} [CommSemiring R] (U : Submonoid R)
    (D : Type uD) [CommSemiring D] [Algebra R D] [IsLocalization U D]
    {M : Type uM} [AddCommMonoid M] [Module R M]
    {Mₛ : Type uMs} [AddCommMonoid Mₛ] [Module R Mₛ]
    [Module D Mₛ] [IsScalarTower R D Mₛ]
    {N : Type uN} [AddCommMonoid N] [Module R N]
    {Nₛ : Type uNs} [AddCommMonoid Nₛ] [Module R Nₛ]
    [Module D Nₛ] [IsScalarTower R D Nₛ]
    (q : M →ₗ[R] Mₛ) [IsLocalizedModule U q]
    (δ : N →ₗ[R] Nₛ) [IsLocalizedModule U δ]
    (f : M →ₗ[R] N) (g : Mₛ →ₗ[D] Nₛ)
    (hcomp : δ.comp f = (g.restrictScalars R).comp q) :
    IsLocalizedModule.mapExtendScalars U q δ D f = g := by
  apply LinearMap.restrictScalars_injective R
  apply IsLocalizedModule.linearMap_ext U q δ
  change (IsLocalizedModule.map U q δ f).comp q = (g.restrictScalars R).comp q
  exact (IsLocalizedModule.map_comp U q δ f).trans hcomp

namespace KaehlerDifferential

section BidualLocalization

variable (Λ : Type uΛ) (A : Type uA) (D : Type uD)
  [CommRing Λ] [CommRing A] [IsNoetherianRing A]
  [CommRing D] [Algebra Λ A] [Algebra Λ D] [Algebra A D]
  [IsScalarTower Λ A D] (U : Submonoid A) [IsLocalization U D]
  (r : ℕ) [Module.Finite A (⋀[A]^r (KaehlerDifferential Λ A))]

private theorem traceExteriorDual_finitePresentation :
    Module.FinitePresentation A
      (Module.Dual A (⋀[A]^r (KaehlerDifferential Λ A))) := by
  let M := ⋀[A]^r (KaehlerDifferential Λ A)
  let : IsNoetherian A (Module.Dual A M) := isNoetherian_linearMap A A M
  let : Module.Finite A (Module.Dual A M) := Module.IsNoetherian.finite A _
  exact Module.finitePresentation_of_finite A _

/-- The original exterior module's twice-native dual localization map. -/
def mapExteriorBidualLocalization :
    Module.Dual A (Module.Dual A (⋀[A]^r (KaehlerDifferential Λ A))) →ₗ[A]
      Module.Dual D (Module.Dual D (⋀[D]^r (KaehlerDifferential Λ D))) := by
  let m := mapExterior Λ A D r
  let : IsLocalizedModule U m := mapExterior_isLocalizedModule Λ A D U r
  let : Module.FinitePresentation A (⋀[A]^r (KaehlerDifferential Λ A)) :=
    Module.finitePresentation_of_finite A _
  exact IsLocalizedModule.mapExtendScalars U
    (IsLocalizedModule.mapExtendScalars U m (Algebra.linearMap A D) D)
    (Algebra.linearMap A D) D

/-- The whole original bidual localization map is its two native scalar-extension maps. -/
theorem mapExteriorBidualLocalization_eq_twice :
    let m := mapExterior Λ A D r
    letI : IsLocalizedModule U m := mapExterior_isLocalizedModule Λ A D U r
    letI : Module.FinitePresentation A (⋀[A]^r (KaehlerDifferential Λ A)) :=
      Module.finitePresentation_of_finite A _
    mapExteriorBidualLocalization Λ A D U r =
      IsLocalizedModule.mapExtendScalars U
        (IsLocalizedModule.mapExtendScalars U m (Algebra.linearMap A D) D)
        (Algebra.linearMap A D) D := rfl

/-- The complete function of the original bidual localization is its two native dual maps. -/
theorem mapExteriorBidualLocalization_coe_eq_twice :
    let m := mapExterior Λ A D r
    letI : IsLocalizedModule U m := mapExterior_isLocalizedModule Λ A D U r
    letI : Module.FinitePresentation A (⋀[A]^r (KaehlerDifferential Λ A)) :=
      Module.finitePresentation_of_finite A _
    DFunLike.coe (mapExteriorBidualLocalization Λ A D U r) =
      DFunLike.coe (IsLocalizedModule.mapExtendScalars U
        (IsLocalizedModule.mapExtendScalars U m (Algebra.linearMap A D) D)
        (Algebra.linearMap A D) D) :=
  congrArg DFunLike.coe (mapExteriorBidualLocalization_eq_twice Λ A D U r)

/-- The actual twice-dual exterior map is a localization of the original bidual. -/
theorem mapExteriorBidualLocalization_isLocalizedModule :
    IsLocalizedModule U (mapExteriorBidualLocalization Λ A D U r) := by
  let m := mapExterior Λ A D r
  let : IsLocalizedModule U m := mapExterior_isLocalizedModule Λ A D U r
  let : Module.FinitePresentation A (⋀[A]^r (KaehlerDifferential Λ A)) :=
    Module.finitePresentation_of_finite A _
  let : Module.FinitePresentation A
      (Module.Dual A (⋀[A]^r (KaehlerDifferential Λ A))) :=
    traceExteriorDual_finitePresentation Λ A r
  exact Module.FinitePresentation.isLocalizedModule_mapExtendScalars _ _ _ _

private theorem mapExteriorBidualLocalization_eval
    (v : ⋀[A]^r (KaehlerDifferential Λ A)) :
    mapExteriorBidualLocalization Λ A D U r (Module.Dual.eval A _ v) =
      Module.Dual.eval D _ (mapExterior Λ A D r v) := by
  let m := mapExterior Λ A D r
  let : IsLocalizedModule U m := mapExterior_isLocalizedModule Λ A D U r
  let : Module.FinitePresentation A (⋀[A]^r (KaehlerDifferential Λ A)) :=
    Module.finitePresentation_of_finite A _
  let : Module.FinitePresentation A
      (Module.Dual A (⋀[A]^r (KaehlerDifferential Λ A))) :=
    traceExteriorDual_finitePresentation Λ A r
  have he := LinearMap.congr_fun (Module.Dual.localized_eval_eq U D m) (m v)
  rw [IsLocalizedModule.map_apply] at he
  exact he

end BidualLocalization

section GenericComparison

variable (Λ : Type uΛ) (A : Type uA) (D : Type uD) (K : Type uK)
  [CommRing Λ] [CommRing A] [IsNoetherianRing A]
  [CommRing D] [IsNoetherianRing D] [Field K]
  [Algebra Λ A] [Algebra Λ D] [Algebra Λ K]
  [Algebra A D] [Algebra A K] [Algebra D K]
  [IsScalarTower Λ A D] [IsScalarTower Λ A K] [IsScalarTower Λ D K]
  [IsScalarTower A D K] [IsFractionRing A K] [IsFractionRing D K]
  (U : Submonoid A) [IsLocalization U D] (n : ℕ)
  [Module.Finite A (⋀[A]^(n + 1) (KaehlerDifferential Λ A))]
  [Module.Finite D (⋀[D]^(n + 1) (KaehlerDifferential Λ D))]

/-- The original bidual localization retains its original fraction-field coordinate. -/
theorem mapExteriorBidualLocalization_generic :
    letI : Module.FinitePresentation A (⋀[A]^(n + 1) (KaehlerDifferential Λ A)) :=
      Module.finitePresentation_of_finite A _
    letI : Module.FinitePresentation D (⋀[D]^(n + 1) (KaehlerDifferential Λ D)) :=
      Module.finitePresentation_of_finite D _
    letI : IsLocalizedModule A⁰ (mapExterior Λ A K (n + 1)) :=
      mapExterior_isLocalizedModule Λ A K A⁰ (n + 1)
    letI : IsLocalizedModule D⁰ (mapExterior Λ D K (n + 1)) :=
      mapExterior_isLocalizedModule Λ D K D⁰ (n + 1)
    letI := finiteExteriorAtFraction Λ A K n
    ((Module.Dual.doubleDualToFraction (K := K)
      (mapExterior Λ D K (n + 1))).restrictScalars A).comp
        (mapExteriorBidualLocalization Λ A D U (n + 1)) =
      Module.Dual.doubleDualToFraction (K := K) (mapExterior Λ A K (n + 1)) := by
  let : Module.FinitePresentation A (⋀[A]^(n + 1) (KaehlerDifferential Λ A)) :=
    Module.finitePresentation_of_finite A _
  let : Module.FinitePresentation D (⋀[D]^(n + 1) (KaehlerDifferential Λ D)) :=
    Module.finitePresentation_of_finite D _
  let : IsLocalizedModule A⁰ (mapExterior Λ A K (n + 1)) :=
    mapExterior_isLocalizedModule Λ A K A⁰ (n + 1)
  let : IsLocalizedModule D⁰ (mapExterior Λ D K (n + 1)) :=
    mapExterior_isLocalizedModule Λ D K D⁰ (n + 1)
  let := finiteExteriorAtFraction Λ A K n
  apply Module.Dual.doubleDualToFraction_unique (K := K) (mapExterior Λ A K (n + 1))
  intro v
  change Module.Dual.doubleDualToFraction (K := K) (mapExterior Λ D K (n + 1))
    (mapExteriorBidualLocalization Λ A D U (n + 1) (Module.Dual.eval A _ v)) = _
  rw [mapExteriorBidualLocalization_eval, Module.Dual.doubleDualToFraction_eval]
  exact mapExterior_tower_apply Λ A D K (n + 1) v

end GenericComparison

section OriginalTrace

variable (Λ : Type uΛ) (A : Type uA) (K : Type uK) (L : Type uL)
  [CommRing Λ] [CommRing A] [IsDomain A]
  [IsNoetherianRing A] [IsIntegrallyClosed A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [Algebra Λ A] [Algebra Λ K] [Algebra Λ L]
  [IsScalarTower Λ A K] [IsScalarTower Λ A L] [IsScalarTower Λ K L]
  [IsPurelyInseparable K L] [Module.Finite A (integralClosure A L)]
  {p : ℕ} [Fact p.Prime] [CharP K p] {a : K}
  (n : ℕ) [Module.Finite A (⋀[A]^(n + 1) (KaehlerDifferential Λ A))]
  (D : Type uD) [CommRing D] [Algebra A D]
  (U : Submonoid A) [IsLocalization U D] (hU : U ≤ A⁰)
  [Algebra D K] [IsScalarTower A D K]

local notation "B" => integralClosure A L
local notation "M" => (⋀[A]^(n + 1) (KaehlerDifferential Λ A))

section CompatibleActions

variable [Algebra Λ D] [Algebra D L]
  [IsScalarTower Λ A D] [IsScalarTower A D L]
  [IsScalarTower Λ D K] [IsScalarTower Λ D L] [IsScalarTower D K L]
  [IsDomain D] [IsNoetherianRing D] [IsIntegrallyClosed D] [IsFractionRing D K]
  [FiniteDimensional K L] [Module.Finite D (integralClosure D L)]
  [Module.Finite D (⋀[D]^(n + 1) (KaehlerDifferential Λ D))]

private theorem integralClosureRawTrace_localization_comp_aux
    (hdegree : Module.finrank K L = p)
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a)) :
    letI := integralClosure.scalarExtensionAlgebra A D L
    letI := integralClosure.scalarExtension_isScalarTower_base A D L
    letI := integralClosure.scalarExtension_isScalarTower_ambient A D L
    letI : IsScalarTower Λ B (integralClosure D L) :=
      IsScalarTower.of_algebraMap_eq fun _ => by
        apply Subtype.ext
        rfl
    (mapExteriorBidualLocalization Λ A D U (n + 1)).comp
        (integralClosureRawTrace Λ A K L n hdegree h) =
      ((integralClosureRawTrace Λ D K L n hdegree h).restrictScalars A).comp
        ((mapExterior Λ B (integralClosure D L) (n + 1)).restrictScalars A) := by
  let := integralClosure.scalarExtensionAlgebra A D L
  let := integralClosure.scalarExtension_isScalarTower_base A D L
  let := integralClosure.scalarExtension_isScalarTower_ambient A D L
  let : IsScalarTower Λ B (integralClosure D L) :=
    IsScalarTower.of_algebraMap_eq fun _ => by
      apply Subtype.ext
      rfl
  let : Module.FinitePresentation A M := Module.finitePresentation_of_finite A _
  let : Module.FinitePresentation D (⋀[D]^(n + 1) (KaehlerDifferential Λ D)) :=
    Module.finitePresentation_of_finite D _
  let : IsLocalizedModule A⁰ (mapExterior Λ A K (n + 1)) :=
    mapExterior_isLocalizedModule Λ A K A⁰ (n + 1)
  let : IsLocalizedModule D⁰ (mapExterior Λ D K (n + 1)) :=
    mapExterior_isLocalizedModule Λ D K D⁰ (n + 1)
  let := finiteExteriorAtFraction Λ A K n
  apply LinearMap.ext
  intro ω
  apply Module.Dual.doubleDualToFraction_injective (K := K) (mapExterior Λ D K (n + 1))
  change Module.Dual.doubleDualToFraction (K := K) (mapExterior Λ D K (n + 1))
      (mapExteriorBidualLocalization Λ A D U (n + 1)
        (integralClosureRawTrace Λ A K L n hdegree h ω)) =
    Module.Dual.doubleDualToFraction (K := K) (mapExterior Λ D K (n + 1))
      (integralClosureRawTrace Λ D K L n hdegree h
        (mapExterior Λ B (integralClosure D L) (n + 1) ω))
  have hgeneric := LinearMap.congr_fun
    (mapExteriorBidualLocalization_generic Λ A D K U n)
    (integralClosureRawTrace Λ A K L n hdegree h ω)
  change Module.Dual.doubleDualToFraction (K := K) (mapExterior Λ D K (n + 1))
      (mapExteriorBidualLocalization Λ A D U (n + 1)
        (integralClosureRawTrace Λ A K L n hdegree h ω)) =
    Module.Dual.doubleDualToFraction (K := K) (mapExterior Λ A K (n + 1))
      (integralClosureRawTrace Λ A K L n hdegree h ω) at hgeneric
  rw [hgeneric]
  rw [integralClosureRawTrace_generic, integralClosureRawTrace_generic,
    integralClosureRawTraceAtFraction_apply, integralClosureRawTraceAtFraction_apply,
    mapExterior_tower_apply]

private theorem integralClosureRawTrace_localization_aux
    (hdegree : Module.finrank K L = p)
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a)) :
    letI := integralClosure.scalarExtensionAlgebra A D L
    letI := integralClosure.scalarExtension_isScalarTower_base A D L
    letI := integralClosure.scalarExtension_isScalarTower_ambient A D L
    letI : IsScalarTower Λ B (integralClosure D L) :=
      IsScalarTower.of_algebraMap_eq fun _ => by
        apply Subtype.ext
        rfl
    letI := integralClosure.scalarExtension_isLocalization A D L U
    letI : IsLocalizedModule (Algebra.algebraMapSubmonoid B U)
        (mapExterior Λ B (integralClosure D L) (n + 1)) :=
      mapExterior_isLocalizedModule Λ B (integralClosure D L)
        (Algebra.algebraMapSubmonoid B U) (n + 1)
    letI : IsLocalizedModule U
        ((mapExterior Λ B (integralClosure D L) (n + 1)).restrictScalars A) :=
      IsLocalizedModule.restrictScalars U (mapExterior Λ B (integralClosure D L) (n + 1))
    letI : IsLocalizedModule U (mapExteriorBidualLocalization Λ A D U (n + 1)) :=
      mapExteriorBidualLocalization_isLocalizedModule Λ A D U (n + 1)
    IsLocalizedModule.mapExtendScalars U
        ((mapExterior Λ B (integralClosure D L) (n + 1)).restrictScalars A)
        (mapExteriorBidualLocalization Λ A D U (n + 1)) D
        (integralClosureRawTrace Λ A K L n hdegree h) =
      integralClosureRawTrace Λ D K L n hdegree h := by
  let := integralClosure.scalarExtensionAlgebra A D L
  let := integralClosure.scalarExtension_isScalarTower_base A D L
  let := integralClosure.scalarExtension_isScalarTower_ambient A D L
  let : IsScalarTower Λ B (integralClosure D L) :=
    IsScalarTower.of_algebraMap_eq fun _ => by
      apply Subtype.ext
      rfl
  let := integralClosure.scalarExtension_isLocalization A D L U
  let : IsLocalizedModule (Algebra.algebraMapSubmonoid B U)
      (mapExterior Λ B (integralClosure D L) (n + 1)) :=
    mapExterior_isLocalizedModule Λ B (integralClosure D L)
      (Algebra.algebraMapSubmonoid B U) (n + 1)
  let q := (mapExterior Λ B (integralClosure D L) (n + 1)).restrictScalars A
  let : IsLocalizedModule U q :=
    IsLocalizedModule.restrictScalars U (mapExterior Λ B (integralClosure D L) (n + 1))
  let : IsLocalizedModule U (mapExteriorBidualLocalization Λ A D U (n + 1)) :=
    mapExteriorBidualLocalization_isLocalizedModule Λ A D U (n + 1)
  exact IsLocalizedModule.mapExtendScalars_eq_of_comp U D q
    (mapExteriorBidualLocalization Λ A D U (n + 1))
    (integralClosureRawTrace Λ A K L n hdegree h)
    (integralClosureRawTrace Λ D K L n hdegree h)
    (integralClosureRawTrace_localization_comp_aux Λ A K L n D U hdegree h)

end CompatibleActions

/-- The original integral raw trace commutes with the actual localization of
both exterior forms and their bidual. Localized normality and finiteness are
derived; the original fields, degree and root presentation are unchanged. -/
theorem integralClosureRawTrace_localization_comp
    (hdegree : Module.finrank K L = p)
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a)) :
    letI : FiniteDimensional K L := FiniteDimensional.of_finrank_pos
      (by rw [hdegree]; exact (Fact.out : p.Prime).pos)
    letI : Algebra D L := ((algebraMap K L).comp (algebraMap D K)).toAlgebra
    letI : IsScalarTower D K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    letI : IsScalarTower A D L := IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap A L x = algebraMap K L (algebraMap D K (algebraMap A D x))
      rw [← IsScalarTower.algebraMap_apply A D K]
      exact IsScalarTower.algebraMap_apply A K L x
    letI : Algebra Λ D := ((algebraMap A D).comp (algebraMap Λ A)).toAlgebra
    letI : IsScalarTower Λ A D := IsScalarTower.of_algebraMap_eq fun _ => rfl
    letI : IsScalarTower Λ D K := IsScalarTower.to₁₃₄ Λ A D K
    letI : IsScalarTower Λ D L := IsScalarTower.to₁₂₄ Λ D K L
    letI : IsDomain D := IsLocalization.isDomain_of_le_nonZeroDivisors D hU
    letI : IsNoetherianRing D := IsLocalization.isNoetherianRing U D inferInstance
    letI : IsIntegrallyClosed D := isIntegrallyClosed_of_isLocalization D U hU
    letI : IsFractionRing D K :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization U D K
    letI := integralClosure.scalarExtensionAlgebra A D L
    letI := integralClosure.scalarExtension_isScalarTower_base A D L
    letI := integralClosure.scalarExtension_isScalarTower_ambient A D L
    letI : IsScalarTower Λ B (integralClosure D L) :=
      IsScalarTower.of_algebraMap_eq fun _ => by
        apply Subtype.ext
        rfl
    letI : IsLocalizedModule U (integralClosure.scalarExtensionHom A D L).toLinearMap :=
      integralClosure.scalarExtensionHom_isLocalizedModule A D L U
    letI : Module.Finite D (integralClosure D L) :=
      Module.Finite.of_isLocalizedModule U (integralClosure.scalarExtensionHom A D L).toLinearMap
    letI : IsLocalizedModule U (mapExterior Λ A D (n + 1)) :=
      mapExterior_isLocalizedModule Λ A D U (n + 1)
    letI : Module.Finite D (⋀[D]^(n + 1) (KaehlerDifferential Λ D)) :=
      Module.Finite.of_isLocalizedModule U (mapExterior Λ A D (n + 1))
    (mapExteriorBidualLocalization Λ A D U (n + 1)).comp
        (integralClosureRawTrace Λ A K L n hdegree h) =
      ((integralClosureRawTrace Λ D K L n hdegree h).restrictScalars A).comp
        ((mapExterior Λ B (integralClosure D L) (n + 1)).restrictScalars A) := by
  let : FiniteDimensional K L := FiniteDimensional.of_finrank_pos
    (by rw [hdegree]; exact (Fact.out : p.Prime).pos)
  let : Algebra D L := ((algebraMap K L).comp (algebraMap D K)).toAlgebra
  let : IsScalarTower D K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower A D L := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap A L x = algebraMap K L (algebraMap D K (algebraMap A D x))
    rw [← IsScalarTower.algebraMap_apply A D K]
    exact IsScalarTower.algebraMap_apply A K L x
  let : Algebra Λ D := ((algebraMap A D).comp (algebraMap Λ A)).toAlgebra
  let : IsScalarTower Λ A D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower Λ D K := IsScalarTower.to₁₃₄ Λ A D K
  let : IsScalarTower Λ D L := IsScalarTower.to₁₂₄ Λ D K L
  let : IsDomain D := IsLocalization.isDomain_of_le_nonZeroDivisors D hU
  let : IsNoetherianRing D := IsLocalization.isNoetherianRing U D inferInstance
  let : IsIntegrallyClosed D := isIntegrallyClosed_of_isLocalization D U hU
  let : IsFractionRing D K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization U D K
  let := integralClosure.scalarExtensionAlgebra A D L
  let := integralClosure.scalarExtension_isScalarTower_base A D L
  let := integralClosure.scalarExtension_isScalarTower_ambient A D L
  let : IsScalarTower Λ B (integralClosure D L) :=
    IsScalarTower.of_algebraMap_eq fun _ => by
      apply Subtype.ext
      rfl
  let : IsLocalizedModule U (integralClosure.scalarExtensionHom A D L).toLinearMap :=
    integralClosure.scalarExtensionHom_isLocalizedModule A D L U
  let : Module.Finite D (integralClosure D L) :=
    Module.Finite.of_isLocalizedModule U (integralClosure.scalarExtensionHom A D L).toLinearMap
  let : IsLocalizedModule U (mapExterior Λ A D (n + 1)) :=
    mapExterior_isLocalizedModule Λ A D U (n + 1)
  let : Module.Finite D (⋀[D]^(n + 1) (KaehlerDifferential Λ D)) :=
    Module.Finite.of_isLocalizedModule U (mapExterior Λ A D (n + 1))
  exact integralClosureRawTrace_localization_comp_aux Λ A K L n D U hdegree h

/-- On the original localized integral closure, the raw trace is the native
localized linear map along the original exterior and twice-dual maps. -/
theorem integralClosureRawTrace_localization
    (hdegree : Module.finrank K L = p)
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a)) :
    letI : FiniteDimensional K L := FiniteDimensional.of_finrank_pos
      (by rw [hdegree]; exact (Fact.out : p.Prime).pos)
    letI : Algebra D L := ((algebraMap K L).comp (algebraMap D K)).toAlgebra
    letI : IsScalarTower D K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    letI : IsScalarTower A D L := IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap A L x = algebraMap K L (algebraMap D K (algebraMap A D x))
      rw [← IsScalarTower.algebraMap_apply A D K]
      exact IsScalarTower.algebraMap_apply A K L x
    letI : Algebra Λ D := ((algebraMap A D).comp (algebraMap Λ A)).toAlgebra
    letI : IsScalarTower Λ A D := IsScalarTower.of_algebraMap_eq fun _ => rfl
    letI : IsScalarTower Λ D K := IsScalarTower.to₁₃₄ Λ A D K
    letI : IsScalarTower Λ D L := IsScalarTower.to₁₂₄ Λ D K L
    letI : IsDomain D := IsLocalization.isDomain_of_le_nonZeroDivisors D hU
    letI : IsNoetherianRing D := IsLocalization.isNoetherianRing U D inferInstance
    letI : IsIntegrallyClosed D := isIntegrallyClosed_of_isLocalization D U hU
    letI : IsFractionRing D K :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization U D K
    letI := integralClosure.scalarExtensionAlgebra A D L
    letI := integralClosure.scalarExtension_isScalarTower_base A D L
    letI := integralClosure.scalarExtension_isScalarTower_ambient A D L
    letI : IsScalarTower Λ B (integralClosure D L) :=
      IsScalarTower.of_algebraMap_eq fun _ => by
        apply Subtype.ext
        rfl
    letI : IsLocalizedModule U (integralClosure.scalarExtensionHom A D L).toLinearMap :=
      integralClosure.scalarExtensionHom_isLocalizedModule A D L U
    letI : Module.Finite D (integralClosure D L) :=
      Module.Finite.of_isLocalizedModule U (integralClosure.scalarExtensionHom A D L).toLinearMap
    letI : IsLocalizedModule U (mapExterior Λ A D (n + 1)) :=
      mapExterior_isLocalizedModule Λ A D U (n + 1)
    letI : Module.Finite D (⋀[D]^(n + 1) (KaehlerDifferential Λ D)) :=
      Module.Finite.of_isLocalizedModule U (mapExterior Λ A D (n + 1))
    letI := integralClosure.scalarExtension_isLocalization A D L U
    letI : IsLocalizedModule (Algebra.algebraMapSubmonoid B U)
        (mapExterior Λ B (integralClosure D L) (n + 1)) :=
      mapExterior_isLocalizedModule Λ B (integralClosure D L)
        (Algebra.algebraMapSubmonoid B U) (n + 1)
    letI : IsLocalizedModule U
        ((mapExterior Λ B (integralClosure D L) (n + 1)).restrictScalars A) :=
      IsLocalizedModule.restrictScalars U (mapExterior Λ B (integralClosure D L) (n + 1))
    letI : IsLocalizedModule U (mapExteriorBidualLocalization Λ A D U (n + 1)) :=
      mapExteriorBidualLocalization_isLocalizedModule Λ A D U (n + 1)
    IsLocalizedModule.mapExtendScalars U
        ((mapExterior Λ B (integralClosure D L) (n + 1)).restrictScalars A)
        (mapExteriorBidualLocalization Λ A D U (n + 1)) D
        (integralClosureRawTrace Λ A K L n hdegree h) =
      integralClosureRawTrace Λ D K L n hdegree h := by
  let : FiniteDimensional K L := FiniteDimensional.of_finrank_pos
    (by rw [hdegree]; exact (Fact.out : p.Prime).pos)
  let : Algebra D L := ((algebraMap K L).comp (algebraMap D K)).toAlgebra
  let : IsScalarTower D K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower A D L := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap A L x = algebraMap K L (algebraMap D K (algebraMap A D x))
    rw [← IsScalarTower.algebraMap_apply A D K]
    exact IsScalarTower.algebraMap_apply A K L x
  let : Algebra Λ D := ((algebraMap A D).comp (algebraMap Λ A)).toAlgebra
  let : IsScalarTower Λ A D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower Λ D K := IsScalarTower.to₁₃₄ Λ A D K
  let : IsScalarTower Λ D L := IsScalarTower.to₁₂₄ Λ D K L
  let : IsDomain D := IsLocalization.isDomain_of_le_nonZeroDivisors D hU
  let : IsNoetherianRing D := IsLocalization.isNoetherianRing U D inferInstance
  let : IsIntegrallyClosed D := isIntegrallyClosed_of_isLocalization D U hU
  let : IsFractionRing D K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization U D K
  let := integralClosure.scalarExtensionAlgebra A D L
  let := integralClosure.scalarExtension_isScalarTower_base A D L
  let := integralClosure.scalarExtension_isScalarTower_ambient A D L
  let : IsScalarTower Λ B (integralClosure D L) :=
    IsScalarTower.of_algebraMap_eq fun _ => by
      apply Subtype.ext
      rfl
  let : IsLocalizedModule U (integralClosure.scalarExtensionHom A D L).toLinearMap :=
    integralClosure.scalarExtensionHom_isLocalizedModule A D L U
  let : Module.Finite D (integralClosure D L) :=
    Module.Finite.of_isLocalizedModule U (integralClosure.scalarExtensionHom A D L).toLinearMap
  let : IsLocalizedModule U (mapExterior Λ A D (n + 1)) :=
    mapExterior_isLocalizedModule Λ A D U (n + 1)
  let : Module.Finite D (⋀[D]^(n + 1) (KaehlerDifferential Λ D)) :=
    Module.Finite.of_isLocalizedModule U (mapExterior Λ A D (n + 1))
  let := integralClosure.scalarExtension_isLocalization A D L U
  let : IsLocalizedModule (Algebra.algebraMapSubmonoid B U)
      (mapExterior Λ B (integralClosure D L) (n + 1)) :=
    mapExterior_isLocalizedModule Λ B (integralClosure D L)
      (Algebra.algebraMapSubmonoid B U) (n + 1)
  let : IsLocalizedModule U
      ((mapExterior Λ B (integralClosure D L) (n + 1)).restrictScalars A) :=
    IsLocalizedModule.restrictScalars U (mapExterior Λ B (integralClosure D L) (n + 1))
  let : IsLocalizedModule U (mapExteriorBidualLocalization Λ A D U (n + 1)) :=
    mapExteriorBidualLocalization_isLocalizedModule Λ A D U (n + 1)
  exact integralClosureRawTrace_localization_aux Λ A K L n D U hdegree h

end OriginalTrace

end KaehlerDifferential
