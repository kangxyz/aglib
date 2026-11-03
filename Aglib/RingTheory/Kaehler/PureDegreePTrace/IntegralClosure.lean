/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kaehler.PureDegreePTrace.Field
public import Aglib.RingTheory.IntegralClosure.PureDegreePAtPrime
public import Aglib.RingTheory.IntegralClosure.FiniteEtale
public import Aglib.RingTheory.Nagata.Basic
public import Aglib.RingTheory.Reflexive.DoubleDual

/-!
# The ordinary differential trace of the literal finite normalization

The coefficient is the literal double dual of the actual exterior module.
Height-one membership is derived from the actual DVR normalization and its
actual trace. Transposition retains original multiplication, and the native
localized map is the original field differential transpose.
-/

@[expose] public noncomputable section

open Polynomial
open scoped nonZeroDivisors

attribute [local instance 2000] Algebra.toSMul

namespace Module.Dual

variable {A K M V : Type*} [CommRing A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [AddCommGroup M] [Module A M] [Module.FinitePresentation A M]
  [Module.FinitePresentation A (Dual A M)]
  [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
  [IsReflexive K V]
  (f : M →ₗ[A] V) [IsLocalizedModule A⁰ f]

/-- The literal bidual embedding is its actual generic module localization. -/
theorem doubleDualToFraction_isLocalizedModule :
    IsLocalizedModule A⁰ (doubleDualToFraction (K := K) f) := by
  let d : Dual A M →ₗ[A] Dual K V :=
    IsLocalizedModule.mapExtendScalars A⁰ f (Algebra.linearMap A K) K
  let : IsLocalizedModule A⁰ d :=
    Module.FinitePresentation.isLocalizedModule_mapExtendScalars _ _ _ _
  let dd : Dual A (Dual A M) →ₗ[A] Dual K (Dual K V) :=
    IsLocalizedModule.mapExtendScalars A⁰ d (Algebra.linearMap A K) K
  let : IsLocalizedModule A⁰ dd :=
    Module.FinitePresentation.isLocalizedModule_mapExtendScalars _ _ _ _
  exact IsLocalizedModule.of_linearEquiv A⁰ dd ((evalEquiv K V).symm.restrictScalars A)

end Module.Dual

namespace KaehlerDifferential

/-- Finiteness of the actual raw exterior power survives its original fraction localization. -/
theorem finiteExteriorAtFraction (Λ A K : Type*) [CommRing Λ] [CommRing A]
    [Field K] [Algebra Λ A] [Algebra Λ K] [Algebra A K]
    [IsScalarTower Λ A K] [IsFractionRing A K] (n : ℕ)
    [Module.Finite A (⋀[A]^(n + 1) (KaehlerDifferential Λ A))] :
    FiniteDimensional K (⋀[K]^(n + 1) (KaehlerDifferential Λ K)) := by
  let : IsLocalizedModule A⁰ (mapExterior Λ A K (n + 1)) :=
    mapExterior_isLocalizedModule Λ A K A⁰ (n + 1)
  exact Module.Finite.of_isLocalizedModule A⁰ (mapExterior Λ A K (n + 1))

/-- The original fraction field localizes the literal normalization. -/
theorem normalizationGenericLocalization (A K L : Type*) [CommRing A] [IsDomain A]
    [Field K] [Field L] [Algebra A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsFractionRing A K] [IsPurelyInseparable K L] :
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure A L) A⁰) L :=
  integralClosure.isLocalization A K L

section GlobalTrace

variable (Λ A K L : Type*) [CommRing Λ]
  [CommRing A] [Field K] [Algebra A K]
  [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [Algebra Λ A] [Algebra Λ K] [Algebra Λ L]
  [IsScalarTower Λ K L] [IsScalarTower Λ A L]
  {p : ℕ} [CharP K p] {a : K}

local notation "B" => integralClosure A L
local notation:max "BaseForms" n:arg => (⋀[A]^(n + 1) (KaehlerDifferential Λ A))
local notation:max "N" n:arg => (⋀[B]^(n + 1) (KaehlerDifferential Λ B))
local notation:max "V" n:arg => (⋀[K]^(n + 1) (KaehlerDifferential Λ K))
local notation:max "W" n:arg => (⋀[L]^(n + 1) (KaehlerDifferential Λ L))

/-- The original field trace restricted along the actual raw-form map of B. -/
def integralClosureRawTraceAtFraction
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a)) (n : ℕ) : (N n) →ₗ[A] (V n) :=
  ((pureDegreePTraceExterior (Λ := Λ) h n).restrictScalars A).comp
    ((mapExterior Λ B L (n + 1)).restrictScalars A)

theorem integralClosureRawTraceAtFraction_apply
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a)) (n : ℕ) (ω : (N n)) :
    integralClosureRawTraceAtFraction Λ A K L h n ω =
      pureDegreePTraceExterior (Λ := Λ) h n (mapExterior Λ B L (n + 1) ω) := rfl

variable [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
  [IsFractionRing A K] [IsScalarTower Λ A K]
  [FiniteDimensional K L] [IsPurelyInseparable K L]
  [Module.Finite A (integralClosure A L)] [Fact p.Prime]

section LocalDenominator

variable (D : Type*) [CommRing D] [Algebra A D]
  [Algebra D K] [IsScalarTower A D K]
  [Algebra D L] [IsScalarTower A D L] [IsScalarTower D K L]
  [Algebra Λ D] [IsScalarTower Λ A D] [IsScalarTower Λ D K] [IsScalarTower Λ D L]
  (q : Ideal A) [q.IsPrime] [IsLocalization q.primeCompl D]

include D in
/-- The actual local monogenic trace supplies a denominator in the original
raw exterior module. No trace-integrality condition is assumed. -/
theorem integralClosureRawTraceAtFraction_denominator
    (hdegree : Module.finrank K L = p) (hq : q.height = 1)
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a)) (n : ℕ) (ω : (N n)) :
    ∃ s ∉ q, s • integralClosureRawTraceAtFraction Λ A K L h n ω ∈
      Set.range (mapExterior Λ A K (n + 1)) := by
  let : IsDomain D :=
    IsLocalization.isDomain_of_le_nonZeroDivisors D q.primeCompl_le_nonZeroDivisors
  let : IsFractionRing D K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl D K
  let : CharP D p := (algebraMap D K).charP (IsFractionRing.injective D K) p
  let C := integralClosure D L
  let : Algebra B C := integralClosure.scalarExtensionAlgebra A D L
  let : IsScalarTower A B C := integralClosure.scalarExtension_isScalarTower_base A D L
  let : IsScalarTower B C L := integralClosure.scalarExtension_isScalarTower_ambient A D L
  let : IsScalarTower Λ B C := IsScalarTower.of_algebraMap_eq fun x => by
    apply Subtype.ext
    rfl
  obtain ⟨c, _, hC, _, _, _⟩ :=
    integralClosure.exists_presentation_at_height_one_of_pure_degree
      A D q K L p hq hdegree
  let ωC := mapExterior Λ B C (n + 1) ω
  let w := pureDegreePTraceExterior (Λ := Λ) hC n ωC
  have hw : mapExterior Λ D K (n + 1) w =
      integralClosureRawTraceAtFraction Λ A K L h n ω := by
    calc
      mapExterior Λ D K (n + 1) w =
          pureDegreePTraceExterior (Λ := Λ) h n
            (mapExterior Λ C L (n + 1) ωC) :=
        (LinearMap.congr_fun (pureDegreePTraceExterior_baseChange hC h n) ωC).symm
      _ = integralClosureRawTraceAtFraction Λ A K L h n ω := by
        rw [show mapExterior Λ C L (n + 1) ωC = mapExterior Λ B L (n + 1) ω from
          mapExterior_tower_apply Λ B C L (n + 1) ω]
        rfl
  let : IsLocalizedModule q.primeCompl (mapExterior Λ A D (n + 1)) :=
    mapExterior_isLocalizedModule Λ A D q.primeCompl (n + 1)
  obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj q.primeCompl
    (mapExterior Λ A D (n + 1)) w
  change (s : A) • w = mapExterior Λ A D (n + 1) m at hs
  refine ⟨(s : A), s.property, m, ?_⟩
  calc
    mapExterior Λ A K (n + 1) m =
        mapExterior Λ D K (n + 1) (mapExterior Λ A D (n + 1) m) :=
      (mapExterior_tower_apply Λ A D K (n + 1) m).symm
    _ = mapExterior Λ D K (n + 1) ((s : A) • w) := congrArg _ hs.symm
    _ = (s : A) • mapExterior Λ D K (n + 1) w :=
      (mapExterior Λ D K (n + 1)).map_smul_of_tower (s : A) w
    _ = (s : A) • integralClosureRawTraceAtFraction Λ A K L h n ω :=
      congrArg ((s : A) • ·) hw

end LocalDenominator

/-- Actual height-one integrality, with the original fraction field retained. -/
theorem integralClosureRawTraceAtFraction_heightOne
    (hdegree : Module.finrank K L = p)
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a)) (n : ℕ) (ω : (N n))
    (q : Ideal A) (hq : q.IsPrime) (hheight : q.height = 1) :
    ∃ s ∉ q, s • integralClosureRawTraceAtFraction Λ A K L h n ω ∈
      Set.range (mapExterior Λ A K (n + 1)) := by
  let : q.IsPrime := hq
  let D := Localization.AtPrime q
  let φ : D →ₐ[A] K :=
    IsLocalization.liftAlgHom (M := q.primeCompl) (f := Algebra.ofId A K)
      (fun s => IsLocalization.map_units K
        ⟨s.val, q.primeCompl_le_nonZeroDivisors s.property⟩)
  let : Algebra D K := φ.toRingHom.toAlgebra
  let : IsScalarTower A D K := IsScalarTower.of_algHom φ
  let : Algebra D L := ((algebraMap K L).comp (algebraMap D K)).toAlgebra
  let : IsScalarTower D K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower A D L := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap A L x = algebraMap K L (φ (algebraMap A D x))
    rw [φ.commutes]
    exact IsScalarTower.algebraMap_apply A K L x
  let : Algebra Λ D := ((algebraMap A D).comp (algebraMap Λ A)).toAlgebra
  let : IsScalarTower Λ A D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower Λ D K := IsScalarTower.to₁₃₄ Λ A D K
  let : IsScalarTower Λ D L := IsScalarTower.to₁₂₄ Λ D K L
  exact integralClosureRawTraceAtFraction_denominator Λ A K L D q
    hdegree hheight h n ω

section BidualCoefficient

variable (n : ℕ)

local instance baseExteriorLocalized : IsLocalizedModule A⁰ (mapExterior Λ A K (n + 1)) :=
  mapExterior_isLocalizedModule Λ A K A⁰ (n + 1)

local instance baseExteriorFinitePresentation
    [Module.Finite A ((BaseForms n))] : Module.FinitePresentation A ((BaseForms n)) :=
  Module.finitePresentation_of_finite A ((BaseForms n))

local instance baseExteriorDualFinitePresentation
    [Module.Finite A ((BaseForms n))] :
    Module.FinitePresentation A (Module.Dual A ((BaseForms n))) := by
  let : IsNoetherian A (Module.Dual A ((BaseForms n))) := isNoetherian_linearMap A A ((BaseForms n))
  let : Module.Finite A (Module.Dual A ((BaseForms n))) := Module.IsNoetherian.finite A _
  exact Module.finitePresentation_of_finite A _

/-- The raw normalization trace takes values in the actual double dual.
Its height-one membership proof is constructed from the original local DVRs. -/
def integralClosureRawTrace
    [Module.Finite A ((BaseForms n))]
    (hdegree : Module.finrank K L = p)
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a)) :
    (N n) →ₗ[A] Module.Dual A (Module.Dual A ((BaseForms n))) := by
  letI := finiteExteriorAtFraction Λ A K n
  exact Module.Dual.liftLinearMapToDoubleDualOfHeightOne (K := K)
    (mapExterior Λ A K (n + 1)) (integralClosureRawTraceAtFraction Λ A K L h n)
    (fun ω q hq hh => integralClosureRawTraceAtFraction_heightOne Λ A K L hdegree h n ω q hq hh)

/-- The original field differential trace is exactly the generic value of the lift. -/
theorem integralClosureRawTrace_generic
    [Module.Finite A ((BaseForms n))]
    (hdegree : Module.finrank K L = p)
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a)) (ω : (N n)) :
    letI := finiteExteriorAtFraction Λ A K n;
    Module.Dual.doubleDualToFraction (K := K) (mapExterior Λ A K (n + 1))
      (integralClosureRawTrace Λ A K L n hdegree h ω) =
        integralClosureRawTraceAtFraction Λ A K L h n ω := by
  let := finiteExteriorAtFraction Λ A K n
  exact Module.Dual.liftLinearMapToDoubleDualOfHeightOne_generic (K := K) _ _ _ ω

/-- The global raw trace is independent of the original field root presentation. -/
theorem integralClosureRawTrace_independent
    [Module.Finite A ((BaseForms n))]
    (hdegree : Module.finrank K L = p)
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a))
    {a' : K} (h' : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a')) :
    integralClosureRawTrace Λ A K L n hdegree h =
      integralClosureRawTrace Λ A K L n hdegree h' := by
  let := finiteExteriorAtFraction Λ A K n
  apply LinearMap.ext
  intro ω
  apply Module.Dual.doubleDualToFraction_injective (K := K) (mapExterior Λ A K (n + 1))
  rw [integralClosureRawTrace_generic, integralClosureRawTrace_generic,
    integralClosureRawTraceAtFraction_apply, integralClosureRawTraceAtFraction_apply,
    pureDegreePFieldTrace_independent h h' n]

/-- The requested c_B, with literal coefficient M** and actual multiplication in B. -/
def integralClosureTraceTranspose
    [Module.Finite A ((BaseForms n))]
    (hdegree : Module.finrank K L = p)
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a)) :
    (N n) →ₗ[A] (B →ₗ[A] Module.Dual A (Module.Dual A ((BaseForms n)))) :=
  LinearMap.smulTranspose (integralClosureRawTrace Λ A K L n hdegree h)

@[simp]
theorem integralClosureTraceTranspose_apply
    [Module.Finite A ((BaseForms n))]
    (hdegree : Module.finrank K L = p)
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a)) (ω : (N n)) (b : B) :
    integralClosureTraceTranspose Λ A K L n hdegree h ω b =
      integralClosureRawTrace Λ A K L n hdegree h (b • ω) := rfl

/-- Coordinate independence survives the unique global bidual lift and transposition. -/
theorem integralClosureTraceTranspose_independent
    [Module.Finite A ((BaseForms n))]
    (hdegree : Module.finrank K L = p)
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a))
    {a' : K} (h' : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a')) :
    integralClosureTraceTranspose Λ A K L n hdegree h =
      integralClosureTraceTranspose Λ A K L n hdegree h' := by
  apply LinearMap.ext
  intro ω
  apply LinearMap.ext
  intro b
  change integralClosureRawTrace Λ A K L n hdegree h (b • ω) =
    integralClosureRawTrace Λ A K L n hdegree h' (b • ω)
  rw [integralClosureRawTrace_independent Λ A K L n hdegree h h']

/-- Pointwise B-linearity uses precomposition on Hom; no B-action on M** is introduced. -/
theorem integralClosureTraceTranspose_smul_apply
    [Module.Finite A ((BaseForms n))]
    (hdegree : Module.finrank K L = p)
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a)) (ω : (N n)) (b c : B) :
    integralClosureTraceTranspose Λ A K L n hdegree h (b • ω) c =
      integralClosureTraceTranspose Λ A K L n hdegree h ω (c * b) :=
  LinearMap.smulTranspose_smul_apply _ b c ω

/-- Evaluation after the actual coefficient embedding is the original differential trace. -/
theorem integralClosureTraceTranspose_generic
    [Module.Finite A ((BaseForms n))]
    (hdegree : Module.finrank K L = p)
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a)) (ω : (N n)) (b : B) :
    letI := finiteExteriorAtFraction Λ A K n;
    Module.Dual.doubleDualToFraction (K := K) (mapExterior Λ A K (n + 1))
      (integralClosureTraceTranspose Λ A K L n hdegree h ω b) =
        pureDegreePTraceExterior (Λ := Λ) h n
          (mapExterior Λ B L (n + 1) (b • ω)) := by
  let := finiteExteriorAtFraction Λ A K n
  exact integralClosureRawTrace_generic Λ A K L n hdegree h (b • ω)

/-- The original generic evaluation determines c_B uniquely. -/
theorem integralClosureTraceTranspose_unique
    [Module.Finite A ((BaseForms n))]
    (hdegree : Module.finrank K L = p)
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a))
    (c : (N n) →ₗ[A] (B →ₗ[A] Module.Dual A (Module.Dual A ((BaseForms n)))))
    (hc : letI := finiteExteriorAtFraction Λ A K n;
      ∀ ω b, Module.Dual.doubleDualToFraction (K := K) (mapExterior Λ A K (n + 1)) (c ω b) =
      pureDegreePTraceExterior (Λ := Λ) h n (mapExterior Λ B L (n + 1) (b • ω))) :
    c = integralClosureTraceTranspose Λ A K L n hdegree h := by
  let := finiteExteriorAtFraction Λ A K n
  apply LinearMap.ext
  intro ω
  apply LinearMap.ext
  intro b
  apply Module.Dual.doubleDualToFraction_injective (K := K) (mapExterior Λ A K (n + 1))
  exact (hc ω b).trans (integralClosureTraceTranspose_generic Λ A K L n hdegree h ω b).symm

section GenericLocalization

local instance normalizationGenericModule
    [IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L] :
    IsLocalizedModule A⁰ ((Algebra.linearMap B L).restrictScalars A) :=
  IsLocalizedModule.restrictScalars A⁰ (Algebra.linearMap B L)

local instance normalizationExteriorGenericModule
    [IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L] :
    IsLocalizedModule A⁰ ((mapExterior Λ B L (n + 1)).restrictScalars A) := by
  let : IsLocalizedModule (Algebra.algebraMapSubmonoid B A⁰)
      (mapExterior Λ B L (n + 1)) :=
    mapExterior_isLocalizedModule Λ B L (Algebra.algebraMapSubmonoid B A⁰) (n + 1)
  exact IsLocalizedModule.restrictScalars A⁰ (mapExterior Λ B L (n + 1))

local instance bidualGenericModule [Module.Finite A ((BaseForms n))] :
    letI := finiteExteriorAtFraction Λ A K n;
    IsLocalizedModule A⁰ (Module.Dual.doubleDualToFraction (K := K)
      (mapExterior Λ A K (n + 1))) := by
  let := finiteExteriorAtFraction Λ A K n
  exact Module.Dual.doubleDualToFraction_isLocalizedModule (K := K) (mapExterior Λ A K (n + 1))

local instance normalizationFinitePresentation : Module.FinitePresentation A B :=
  Module.finitePresentation_of_finite A B

/-- The actual localized Hom map for the literal normalization and literal bidual. -/
def integralClosureTraceHomToFraction [Module.Finite A ((BaseForms n))] :
    (B →ₗ[A] Module.Dual A (Module.Dual A ((BaseForms n)))) →ₗ[A] (L →ₗ[K] (V n)) := by
  letI := finiteExteriorAtFraction Λ A K n
  letI := normalizationGenericLocalization A K L
  exact IsLocalizedModule.mapExtendScalars A⁰ ((Algebra.linearMap B L).restrictScalars A)
    (Module.Dual.doubleDualToFraction (K := K) (mapExterior Λ A K (n + 1))) K

local instance traceHomGenericModule [Module.Finite A ((BaseForms n))] :
    IsLocalizedModule A⁰ (integralClosureTraceHomToFraction Λ A K L n) := by
  let := finiteExteriorAtFraction Λ A K n
  let := normalizationGenericLocalization A K L
  exact Module.FinitePresentation.isLocalizedModule_mapExtendScalars _ _ _ _

/-- The localized global c_B is the actual field differential transpose.
Both sides and both localization maps are the original native maps. -/
theorem integralClosureTraceTranspose_localization
    [Module.Finite A ((BaseForms n))]
    (hdegree : Module.finrank K L = p)
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a)) :
    letI := normalizationGenericLocalization A K L;
    IsLocalizedModule.mapExtendScalars A⁰
      ((mapExterior Λ B L (n + 1)).restrictScalars A)
      (integralClosureTraceHomToFraction Λ A K L n) K
      (integralClosureTraceTranspose Λ A K L n hdegree h) =
        pureDegreePFieldTranspose (Λ := Λ) h n := by
  let := finiteExteriorAtFraction Λ A K n
  let := normalizationGenericLocalization A K L
  apply LinearMap.restrictScalars_injective A
  apply IsLocalizedModule.linearMap_ext A⁰
    ((mapExterior Λ B L (n + 1)).restrictScalars A)
    (integralClosureTraceHomToFraction Λ A K L n)
  apply LinearMap.ext
  intro ω
  change IsLocalizedModule.map A⁰ ((mapExterior Λ B L (n + 1)).restrictScalars A)
      (integralClosureTraceHomToFraction Λ A K L n)
      (integralClosureTraceTranspose Λ A K L n hdegree h)
      (mapExterior Λ B L (n + 1) ω) =
    pureDegreePFieldTranspose (Λ := Λ) h n (mapExterior Λ B L (n + 1) ω)
  refine (IsLocalizedModule.map_apply A⁰ ((mapExterior Λ B L (n + 1)).restrictScalars A)
    (integralClosureTraceHomToFraction Λ A K L n)
    (integralClosureTraceTranspose Λ A K L n hdegree h) ω).trans ?_
  apply LinearMap.restrictScalars_injective A
  apply IsLocalizedModule.linearMap_ext A⁰ ((Algebra.linearMap B L).restrictScalars A)
    (Module.Dual.doubleDualToFraction (K := K) (mapExterior Λ A K (n + 1)))
  apply LinearMap.ext
  intro b
  change IsLocalizedModule.map A⁰ ((Algebra.linearMap B L).restrictScalars A)
      (Module.Dual.doubleDualToFraction (K := K) (mapExterior Λ A K (n + 1)))
      (integralClosureTraceTranspose Λ A K L n hdegree h ω) (algebraMap B L b) =
    pureDegreePFieldTranspose (Λ := Λ) h n (mapExterior Λ B L (n + 1) ω) (algebraMap B L b)
  refine (IsLocalizedModule.map_apply A⁰ ((Algebra.linearMap B L).restrictScalars A)
    (Module.Dual.doubleDualToFraction (K := K) (mapExterior Λ A K (n + 1)))
    (integralClosureTraceTranspose Λ A K L n hdegree h ω) b).trans ?_
  rw [integralClosureTraceTranspose_generic, pureDegreePFieldTranspose_apply]
  apply congrArg (pureDegreePTraceExterior (Λ := Λ) h n)
  rw [map_smul, ← IsScalarTower.algebraMap_smul L b]

/-- Generic bijectivity uses only actual generic lines and a nonzero generic
wedge. In particular no integral wedge is required to be a unit generator. -/
theorem integralClosureTraceTranspose_generic_bijective
    [Module.Finite A ((BaseForms n))]
    (hdegree : Module.finrank K L = p)
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a))
    (v : Fin n → KaehlerDifferential Λ K)
    (hv : exteriorPower.ιMulti K (n + 1) (Fin.snoc v (D Λ K a)) ≠ 0)
    (hV : Module.finrank K ((V n)) = 1) (hW : Module.finrank L ((W n)) = 1) :
    letI := normalizationGenericLocalization A K L;
    Function.Bijective
      (IsLocalizedModule.mapExtendScalars A⁰
        ((mapExterior Λ B L (n + 1)).restrictScalars A)
        (integralClosureTraceHomToFraction Λ A K L n) K
        (integralClosureTraceTranspose Λ A K L n hdegree h)) := by
  let := normalizationGenericLocalization A K L
  rw [integralClosureTraceTranspose_localization]
  exact pureDegreePFieldTranspose_bijective h n v hv hV hW

end GenericLocalization

end BidualCoefficient

end GlobalTrace

section Nagata

universe u

variable (Λ : Type*) (A K L : Type u) [CommRing Λ]
  [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [Algebra Λ A] [Algebra Λ K] [Algebra Λ L]
  [IsScalarTower Λ A K] [IsScalarTower Λ K L] [IsScalarTower Λ A L]
  [FiniteDimensional K L] [IsPurelyInseparable K L]
  {p : ℕ} [Fact p.Prime] [CharP K p] {a : K}
  (n : ℕ) [Module.Finite A (⋀[A]^(n + 1) (KaehlerDifferential Λ A))]

/-- The Nagata domain supplies the actual normalization finiteness used by c_B.
Only the actual raw-form finiteness remains as a B4 coherence input. -/
def integralClosureTraceTransposeOfNagata
    (hNagata : IsNagataRing.{u, 0} A) (hdegree : Module.finrank K L = p)
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a)) :
    (⋀[integralClosure A L]^(n + 1) (KaehlerDifferential Λ (integralClosure A L))) →ₗ[A]
      (integralClosure A L →ₗ[A]
        Module.Dual A (Module.Dual A (⋀[A]^(n + 1) (KaehlerDifferential Λ A)))) := by
  let : IsNoetherianRing A := hNagata.1
  let : Module.Finite A (integralClosure A L) :=
    hNagata.isJapaneseRing.finite_integralClosure_of_isFractionRing K L
  exact integralClosureTraceTranspose Λ A K L n hdegree h

end Nagata

end KaehlerDifferential
