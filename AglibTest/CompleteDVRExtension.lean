/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.CompleteDVRExtension

/-!
# Complete DVR extension consumers

These consumers use the actual integral closure and literal algebra maps.
They assume no local-ring, DVR, completeness, or residue-finiteness structure
on the integral closure.
-/

@[expose] public noncomputable section

open IsLocalRing IsDiscreteValuationRing.CompleteExtension

namespace AglibTest.CompleteDVRExtension

variable (R L : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [Field L] [Algebra (FractionRing R) L]
  [Algebra R L] [IsScalarTower R (FractionRing R) L]
  [FiniteDimensional (FractionRing R) L] [Algebra.IsSeparable (FractionRing R) L]

/-- No local hypothesis on the extension ring is supplied. -/
theorem actual_closure_dvr : IsDiscreteValuationRing (integralClosure R L) :=
  integralClosure_isDiscreteValuationRing R (FractionRing R) L


omit [Algebra.IsSeparable (FractionRing R) L] in
/-- Residue characteristic zero supplies separability instead of assuming it. -/
theorem residue_charZero_closure [CharZero (ResidueField R)] :
    IsDiscreteValuationRing (integralClosure R L) := by
  have : CharZero R := RingHom.charZero (residue R)
  have : CharZero (FractionRing R) := inferInstance
  exact integralClosure_isDiscreteValuationRing R (FractionRing R) L

/-- Completeness refers to the actual closure's own maximal ideal. -/
theorem actual_closure_complete :
    let _ := actual_closure_dvr R L
    IsAdicComplete (maximalIdeal (integralClosure R L)) (integralClosure R L) :=
  integralClosure_isAdicComplete R (FractionRing R) L

/-- The resulting henselian ring is the integral closure itself. -/
theorem actual_closure_henselian : HenselianLocalRing (integralClosure R L) :=
  integralClosure_henselianLocalRing R (FractionRing R) L

/-- The residue-field degree is finite and strictly positive. -/
theorem actual_residue_degree_positive :
    let _ := actual_closure_dvr R L
    let _ := integralClosure_isLocalHom R (FractionRing R) L
    0 < Module.finrank (ResidueField R) (ResidueField (integralClosure R L)) := by
  let _ := actual_closure_dvr R L
  let _ := integralClosure_isLocalHom R (FractionRing R) L
  have := integralClosure_residue_finite R (FractionRing R) L
  exact Module.finrank_pos

/-- Both the coefficient and unit factor are elements of the literal integral closure. -/
theorem actual_uniformizer_factorization
    {π : R} (hπ : Irreducible π) {ϖ : integralClosure R L} (hϖ : Irreducible ϖ) :
    ∃ (e : ℕ) (_ : 0 < e) (u : (integralClosure R L)ˣ),
      algebraMap R (integralClosure R L) π = u * ϖ ^ e :=
  integralClosure_exists_positive_ramification R (FractionRing R) L hπ hϖ

omit [Algebra (FractionRing R) L] [IsScalarTower R (FractionRing R) L]
  [FiniteDimensional (FractionRing R) L] [Algebra.IsSeparable (FractionRing R) L] in
/-- The ramification input also works when the fraction field is explicitly named. -/
theorem named_fraction_field_closure (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] [Algebra K L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    IsDiscreteValuationRing (integralClosure R L) :=
  integralClosure_isDiscreteValuationRing R K L


/-- Every coefficient-field embedding sends actual principal integral elements to principal ones. -/
theorem actual_principal_embedding
    (E : Type*) [Field E] [Algebra (FractionRing R) E] [Algebra R E]
    [IsScalarTower R (FractionRing R) E] [FiniteDimensional (FractionRing R) E]
    [Algebra.IsSeparable (FractionRing R) E] (f : E →ₐ[FractionRing R] L) :
    let _ := actual_closure_dvr R E
    let _ := actual_closure_dvr R L
    ∀ x : integralClosure R E, residue (integralClosure R E) x = 1 →
      residue (integralClosure R L) ((f.restrictScalars R).mapIntegralClosure x) = 1 := by
  let _ := actual_closure_dvr R E
  let _ := actual_closure_dvr R L
  have : IsLocalHom (f.restrictScalars R).mapIntegralClosure.toRingHom :=
    mapIntegralClosure_isLocalHom (f.restrictScalars R)
  dsimp only
  intro x hx
  calc
    residue (integralClosure R L) ((f.restrictScalars R).mapIntegralClosure x) =
        ResidueField.map (f.restrictScalars R).mapIntegralClosure.toRingHom
          (residue (integralClosure R E) x) :=
      (ResidueField.map_residue (f.restrictScalars R).mapIntegralClosure.toRingHom x).symm
    _ = 1 := by rw [hx, map_one]

/-- The restriction is the native integral-closure map of the actual field embedding. -/
theorem actual_embedding_isLocal
    {A E F : Type*} [CommRing A] [Field E] [Field F] [Algebra A E] [Algebra A F]
    (f : E →ₐ[A] F) : IsLocalHom f.mapIntegralClosure.toRingHom :=
  mapIntegralClosure_isLocalHom f

/-- Restricting a field embedding preserves its literal values on integral elements. -/
theorem actual_embedding_commutes
    {A E F : Type*} [CommRing A] [Field E] [Field F] [Algebra A E] [Algebra A F]
    (f : E →ₐ[A] F) (x : integralClosure A E) :
    (f.mapIntegralClosure x : F) = f (x : E) :=
  f.coe_mapIntegralClosure x


open Lean in
run_cmd do
  for name in #[``IsDiscreteValuationRing.CompleteExtension.isLocalRing_of_artinian_of_idempotents,
      ``IsDiscreteValuationRing.CompleteExtension.exists_idempotent_lift,
      ``IsDiscreteValuationRing.CompleteExtension.isLocalRing_of_henselian_of_artinian_quotient,
      ``IsDiscreteValuationRing.CompleteExtension.isLocalRing_of_finite,
      ``IsDiscreteValuationRing.CompleteExtension.isAdicComplete_of_pow,
      ``IsDiscreteValuationRing.CompleteExtension.exists_positive_ramification,
      ``IsDiscreteValuationRing.CompleteExtension.mapIntegralClosure_isLocalHom,
      ``IsDiscreteValuationRing.CompleteExtension.integralClosure_isLocalRing,
      ``IsDiscreteValuationRing.CompleteExtension.integralClosure_algebraMap_injective,
      ``IsDiscreteValuationRing.CompleteExtension.integralClosure_isDiscreteValuationRing,
      ``IsDiscreteValuationRing.CompleteExtension.integralClosure_isLocalHom,
      ``IsDiscreteValuationRing.CompleteExtension.integralClosure_isAdicComplete,
      ``IsDiscreteValuationRing.CompleteExtension.integralClosure_residue_finite,
      ``IsDiscreteValuationRing.CompleteExtension.integralClosure_henselianLocalRing,
      ``IsDiscreteValuationRing.CompleteExtension.integralClosure_exists_positive_ramification,
      ``actual_closure_dvr, ``residue_charZero_closure, ``actual_closure_complete,
      ``actual_closure_henselian, ``actual_residue_degree_positive,
      ``actual_uniformizer_factorization, ``named_fraction_field_closure,
      ``actual_principal_embedding, ``actual_embedding_isLocal, ``actual_embedding_commutes] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual complete DVR extensions use only standard foundations."

end AglibTest.CompleteDVRExtension
