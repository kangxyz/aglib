/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.ProperLocalApproximation
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.ProperResidue.EssentialSurjectivity
public import Aglib.RingTheory.Henselian.GeometricLocalArtinApproximationAlgHom
public import Aglib.RingTheory.Henselian.HenselizationNoetherian

/-!
# Proper finite-etale equivalence over geometric local henselizations

The actual henselization at an arbitrary prime of a finite-type algebra over
a field or a characteristic-zero DVR satisfies the proper closed-fibre
equivalence. No approximation, descent, or finite-origin-model oracle remains.
The coefficient algebra may have zero divisors and need not be flat.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u v

section Field

variable (k : Type v) [Field k] (B : Type u) [CommRing B] [Algebra k B]
  [Algebra.FiniteType k B] (q : Ideal B) [q.IsPrime]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of (Henselization (Localization.AtPrime q))))
  [IsProper f]

include k in
/-- Essential surjectivity over the actual geometric local henselization
of a finite-type algebra over an arbitrary field. -/
theorem properGeometricLocal_baseChange_essSurj :
    (baseChange (pullback.fst f
      (LocalRing.residueSpecMap (Henselization (Localization.AtPrime q))))).EssSurj := by
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  let : IsNoetherianRing (Henselization (Localization.AtPrime q)) :=
    Henselization.isNoetherianRing _
  apply properLocal_baseChange_essSurj_of_approximation f
  intro C _ _ _ b
  exact GeometricLocalHenselization.exists_algHom_ideal_completion_with_precision
    k B q _ (by exact (inferInstance :
      (IsLocalRing.maximalIdeal (Henselization (Localization.AtPrime q))).IsMaximal).ne_top) C b 1

include k in
/-- The original closed-fibre restriction is an equivalence over a geometric
local henselization of finite type over a field. -/
theorem properGeometricLocal_baseChange_isEquivalence :
    (baseChange (pullback.fst f
      (LocalRing.residueSpecMap (Henselization (Localization.AtPrime q))))).IsEquivalence where
  faithful := inferInstance
  full := ProperResidue.closedFiber_baseChange_full_of_universal_essSurj
    (fun _ g hg => by
      let := hg
      exact properGeometricLocal_baseChange_essSurj k B q g) f
  essSurj := properGeometricLocal_baseChange_essSurj k B q f

end Field

section DVR

variable (D : Type v) [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] [CharZero D]
  (B : Type u) [CommRing B] [Algebra D B] [Algebra.FiniteType D B]
  (q : Ideal B) [q.IsPrime]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of (Henselization (Localization.AtPrime q))))
  [IsProper f]

include D in
/-- Essential surjectivity over the actual henselization at an arbitrary prime
of any finite-type algebra over a characteristic-zero DVR. -/
theorem properGeometricLocal_baseChange_essSurj_of_charZeroDVR :
    (baseChange (pullback.fst f
      (LocalRing.residueSpecMap (Henselization (Localization.AtPrime q))))).EssSurj := by
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing D B
  let : IsNoetherianRing (Henselization (Localization.AtPrime q)) :=
    Henselization.isNoetherianRing _
  apply properLocal_baseChange_essSurj_of_approximation f
  intro C _ _ _ b
  exact GeometricLocalHenselization.exists_algHom_ideal_completion_with_precision_of_charZeroDVR
    D B q _ (by exact (inferInstance :
      (IsLocalRing.maximalIdeal (Henselization (Localization.AtPrime q))).IsMaximal).ne_top) C b 1

include D in
/-- The original closed-fibre restriction is an equivalence over a geometric
local henselization of finite type over a characteristic-zero DVR. -/
theorem properGeometricLocal_baseChange_isEquivalence_of_charZeroDVR :
    (baseChange (pullback.fst f
      (LocalRing.residueSpecMap (Henselization (Localization.AtPrime q))))).IsEquivalence where
  faithful := inferInstance
  full := ProperResidue.closedFiber_baseChange_full_of_universal_essSurj
    (fun _ g hg => by
      let := hg
      exact properGeometricLocal_baseChange_essSurj_of_charZeroDVR D B q g) f
  essSurj := properGeometricLocal_baseChange_essSurj_of_charZeroDVR D B q f

end DVR

end AlgebraicGeometry.Scheme.FiniteEtale
