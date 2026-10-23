/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.Approximation.Bridge
public import Aglib.RingTheory.Henselian.GeometricLocalArtinApproximationAlgHom
public import Aglib.RingTheory.Henselian.HenselizationNoetherian
public import Mathlib.RingTheory.Localization.Submodule

/-!
# Closed-fibre approximation of actual geometric completed line bundles

The existing field and characteristic-zero DVR Artin theorems supply the
precision-one algebra maps required by the finite-data application. The
original henselization is Noetherian by its existing theorem. No separably
closed residue-field assumption or arbitrary henselian approximation is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u v

/-- Native precision one in the ideal-power quotient retains precisely the
original quotient map to the original closed fibre. -/
theorem algHom_precisionOne_of_precision
    {R : Type u} [CommRing R] {C : Type v} [CommRing C] [Algebra R C]
    (I : Ideal R) (a : C →ₐ[R] R) (b : C →ₐ[R] AdicCompletion I R)
    (h : (Ideal.Quotient.mkₐ R (I ^ 1)).comp a = (AdicCompletion.evalₐ I 1).comp b) :
    (Ideal.Quotient.mkₐ R I).comp a = (AdicCompletion.evalOneₐ I).comp b := by
  ext c
  have hc := congrArg (Ideal.Quotient.factor (show I ^ 1 ≤ I by simp))
    (DFunLike.congr_fun h c)
  simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.factor_mk, AdicCompletion.factorₐ_evalₐ_one] using hc

section Field

variable (k : Type u) [Field k] (B : Type v) [CommRing B] [Algebra k B]
  [Algebra.FiniteType k B] (q : Ideal B) [q.IsPrime]

include k in
/-- Every actual completed line bundle over a geometric local henselization
over a field is the closed-fibre restriction of an actual original bundle. -/
theorem exists_lineBundle_of_completion_geometricLocal
    {X : Scheme.{v}}
    (f : X ⟶ Spec (CommRingCat.of (Henselization (Localization.AtPrime q))))
    [QuasiCompact f] [QuasiSeparated f]
    (I : Ideal (Henselization (Localization.AtPrime q))) (hI : I ≠ ⊤)
    (L : LineBundle (completionBaseChange f I)) :
    ∃ M : LineBundle X,
      Nonempty ((pullback (idealThickeningι f I)).obj M.val ≅
        (pullback (completionClosedFiberMap f I)).obj L.val) := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have : IsNoetherianRing (Henselization (Localization.AtPrime q)) :=
    Henselization.isNoetherianRing (Localization.AtPrime q)
  apply exists_lineBundle_of_completion_of_algHom_approximation f I ?_ L
  intro C _ _ _ b
  obtain ⟨a, ha⟩ := GeometricLocalHenselization.exists_algHom_ideal_completion_with_precision
    k B q I hI C b 1
  exact ⟨a, algHom_precisionOne_of_precision I a b ha⟩

include k in
/-- The field-geometric application preserves a specified comparison with
the supplied bundle on the original closed fibre. -/
theorem exists_lineBundle_lift_of_completion_geometricLocal
    {X : Scheme.{v}}
    (f : X ⟶ Spec (CommRingCat.of (Henselization (Localization.AtPrime q))))
    [QuasiCompact f] [QuasiSeparated f]
    (I : Ideal (Henselization (Localization.AtPrime q))) (hI : I ≠ ⊤)
    (L : LineBundle (completionBaseChange f I))
    (L₀ : LineBundle (idealThickeningSpace f I))
    (e₀ : (pullback (completionClosedFiberMap f I)).obj L.val ≅ L₀.val) :
    ∃ M : LineBundle X, Nonempty ((pullback (idealThickeningι f I)).obj M.val ≅ L₀.val) := by
  obtain ⟨M, ⟨e⟩⟩ := exists_lineBundle_of_completion_geometricLocal k B q f I hI L
  exact ⟨M, ⟨e ≪≫ e₀⟩⟩

end Field

section DVR

variable (D : Type u) [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] [CharZero D]
  (B : Type v) [CommRing B] [Algebra D B] [Algebra.FiniteType D B]
  (q : Ideal B) [q.IsPrime]

include D in
/-- The same actual completed-bundle approximation over a geometric local
henselization of a finite-type algebra over a characteristic-zero DVR. -/
theorem exists_lineBundle_of_completion_geometricLocal_of_charZeroDVR
    {X : Scheme.{v}}
    (f : X ⟶ Spec (CommRingCat.of (Henselization (Localization.AtPrime q))))
    [QuasiCompact f] [QuasiSeparated f]
    (I : Ideal (Henselization (Localization.AtPrime q))) (hI : I ≠ ⊤)
    (L : LineBundle (completionBaseChange f I)) :
    ∃ M : LineBundle X,
      Nonempty ((pullback (idealThickeningι f I)).obj M.val ≅
        (pullback (completionClosedFiberMap f I)).obj L.val) := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing D B
  have : IsNoetherianRing (Henselization (Localization.AtPrime q)) :=
    Henselization.isNoetherianRing (Localization.AtPrime q)
  apply exists_lineBundle_of_completion_of_algHom_approximation f I ?_ L
  intro C _ _ _ b
  obtain ⟨a, ha⟩ :=
    GeometricLocalHenselization.exists_algHom_ideal_completion_with_precision_of_charZeroDVR
      D B q I hI C b 1
  exact ⟨a, algHom_precisionOne_of_precision I a b ha⟩

include D in
/-- The DVR-geometric application preserves a specified comparison with
the supplied bundle on the original closed fibre. -/
theorem exists_lineBundle_lift_of_completion_geometricLocal_of_charZeroDVR
    {X : Scheme.{v}}
    (f : X ⟶ Spec (CommRingCat.of (Henselization (Localization.AtPrime q))))
    [QuasiCompact f] [QuasiSeparated f]
    (I : Ideal (Henselization (Localization.AtPrime q))) (hI : I ≠ ⊤)
    (L : LineBundle (completionBaseChange f I))
    (L₀ : LineBundle (idealThickeningSpace f I))
    (e₀ : (pullback (completionClosedFiberMap f I)).obj L.val ≅ L₀.val) :
    ∃ M : LineBundle X, Nonempty ((pullback (idealThickeningι f I)).obj M.val ≅ L₀.val) := by
  obtain ⟨M, ⟨e⟩⟩ := exists_lineBundle_of_completion_geometricLocal_of_charZeroDVR
    D B q f I hI L
  exact ⟨M, ⟨e ≪≫ e₀⟩⟩

end DVR

end AlgebraicGeometry.Scheme.Modules.Invertible
