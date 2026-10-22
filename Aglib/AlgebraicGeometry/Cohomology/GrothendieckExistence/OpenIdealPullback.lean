/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.PullbackQuotient
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.QuotientComparisonTransport
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.OpenIdealPowers

/-! # Original finite-order quotient restriction for arbitrary ideals -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u
variable {X Y : Scheme.{u}} (p : Y ⟶ X) [IsOpenImmersion p]
  (K : X.IdealSheafData) (M : X.Modules) [M.IsQuasicoherent]

/-- The whole comparison, constructed before specializing its unit equation. -/
def openIdealPullbackQuotientComparison (n : ℕ) :
    {e : (pullback p).obj ((idealSheafQuotientFunctor X (K ^ n)).obj M) ≅
      (idealSheafQuotientFunctor Y (K.comap p ^ n)).obj ((pullback p).obj M) //
      (pullback p).map ((idealSheafQuotientUnit X (K ^ n)).app M) ≫ e.hom =
        (idealSheafQuotientUnit Y (K.comap p ^ n)).app ((pullback p).obj M)} :=
  arrowFamilyComparison
    (fun T => (idealSheafQuotientFunctor Y T).obj ((pullback p).obj M))
    (fun T => (idealSheafQuotientUnit Y T).app ((pullback p).obj M))
    ((pullback p).map ((idealSheafQuotientUnit X (K ^ n)).app M))
    (idealSheafPullbackQuotientIso p (K ^ n) M)
    (idealSheafPullbackQuotientIso_unit p (K ^ n) M)
    (IdealSheafData.comap_pow_of_isOpenImmersion p K n)

/-- Original geometric quotient comparison with its inferred native objects. -/
def openIdealPullbackQuotientIso (n : ℕ) :
    (pullback p).obj ((idealSheafQuotientFunctor X (K ^ n)).obj M) ≅
      (idealSheafQuotientFunctor Y (K.comap p ^ n)).obj ((pullback p).obj M) :=
  (openIdealPullbackQuotientComparison p K M n).val

/-- The original unit equation is a projection of the same whole comparison. -/
@[simp]
theorem openIdealPullbackQuotientIso_unit (n : ℕ) :
    (pullback p).map ((idealSheafQuotientUnit X (K ^ n)).app M) ≫
      (openIdealPullbackQuotientIso p K M n).hom =
        (idealSheafQuotientUnit Y (K.comap p ^ n)).app ((pullback p).obj M) :=
  (openIdealPullbackQuotientComparison p K M n).property

/-- Actual annihilated coefficients stay annihilated after open restriction. -/
theorem killedByOpenIdeal_pullback (n : ℕ)
    (hM : killedByIdealSheaf (K ^ n) M) :
    killedByIdealSheaf ((K.comap p) ^ n) ((pullback p).obj M) := by
  let K₀ := K ^ n
  let L := (K.comap p) ^ n
  have hK : IsIso ((idealSheafQuotientUnit X K₀).app M) :=
    (pullbackPushforwardUnit_isIso_iff_killedByIdealSheaf K₀.subschemeι M).mpr
      (by simpa only [IdealSheafData.ker_subschemeι] using hM)
  let := hK
  have hL : IsIso ((idealSheafQuotientUnit Y L).app ((pullback p).obj M)) := by
    rw [← openIdealPullbackQuotientIso_unit p K M n]
    infer_instance
  have hh := (pullbackPushforwardUnit_isIso_iff_killedByIdealSheaf L.subschemeι
    ((pullback p).obj M)).mp hL
  simpa only [IdealSheafData.ker_subschemeι] using hh

end AlgebraicGeometry.Scheme.Modules.Coherent
