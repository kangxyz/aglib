/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.QuotientComparisonTransport
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.PullbackQuotient
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.AffinePushforward

/-! # Original quotient pullback for ideals from a specified affine base -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

variable {A : Type u} [CommRing A] {X Y : Scheme.{u}}
  (p : Y ⟶ X) (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)

/-- The original base-induced ideal pulls back to the ideal of the composite. -/
theorem baseIdeal_comap :
    (idealThickeningIdealSheaf f I).comap p = idealThickeningIdealSheaf (p ≫ f) I := by
  calc
    _ = (idealThickeningι f I).ker.comap p :=
      congrArg (fun K => K.comap p) (idealThickeningι_ker f I).symm
    _ = (Limits.pullback.fst p (idealThickeningι f I)).ker :=
      (IdealSheafData.ker_fst_of_isClosedImmersion (idealThickeningι f I) p).symm
    _ = (idealThickeningι (p ≫ f) I).ker := (idealThickeningComposite_ker p f I).symm
    _ = _ := idealThickeningι_ker (p ≫ f) I

/-- Every original ideal power has the required pullback equality. -/
theorem baseIdeal_pow_comap (n : ℕ) :
    (idealThickeningIdealSheaf f I ^ n).comap p =
      idealThickeningIdealSheaf (p ≫ f) I ^ n := by
  rw [idealThickeningIdealSheaf_pow, idealThickeningIdealSheaf_pow]
  exact baseIdeal_comap p f (I ^ n)

variable (M : X.Modules) [M.IsQuasicoherent]

/-- The whole comparison, constructed before specializing its unit equation. -/
def baseIdealPullbackQuotientComparison (n : ℕ) :
    { e : (pullback p).obj
        ((idealSheafQuotientFunctor X (idealThickeningIdealSheaf f I ^ n)).obj M) ≅
      (idealSheafQuotientFunctor Y (idealThickeningIdealSheaf (p ≫ f) I ^ n)).obj
        ((pullback p).obj M) //
      (pullback p).map ((idealSheafQuotientUnit X (idealThickeningIdealSheaf f I ^ n)).app M) ≫
        e.hom = (idealSheafQuotientUnit Y
          (idealThickeningIdealSheaf (p ≫ f) I ^ n)).app ((pullback p).obj M) } :=
  arrowFamilyComparison
    (fun T => (idealSheafQuotientFunctor Y T).obj ((pullback p).obj M))
    (fun T => (idealSheafQuotientUnit Y T).app ((pullback p).obj M))
    ((pullback p).map ((idealSheafQuotientUnit X (idealThickeningIdealSheaf f I ^ n)).app M))
    (idealSheafPullbackQuotientIso p (idealThickeningIdealSheaf f I ^ n) M)
    (idealSheafPullbackQuotientIso_unit p (idealThickeningIdealSheaf f I ^ n) M)
    (baseIdeal_pow_comap p f I n)

/-- Original geometric quotient comparison with explicit native quotient objects. -/
def baseIdealPullbackQuotientIso (n : ℕ) :
    (pullback p).obj
        ((idealSheafQuotientFunctor X (idealThickeningIdealSheaf f I ^ n)).obj M) ≅
      (idealSheafQuotientFunctor Y (idealThickeningIdealSheaf (p ≫ f) I ^ n)).obj
        ((pullback p).obj M) :=
  (baseIdealPullbackQuotientComparison p f I M n).val

/-- The original unit equation is a projection of the same whole comparison. -/
@[simp]
theorem baseIdealPullbackQuotientIso_unit (n : ℕ) :
    (pullback p).map ((idealSheafQuotientUnit X (idealThickeningIdealSheaf f I ^ n)).app M) ≫
      (baseIdealPullbackQuotientIso p f I M n).hom =
        (idealSheafQuotientUnit Y (idealThickeningIdealSheaf (p ≫ f) I ^ n)).app
          ((pullback p).obj M) :=
  (baseIdealPullbackQuotientComparison p f I M n).property

/-- Actual annihilated coefficients stay annihilated after arbitrary pullback. -/
theorem killedByBaseIdeal_pullback (n : ℕ)
    (hM : killedByIdealSheaf (idealThickeningIdealSheaf f I ^ n) M) :
    killedByIdealSheaf (idealThickeningIdealSheaf (p ≫ f) I ^ n) ((pullback p).obj M) := by
  let K := idealThickeningIdealSheaf f I ^ n
  let L := idealThickeningIdealSheaf (p ≫ f) I ^ n
  have hK : IsIso ((idealSheafQuotientUnit X K).app M) :=
    (pullbackPushforwardUnit_isIso_iff_killedByIdealSheaf K.subschemeι M).mpr
      (by simpa only [IdealSheafData.ker_subschemeι] using hM)
  let := hK
  have hL : IsIso ((idealSheafQuotientUnit Y L).app ((pullback p).obj M)) := by
    rw [← baseIdealPullbackQuotientIso_unit p f I M n]
    infer_instance
  have hh := (pullbackPushforwardUnit_isIso_iff_killedByIdealSheaf L.subschemeι
    ((pullback p).obj M)).mp hL
  simpa only [IdealSheafData.ker_subschemeι] using hh

end AlgebraicGeometry.Scheme.Modules.Coherent
