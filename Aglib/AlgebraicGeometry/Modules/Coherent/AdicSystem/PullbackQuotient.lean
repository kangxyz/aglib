/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.PullbackQuotient
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.QuotientComparison
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.Quotient
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Pullback of native ideal-sheaf quotients and their original units -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {X Y : Scheme.{u}} (p : Y ⟶ X) (K : X.IdealSheafData)

/-- The reversed fibre-product presentation has the same actual ideal kernel. -/
theorem idealSheafPullback_snd_ker :
    (Limits.pullback.snd K.subschemeι p).ker = K.comap p := by
  rw [← pullbackSymmetry_hom_comp_fst K.subschemeι p,
    Scheme.Hom.ker_comp_of_isIso]
  rfl

variable (M : X.Modules) [M.IsQuasicoherent]

/-- Arbitrary geometric pullback commutes with the native ideal-sheaf quotient. -/
def idealSheafPullbackQuotientIso :
    (pullback p).obj ((idealSheafQuotientFunctor X K).obj M) ≅
      (idealSheafQuotientFunctor Y (K.comap p)).obj ((pullback p).obj M) :=
  closedImmersionPullbackQuotientIso K.subschemeι p M ≪≫
    closedImmersionQuotientIso (Limits.pullback.snd K.subschemeι p)
      (K.comap p).subschemeι
      ((idealSheafPullback_snd_ker p K).trans
        (IdealSheafData.ker_subschemeι _).symm) ((pullback p).obj M)

@[reassoc (attr := simp)]
theorem idealSheafPullbackQuotientIso_unit :
    (pullback p).map ((idealSheafQuotientUnit X K).app M) ≫
      (idealSheafPullbackQuotientIso p K M).hom =
        (idealSheafQuotientUnit Y (K.comap p)).app ((pullback p).obj M) := by
  dsimp only [idealSheafPullbackQuotientIso, Iso.trans_hom]
  rw [← Category.assoc, closedImmersionPullbackQuotientIso_unit,
    closedImmersionUnit_quotientIso_hom]

/-- Quotient pullback comparisons retain original coefficient maps. -/
@[reassoc]
theorem idealSheafPullbackQuotientIso_naturality {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (g : M ⟶ N) :
    (pullback p).map ((idealSheafQuotientFunctor X K).map g) ≫
      (idealSheafPullbackQuotientIso p K N).hom =
    (idealSheafPullbackQuotientIso p K M).hom ≫
      (idealSheafQuotientFunctor Y (K.comap p)).map ((pullback p).map g) := by
  apply (cancel_epi ((pullback p).map ((idealSheafQuotientUnit X K).app M))).mp
  rw [← Functor.map_comp_assoc]
  rw [← (idealSheafQuotientUnit X K).naturality g]
  simp only [Functor.id_map, Functor.map_comp, Category.assoc]
  rw [idealSheafPullbackQuotientIso_unit]
  rw [← Category.assoc, idealSheafPullbackQuotientIso_unit]
  exact (idealSheafQuotientUnit Y (K.comap p)).naturality ((pullback p).map g)

end AlgebraicGeometry.Scheme.Modules.Coherent
