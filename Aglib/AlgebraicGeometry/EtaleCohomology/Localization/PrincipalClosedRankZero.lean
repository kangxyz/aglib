/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleEmpty
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.PrincipalClosedSupport

/-! # Actual class annihilation on the rank-zero principal closed branch

The finite coefficient transformation and localization preserve the original
zero-dimensional bound. The nonzero actual principal denominator makes the
literal quotient trivial. Every original family over that closed quotient is
empty, so its original cohomology class is zero in every degree. The H1
consumer therefore needs only its original open-zero input, not a supplied
closed-zero certificate. No new target or source refinement is substituted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u eY eV eW dY dV dA

attribute [local instance] hasSheafifyLarge hasSheafifyModules

/-- Vanishing belongs to the original H of any original coefficient. -/
theorem cohomology_eq_zero_of_isEmpty {X : Scheme.{u}} [IsEmpty X]
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} X)]
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (c : Sheaf.H.{eY} F q) : c = 0 := by
  let : Subsingleton (Sheaf.H.{eY} F q) :=
    Sheaf.subsingleton_H_of_isZero (Scheme.Etale.isZero_of_isEmpty F) q
  exact Subsingleton.elim _ _

variable (R S L : Type u) [CommRing R] [CommRing S] [CommRing L]
  [Algebra R S] [Module.Finite R S]
  (M : Submonoid S) [Algebra S L] [IsLocalization M L] [IsDomain L]
  (s : L) (hs : s ≠ 0) (hd : ringKrullDim R ≤ 0)

include hs hd M

/-- Produce zero of any actual closed-branch class, after deriving emptiness
from the original finite model, localization and denominator. -/
theorem principalClosed_class_eq_zero_of_rank_zero
    {W : Scheme.{u}}
    [HasExt.{eW} (AbelianSheaf.{u, u + 1} W)]
    (bZ : W ⟶ Spec (CommRingCat.of (L ⧸ Ideal.span {s})))
    (F : AbelianSheaf.{u, u + 1} W) (q : ℕ) (c : Sheaf.H.{eW} F q) : c = 0 := by
  have hdimL : ringKrullDim L ≤ 0 :=
    (IsLocalization.ringKrullDim_le S L M).trans
      ((RingHom.IsIntegral.ringKrullDim_le
        (algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral R S))).trans hd)
  have hquot : ringKrullDim (L ⧸ Ideal.span {s}) + 1 ≤ 0 :=
    (ringKrullDim_quotient_succ_le_of_nonZeroDivisor
      (mem_nonZeroDivisors_iff_ne_zero.mpr hs)).trans hdimL
  let : Subsingleton (L ⧸ Ideal.span {s}) :=
    ringKrullDim_eq_bot_iff_subsingleton.mp ((ENat.WithBot.add_one_le_zero_iff _).mp hquot)
  let : IsEmpty (Spec (CommRingCat.of (L ⧸ Ideal.span {s}))) :=
    inferInstanceAs (IsEmpty (PrimeSpectrum (L ⧸ Ideal.span {s})))
  let : IsEmpty W := Function.isEmpty bZ
  exact cohomology_eq_zero_of_isEmpty F q c

/-- The rank-zero H1 step actually discharges the closed branch. The only
zero input is the original class's restriction to its actual principal open. -/
theorem principalClosed_H1_zero_of_open_zero_at_rank_zero
    {Y V W : Scheme.{u}}
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{eV} (AbelianSheaf.{u, u + 1} V)]
    [HasExt.{eW} (AbelianSheaf.{u, u + 1} W)]
    [HasDerivedCategory.{dY} (AbelianSheaf.{u, u + 1} Y)]
    [HasDerivedCategory.{dV} (AbelianSheaf.{u, u + 1} V)]
    [HasDerivedCategory.{dA} AddCommGrpCat.{u + 1}]
    (n : ℕ) (hn : 0 < n)
    (I : ModuleSheaf (Spec (.of L)) (ULift.{u + 1} (ZMod n))) [Injective I]
    (b : Y ⟶ Spec (.of L)) (j' : V ⟶ Y)
    (bU : V ⟶ (principalSupportOpen L s).toScheme)
    (hj : IsPullback bU j' (principalSupportOpen L s).ι b) [Smooth b]
    (i' : W ⟶ Y) (bZ : W ⟶ Spec (CommRingCat.of (L ⧸ Ideal.span {s})))
    (hi : IsPullback bZ i' (principalSupportClosedMap L s) b)
    (c : Sheaf.H.{eY} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing (Spec (.of L))
        (ULift.{u + 1} (ZMod n)))).obj I)) 1)
    (hopen : cohomologyPullback j' _ 1 c = 0) : c = 0 := by
  obtain ⟨J, hJ, a, ha, hdetect⟩ :=
    exists_principalClosed_H1_detector (Y := Y) (V := V) (W := W) L s n hn I
  apply hdetect b j' bU hj inferInstance i' bZ hi c hopen
  exact principalClosed_class_eq_zero_of_rank_zero R S L M s hs hd bZ _ 1 _

end AlgebraicGeometry.Scheme.EtaleCohomology
