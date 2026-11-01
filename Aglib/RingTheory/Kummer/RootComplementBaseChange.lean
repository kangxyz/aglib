/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.RootComplement
public import Aglib.RingTheory.Kummer.RootBaseChange

/-! # The original root-complement square under coefficient change

Both vertical maps are native localization lifts of the original coefficient
and root-algebra maps. The complete square retains the same literal parameter
and root localizations, without a normalization base-change assertion.
-/

@[expose] public noncomputable section

namespace Algebra.Kummer

variable {R : Type*} [CommRing R] (B : Type*) [CommRing B] [Algebra R B]
  (N : ℕ) (f : R)

local notation "T" => RootAlgebra N f
local notation "TB" => RootAlgebra N (algebraMap R B f)
local notation "θ" => AdjoinRoot.root (rootPolynomial N f)
local notation "θB" => AdjoinRoot.root (rootPolynomial N (algebraMap R B f))

/-- Change coefficients on the literal parameter complement. -/
def parameterComplementBaseChangeHom :
    Localization.Away f →+* Localization.Away (algebraMap R B f) :=
  IsLocalization.Away.lift f
    (g := (algebraMap B (Localization.Away (algebraMap R B f))).comp (algebraMap R B))
    (IsLocalization.Away.algebraMap_isUnit (algebraMap R B f))

/-- Change coefficients on the literal root complement through the original root map. -/
def rootComplementBaseChangeHom : Localization.Away θ →+* Localization.Away θB :=
  IsLocalization.Away.lift θ
    (g := (algebraMap TB (Localization.Away θB)).comp (rootBaseChangeHom B N f).toRingHom)
    (by
      change IsUnit (algebraMap TB (Localization.Away θB) (rootBaseChangeHom B N f θ))
      rw [rootBaseChangeHom_root]
      exact IsLocalization.Away.algebraMap_isUnit θB)

@[simp] theorem parameterComplementBaseChangeHom_algebraMap (r : R) :
    parameterComplementBaseChangeHom B f (algebraMap R (Localization.Away f) r) =
      algebraMap B (Localization.Away (algebraMap R B f)) (algebraMap R B r) :=
  IsLocalization.Away.lift_eq _ _ _

@[simp] theorem rootComplementBaseChangeHom_algebraMap (t : T) :
    rootComplementBaseChangeHom B N f (algebraMap T (Localization.Away θ) t) =
      algebraMap TB (Localization.Away θB) (rootBaseChangeHom B N f t) :=
  IsLocalization.Away.lift_eq _ _ _

/-- The entire parameter coefficient triangle. -/
theorem parameterComplementBaseChangeHom_comp :
    (parameterComplementBaseChangeHom B f).comp (algebraMap R (Localization.Away f)) =
      (algebraMap B (Localization.Away (algebraMap R B f))).comp (algebraMap R B) :=
  IsLocalization.Away.lift_comp _ _

/-- The entire original root-algebra triangle. -/
theorem rootComplementBaseChangeHom_comp :
    (rootComplementBaseChangeHom B N f).comp (algebraMap T (Localization.Away θ)) =
      (algebraMap TB (Localization.Away θB)).comp (rootBaseChangeHom B N f).toRingHom :=
  IsLocalization.Away.lift_comp _ _

/-- The actual complement square commutes on the original localization maps. -/
theorem rootComplementBaseChangeHom_comp_rootComplementHom :
    (rootComplementBaseChangeHom B N f).comp (rootComplementHom N f) =
      (rootComplementHom N (algebraMap R B f)).comp
        (parameterComplementBaseChangeHom B f) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext r
  simp only [RingHom.comp_apply, rootComplementHom_algebraMap,
    parameterComplementBaseChangeHom_algebraMap]
  rw [IsScalarTower.algebraMap_apply R T (Localization.Away θ),
    rootComplementBaseChangeHom_algebraMap, rootBaseChangeHom_algebraMap,
    IsScalarTower.algebraMap_apply R B TB,
    ← IsScalarTower.algebraMap_apply B TB (Localization.Away θB)]

end Algebra.Kummer
