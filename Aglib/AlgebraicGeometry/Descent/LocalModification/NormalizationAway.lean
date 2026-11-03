/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.FunctionField.FlatPreimmersion
public import Aglib.AlgebraicGeometry.FunctionField.Normalization
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.NormalizedPointBlowupChain

/-!
# The unchanged open for a literal normalized point step

The ordinary point centre is the full reduced point ideal. Generic
normalization over a normal open is identified by its original comparison,
not by an assumed abstract normal model.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- Literal generic normalization is unchanged over a nonempty normal open. -/
theorem genericNormalization_isIso_restrict_of_normal_open
    (B : Scheme.{u}) [IsIntegral B] (V : B.Opens) [Nonempty V]
    (hV : NormalStalks V.toScheme) :
    IsIso ((B.fromSpecStalk (genericPoint B)).fromNormalization ∣_ V) := by
  let : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  let : IsDominant V.ι := Scheme.isDominant_of_isOpenImmersion V.ι
  let (v : V.toScheme) : IsIntegrallyClosed (V.toScheme.presheaf.stalk v) := (hV v).2
  let ν := (B.fromSpecStalk (genericPoint B)).fromNormalization
  let E := genericNormalizationPullbackIso V.ι
  have H : E.hom ≫ pullback.snd ν V.ι =
      (V.toScheme.fromSpecStalk (genericPoint V.toScheme)).fromNormalization :=
    genericNormalizationPullbackIso_hom_snd V.ι
  have : IsIso (E.hom ≫ pullback.snd ν V.ι) := by rw [H]; infer_instance
  let : IsIso (pullback.snd ν V.ι) := IsIso.of_isIso_comp_left E.hom _
  change IsIso ((pullbackRestrictIsoRestrict ν V).inv ≫ pullback.snd ν V.ι)
  infer_instance

namespace Blowup

/-- The actual normalized point step is an isomorphism on every nonempty
open avoiding its closed centre when the original scheme is normal.
No finiteness of normalization or properness premise is needed here. -/
theorem normalizedPointBlowupMap_isIso_restrict_away
    (X : Scheme.{u}) [IsIntegral X] (hX : NormalStalks X)
    (x : X) (hx : IsClosed ({x} : Set X)) (hne : x ≠ genericPoint X)
    (U : X.Opens) [Nonempty U] (hxU : x ∉ U) :
    IsIso (normalizedPointBlowupMap X x hx hne ∣_ U) := by
  let B := blowupDatum (X.fromSpecResidueField x).ker
  let : IsIntegral B.Y := pointBlowup_isIntegral X x hx hne
  have hBU : IsIso (B.map ∣_ U) := by
    apply B.restrict_isIso_of_disjoint U
    rw [Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField, hx.closure_eq]
    exact Set.disjoint_singleton_right.mpr hxU
  let := hBU
  let V := B.map ⁻¹ᵁ U
  let : Nonempty V := Nonempty.map (inv (B.map ∣_ U)) inferInstance
  let j := (B.map ∣_ U) ≫ U.ι
  have hV : NormalStalks V.toScheme := by
    intro v
    let := (hX (j v)).1
    let := (hX (j v)).2
    let e := (asIso (j.stalkMap v)).commRingCatIsoToRingEquiv
    exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩
  let ν := (B.Y.fromSpecStalk (genericPoint B.Y)).fromNormalization
  let : IsIso (ν ∣_ V) := genericNormalization_isIso_restrict_of_normal_open B.Y V hV
  change IsIso ((ν ≫ B.map) ∣_ U)
  rw [morphismRestrict_comp]
  infer_instance

end Blowup
end AlgebraicGeometry.Scheme
