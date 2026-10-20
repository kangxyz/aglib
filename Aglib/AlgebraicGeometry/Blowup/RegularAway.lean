/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.UniversalProperty
public import Aglib.AlgebraicGeometry.Properties.Regular.Basic

/-!
Source: `R5Lab.Aglib.AlgebraicGeometry.Blowup.RegularAway`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `26f177b96efffced1cf224cb7945531d8ac7179ce662fd5c85eca7942556921d`.
Actual maps and mathematical hypotheses are retained. Conditional family
definitions do not supply blowup existence, properness, base change or an atlas.
-/

@[expose] public section

/-!
# Regularity of a blowup away from its centre

Source: R5 revision `e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`.
Statements, chosen comparisons, and explicit incoming evidence boundaries are retained.
-/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u v

namespace AlgebraicGeometry.Scheme.Blowup

open AlgebraicGeometry.Scheme.Blowup

/-- A point blowup is regular at every point lying over the old regular complement. -/
lemma blowup_regular_away {P Y : Scheme.{u}} (q : P ⟶ Y) [IsClosedImmersion q]
    (B : BlowupDatum q.ker)
    (hY : ∀ y : Y, y ∉ Set.range q → IsRegularLocalRing (Y.presheaf.stalk y))
    (z : B.Y) (hz : B.map z ∉ Set.range q) : IsRegularLocalRing (B.Y.presheaf.stalk z) := by
  let U : Y.Opens := ⟨(Set.range q)ᶜ, q.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hU : Disjoint (U : Set Y) (q.ker.support : Set Y) := by
    rw [Scheme.Hom.support_ker, q.isClosedEmbedding.isClosed_range.closure_eq]
    exact Set.disjoint_left.mpr (fun z hz hz' => hz hz')
  let := B.restrict_isIso_of_disjoint U hU
  have hreg : RegularStalks U.toScheme := by
    intro u
    let : IsRegularLocalRing (Y.presheaf.stalk (U.ι u)) := hY (U.ι u) u.property
    exact IsRegularLocalRing.of_ringEquiv (asIso (U.ι.stalkMap u)).commRingCatIsoToRingEquiv
  have hreg' := hreg.of_isOpenImmersion (B.map ∣_ U)
  let w : (B.map ⁻¹ᵁ U).toScheme := ⟨z, hz⟩
  let : IsRegularLocalRing (((B.map ⁻¹ᵁ U).toScheme).presheaf.stalk w) := hreg' w
  exact IsRegularLocalRing.of_ringEquiv
    (asIso ((B.map ⁻¹ᵁ U).ι.stalkMap w)).commRingCatIsoToRingEquiv.symm

end AlgebraicGeometry.Scheme.Blowup
