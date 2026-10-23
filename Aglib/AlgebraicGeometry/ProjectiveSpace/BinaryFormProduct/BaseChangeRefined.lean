/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.BaseChangeCoordinates
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.Map

/-!
# Actual coefficient basic opens under arbitrary base change

The original coefficient ring-map identity identifies the actual refined
source opens and the same coefficient sections on these opens. These are
the original local frames used to define the coefficient morphism.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct

universe u

private theorem basicOpen_appLE {X Y : Scheme.{u}} (g : X ⟶ Y)
    (U : Y.Opens) (V : X.Opens) (hV : V ≤ g ⁻¹ᵁ U) (r : Γ(Y, U)) :
    X.basicOpen ((g.appLE U V hV) r) = V ⊓ g ⁻¹ᵁ Y.basicOpen r := by
  change X.basicOpen (X.presheaf.map (homOfLE hV).op ((g.app U) r)) = _
  rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Each original coefficient basic open has its exact original base-change preimage. -/
theorem sourceBaseChangeMap_preimage_refinedOpen (σ : R →+* S) (n : ℕ)
    (z : Chart.{u} n × ULift.{u} (Fin (n + 1))) :
    sourceBaseChangeMap σ n ⁻¹ᵁ refinedOpen R n z = refinedOpen S n z := by
  have h := basicOpen_appLE (sourceBaseChangeMap σ n)
    (sourceOpen R n z.1) (sourceOpen S n z.1)
    (sourceBaseChangeMap_preimage_sourceOpen σ n z.1).ge
    (localCoefficient R n z.1 (sourceOpen R n z.1) le_rfl z.2.down)
  rw [sourceBaseChangeMap_appLE_localCoefficient] at h
  have hle : sourceBaseChangeMap σ n ⁻¹ᵁ refinedOpen R n z ≤ sourceOpen S n z.1 :=
    ((sourceBaseChangeMap σ n).preimage_mono (refinedOpen_le R n z)).trans
      (sourceBaseChangeMap_preimage_sourceOpen σ n z.1).le
  change refinedOpen S n z = sourceOpen S n z.1 ⊓
    sourceBaseChangeMap σ n ⁻¹ᵁ refinedOpen R n z at h
  rw [inf_eq_right.mpr hle] at h
  exact h.symm

/-- The actual section homomorphism on a refined original source open
preserves each original polynomial coefficient. -/
theorem sourceBaseChangeMap_appLE_refinedCoefficient (σ : R →+* S) (n : ℕ)
    (z : Chart.{u} n × ULift.{u} (Fin (n + 1))) (j : Fin (n + 1)) :
    (sourceBaseChangeMap σ n |>.appLE (refinedOpen R n z) (refinedOpen S n z)
      (sourceBaseChangeMap_preimage_refinedOpen σ n z).ge)
        (localCoefficient R n z.1 (refinedOpen R n z) (refinedOpen_le R n z) j) =
      localCoefficient S n z.1 (refinedOpen S n z) (refinedOpen_le S n z) j := by
  have h₁ := ConcreteCategory.congr_hom
    ((sourceBaseChangeMap σ n).map_appLE
      (sourceBaseChangeMap_preimage_refinedOpen σ n z).ge
      (homOfLE (refinedOpen_le R n z)).op)
    (localCoefficient R n z.1 (sourceOpen R n z.1) le_rfl j)
  change (sourceBaseChangeMap σ n |>.appLE (refinedOpen R n z) (refinedOpen S n z)
      (sourceBaseChangeMap_preimage_refinedOpen σ n z).ge)
      (sectionRestrict (source R n) (refinedOpen_le R n z)
        (localCoefficient R n z.1 (sourceOpen R n z.1) le_rfl j)) = _ at h₁
  rw [localCoefficient_restrict] at h₁
  have h₂ := ConcreteCategory.congr_hom
    ((sourceBaseChangeMap σ n).appLE_map
      (sourceBaseChangeMap_preimage_sourceOpen σ n z.1).ge
      (homOfLE (refinedOpen_le S n z)).op)
    (localCoefficient R n z.1 (sourceOpen R n z.1) le_rfl j)
  change sectionRestrict (source S n) (refinedOpen_le S n z)
      ((sourceBaseChangeMap σ n |>.appLE (sourceOpen R n z.1) (sourceOpen S n z.1)
        (sourceBaseChangeMap_preimage_sourceOpen σ n z.1).ge)
          (localCoefficient R n z.1 (sourceOpen R n z.1) le_rfl j)) = _ at h₂
  rw [sourceBaseChangeMap_appLE_localCoefficient, localCoefficient_restrict] at h₂
  exact h₁.trans h₂.symm

end AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct
