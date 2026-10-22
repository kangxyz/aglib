/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Identifying closed models with the same schematically dense source

Two closed embeddings with the same schematically dense parametrization have
equal native kernel ideal sheaves. Their resulting isomorphism preserves both
the ambient embedding and the original source, including on nonreduced schemes.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {T Z₁ Z₂ X : Scheme.{u}}
variable (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X)
    (t₁ : T ⟶ Z₁) (t₂ : T ⟶ Z₂)
    [IsSchemeTheoreticallyDominant t₁] [IsSchemeTheoreticallyDominant t₂]
    (w : t₁ ≫ i₁ = t₂ ≫ i₂)

include t₁ t₂ w in
/-- Common schematic density identifies the actual kernel ideal sheaves. -/
lemma ker_eq_of_common_schematicallyDense_source : i₁.ker = i₂.ker := by
  simpa only [Hom.ker_comp, Hom.ker_eq_bot, IdealSheafData.map_bot] using
    congrArg Hom.ker w

variable [IsClosedImmersion i₁] [IsClosedImmersion i₂]

/-- The canonical closed-model isomorphism induced by a common dense source. -/
def closedIsoOfCommonDenseSource : Z₁ ≅ Z₂ := by
  let h := ker_eq_of_common_schematicallyDense_source i₁ i₂ t₁ t₂ w
  let f := IsClosedImmersion.lift i₂ i₁ h.symm.le
  letI : IsIso f := IsClosedImmersion.isIso_lift i₂ i₁ h.symm
  exact asIso f

@[reassoc (attr := simp)]
lemma closedIsoOfCommonDenseSource_hom_comp :
    (closedIsoOfCommonDenseSource i₁ i₂ t₁ t₂ w).hom ≫ i₂ = i₁ :=
  IsClosedImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
lemma comp_closedIsoOfCommonDenseSource_hom :
    t₁ ≫ (closedIsoOfCommonDenseSource i₁ i₂ t₁ t₂ w).hom = t₂ := by
  apply (cancel_mono i₂).mp
  rw [Category.assoc, closedIsoOfCommonDenseSource_hom_comp]
  exact w

end AlgebraicGeometry.Scheme
