/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Cartesian isomorphism restrictions

Source: `lean/R5Lab/Aglib/AlgebraicGeometry/Morphisms/Isomorphism/CartesianRestriction.lean`.
Frozen R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `afa3f64c57d9ed93d0343360e8896a412889eeee4892578dfbe86e564fe4b291`.
Native objects and proved suppliers replace application provenance and redundant premises.
-/

@[expose] public section


noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Isomorphism neighborhoods pull back to the actual restricted fibre map. -/
theorem isIso_restrict_of_isPullback
    {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X}
    {iX : X ⟶ S} {iY : Y ⟶ T} (H : IsPullback g iY iX f)
    (U : S.Opens) [IsIso (f ∣_ U)] : IsIso (g ∣_ (iX ⁻¹ᵁ U)) := by
  have h := Scheme.Hom.isPullback_resLE H (US := U) (UT := f ⁻¹ᵁ U)
    (UX := iX ⁻¹ᵁ U) le_rfl le_rfl
    (UY := g ⁻¹ᵁ (iX ⁻¹ᵁ U)) (by
      rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage]
      exact (inf_idem _).symm)
  have : IsIso (f.resLE U (f ⁻¹ᵁ U) le_rfl) := by
    simpa [Scheme.Hom.resLE] using (inferInstance : IsIso (f ∣_ U))
  simpa [Scheme.Hom.resLE] using h.isIso_fst_of_isIso

end AlgebraicGeometry.Scheme.Hom
