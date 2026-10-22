/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.OpenExtension

/-!
# Extension of centres from a closed subscheme

The native pushforward ideal along a closed immersion pulls back to the
original ideal. If that ideal avoids the inverse image of a protected open,
the same literal pushforward ideal avoids the protected ambient open.
Neither statement requires reducedness or a Noetherian hypothesis.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Z : Scheme.{u}}

/-- A centre on a closed subscheme extends by its native pushforward ideal,
with equality of its actual pullback ideal. -/
@[simp]
theorem comap_map_of_isClosedImmersion (J : Z.IdealSheafData) (i : Z ⟶ X)
    [IsClosedImmersion i] : (J.map i).comap i = J := by
  have h : IsPullback J.subschemeι (𝟙 _) i (J.subschemeι ≫ i) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  rw [map, ← ker_fst_of_isClosedImmersion,
    ← Hom.ker_comp_of_isIso h.isoPullback.hom, h.isoPullback_hom_fst,
    ker_subschemeι]

/-- The same extended centre avoids the entire prescribed ambient open. -/
theorem exists_closed_extension_eq_top (J : Z.IdealSheafData) (i : Z ⟶ X)
    [IsClosedImmersion i] (V : X.Opens)
    (hJ : J.comap (i ⁻¹ᵁ V).ι = ⊤) :
    ∃ I : X.IdealSheafData, I.comap i = J ∧ I.comap V.ι = ⊤ :=
  ⟨J.map i, J.comap_map_of_isClosedImmersion i,
    J.map_comap_eq_top_of_comap_eq_top i V hJ⟩

end AlgebraicGeometry.Scheme.IdealSheafData
