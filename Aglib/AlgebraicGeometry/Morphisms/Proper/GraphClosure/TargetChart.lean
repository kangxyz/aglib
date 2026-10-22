/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.GraphClosure

/-!
# Target-chart control for an original graph closure

Suppose the original source is separated over the base and its partial map
is closed in an open of the target. The original graph identifies its domain
with the inverse image of that target open in the graph closure. If the target
is proper, this is also the inverse image of the original source open.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.GraphClosure

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (U : X.Opens)
  (h : U.toScheme ⟶ Y) (w : U.ι ≫ f = h ≫ g)

instance toTarget_isSeparated [IsSeparated f] :
    IsSeparated (toTarget f g U h w) := by
  dsimp only [toTarget]
  infer_instance

variable (W : Y.Opens) (j : U.toScheme ⟶ W.toScheme) (hj : j ≫ W.ι = h)

/-- The original graph map, lifted to the inverse image of its specified target chart. -/
def fromOpenToTargetPreimage : U.toScheme ⟶ ((toTarget f g U h w) ⁻¹ᵁ W).toScheme :=
  IsOpenImmersion.lift ((toTarget f g U h w) ⁻¹ᵁ W).ι (fromOpen f g U h w) (by
    rw [Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change (fromOpen f g U h w ≫ toTarget f g U h w) x ∈ W
    rw [fromOpen_toTarget, ← hj]
    exact (j x).property)

@[reassoc (attr := simp)]
theorem fromOpenToTargetPreimage_ι :
    fromOpenToTargetPreimage f g U h w W j hj ≫ ((toTarget f g U h w) ⁻¹ᵁ W).ι =
      fromOpen f g U h w := IsOpenImmersion.lift_fac _ _ _

/-- The target-restricted original graph projection is the specified closed chart map. -/
@[reassoc (attr := simp)]
theorem fromOpenToTargetPreimage_restrict :
    fromOpenToTargetPreimage f g U h w W j hj ≫ (toTarget f g U h w ∣_ W) = j := by
  apply (cancel_mono W.ι).mp
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc,
    fromOpenToTargetPreimage_ι, fromOpen_toTarget, hj]

instance fromOpenToTargetPreimage_isOpenImmersion [QuasiSeparated g] [QuasiCompact U.ι] :
    IsOpenImmersion (fromOpenToTargetPreimage f g U h w W j hj) := by
  have : IsOpenImmersion
      (fromOpenToTargetPreimage f g U h w W j hj ≫ ((toTarget f g U h w) ⁻¹ᵁ W).ι) := by
    rw [fromOpenToTargetPreimage_ι]
    infer_instance
  exact IsOpenImmersion.of_comp _ ((toTarget f g U h w) ⁻¹ᵁ W).ι

instance fromOpenToTargetPreimage_isDominant [QuasiSeparated g] [QuasiCompact U.ι] :
    IsDominant (fromOpenToTargetPreimage f g U h w W j hj) := by
  have : IsDominant
      (fromOpenToTargetPreimage f g U h w W j hj ≫ ((toTarget f g U h w) ⁻¹ᵁ W).ι) := by
    rw [fromOpenToTargetPreimage_ι]
    infer_instance
  exact IsDominant.of_comp_of_isOpenImmersion _ ((toTarget f g U h w) ⁻¹ᵁ W).ι

instance fromOpenToTargetPreimage_isClosedImmersion [IsSeparated f] [IsClosedImmersion j] :
    IsClosedImmersion (fromOpenToTargetPreimage f g U h w W j hj) := by
  have : IsClosedImmersion
      (fromOpenToTargetPreimage f g U h w W j hj ≫ (toTarget f g U h w ∣_ W)) := by
    rw [fromOpenToTargetPreimage_restrict]
    infer_instance
  exact IsClosedImmersion.of_comp _ (toTarget f g U h w ∣_ W)

/-- An original partial graph closed in the target chart fills that chart of its closure. -/
theorem isIso_fromOpenToTargetPreimage
    [IsSeparated f] [QuasiSeparated g] [QuasiCompact U.ι] [IsClosedImmersion j] :
    IsIso (fromOpenToTargetPreimage f g U h w W j hj) := by
  let a := fromOpenToTargetPreimage f g U h w W j hj
  let : Surjective a := surjective_of_isDominant_of_isClosed_range a
    a.isClosedEmbedding.isClosed_range
  exact (isIso_iff_isOpenImmersion_and_surjective a).mpr ⟨inferInstance, inferInstance⟩

include hj in
/-- The graph domain is exactly the inverse image of the specified target chart. -/
theorem fromOpen_opensRange_eq_targetPreimage
    [IsSeparated f] [QuasiSeparated g] [QuasiCompact U.ι] [IsClosedImmersion j] :
    (fromOpen f g U h w).opensRange = (toTarget f g U h w) ⁻¹ᵁ W := by
  let := isIso_fromOpenToTargetPreimage f g U h w W j hj
  simpa only [fromOpenToTargetPreimage_ι, Opens.opensRange_ι] using
    (Hom.opensRange_comp_of_isIso (fromOpenToTargetPreimage f g U h w W j hj)
      ((toTarget f g U h w) ⁻¹ᵁ W).ι)

include hj in
/-- For a proper target, the original source and target chart preimages coincide. -/
theorem targetPreimage_eq_sourcePreimage
    [IsSeparated f] [IsProper g] [QuasiCompact U.ι] [IsClosedImmersion j] :
    (toTarget f g U h w) ⁻¹ᵁ W = (toSource f g U h w) ⁻¹ᵁ U := by
  let : IsIso (fromOpenToPreimage f g U h w) := by
    rw [← toSourceRestrictIso_inv]
    infer_instance
  rw [← fromOpen_opensRange_eq_targetPreimage f g U h w W j hj]
  simpa only [fromOpenToPreimage_ι, Opens.opensRange_ι] using
    (Hom.opensRange_comp_of_isIso (fromOpenToPreimage f g U h w)
      ((toSource f g U h w) ⁻¹ᵁ U).ι)

end AlgebraicGeometry.Scheme.GraphClosure
