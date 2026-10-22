/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Gluing.OpenUnionPushout
public import Mathlib.AlgebraicGeometry.QuasiAffine

/-!
# Original coordinates for adjoining one affine open

The affine chart is its native section spectrum, and the overlap is the
literal open image inside that spectrum. All comparisons with the original
union and its other chart are retained as native isomorphisms and equations.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.FinitePresentationEnvelope.OpenUnionCoordinates

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}} (U V : X.Opens) [IsAffine U.toScheme]

/-- The original overlap, as an open of the second chart. -/
def overlap : V.toScheme.Opens := V.ι ⁻¹ᵁ U

/-- Its original map into the first affine chart's coordinate spectrum. -/
def toAffine : (overlap U V).toScheme ⟶ Spec Γ(U.toScheme, ⊤) :=
  (V.ι ∣_ U) ≫ U.toScheme.isoSpec.hom

instance : IsOpenImmersion (toAffine U V) := by
  dsimp [toAffine]
  infer_instance

/-- The literal open image in the first chart's spectrum. -/
def image : (Spec Γ(U.toScheme, ⊤)).Opens := (toAffine U V).opensRange

/-- The original overlap identifies with that literal open image. -/
def overlapIso : (overlap U V).toScheme ≅ (image U V).toScheme :=
  IsOpenImmersion.isoOfRangeEq (toAffine U V) (image U V).ι (by
    simp only [Opens.range_ι]
    rfl)

@[reassoc (attr := simp)]
theorem overlapIso_hom_ι :
    (overlapIso U V).hom ≫ (image U V).ι = toAffine U V :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The original inclusion of the second chart, expressed from the open image. -/
def toRight : (image U V).toScheme ⟶ V.toScheme :=
  (overlapIso U V).inv ≫ (overlap U V).ι

instance : IsOpenImmersion (toRight U V) := by
  dsimp [toRight]
  infer_instance

/-- The native inverse affine-coordinate isomorphism followed by the original inclusion. -/
def fromAffine : Spec Γ(U.toScheme, ⊤) ⟶ X := U.toScheme.isoSpec.inv ≫ U.ι

instance : IsOpenImmersion (fromAffine U) := by
  dsimp [fromAffine]
  infer_instance

/-- The actual coordinate span has the original union as its pushout. -/
theorem isPushout (hcover : U ⊔ V = ⊤) :
    IsPushout (image U V).ι (toRight U V) (fromAffine U) V.ι := by
  apply (Scheme.isPushout_opens_of_sup_eq_top U V hcover).of_iso
    (overlapIso U V) U.toScheme.isoSpec (Iso.refl _) (Iso.refl _)
  · exact (overlapIso_hom_ι U V).symm
  · simp [toRight, overlap]
  · simp [fromAffine]
  · simp

/-- A compact second chart makes the overlap compact in a quasi-separated union. -/
theorem overlap_isCompact [QuasiSeparatedSpace X]
    (hV : IsCompact (V : Set X)) :
    IsCompact (overlap U V : Set V.toScheme) := by
  have : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hV
  exact V.ι.isCompact_preimage (show IsCompact (U : Set X) from
    (show IsAffineOpen U from ‹IsAffine U.toScheme›).isCompact)

/-- The coordinate overlap image is compact, without a Noetherian assumption. -/
theorem image_isCompact [QuasiSeparatedSpace X]
    (hV : IsCompact (V : Set X)) :
    IsCompact (image U V : Set (Spec Γ(U.toScheme, ⊤))) := by
  have : CompactSpace (overlap U V).toScheme :=
    isCompact_iff_compactSpace.mp (overlap_isCompact U V hV)
  exact isCompact_range (toAffine U V).continuous

/-- The original compact overlap is quasi-affine because it embeds in the affine chart. -/
theorem overlap_isQuasiAffine [QuasiSeparatedSpace X]
    (hV : IsCompact (V : Set X)) : IsQuasiAffine (overlap U V).toScheme := by
  have : CompactSpace (overlap U V).toScheme :=
    isCompact_iff_compactSpace.mp (overlap_isCompact U V hV)
  exact IsQuasiAffine.of_isImmersion (toAffine U V)

end AlgebraicGeometry.Scheme.FinitePresentationEnvelope.OpenUnionCoordinates
