/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.CurveImage
public import Aglib.AlgebraicGeometry.SchemeTheoreticImage.Integral
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.ReducedFactor
public import Aglib.AlgebraicGeometry.Curves.Projectivity.Graph

/-!
# The actual contracted curve over its image residue field

Take the schematic image of the original residue-field inclusion at the
curve generic point. This gives its actual integral closed scheme structure.
Reduced-source factorization through the original closed image point retains
the structural map to that point's original residue field. The native curve
coordinate theorem then supplies an actual affine transcendental unit.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.NormalizedPointDomination.CurveResidue

universe u

variable {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p]
  (C : IrreducibleCloseds X) (hC : C ∈ contractedCurves p)

/-- The original generic point of the actual irreducible closed curve. -/
abbrev point : X := C.isIrreducible.genericPoint

/-- The integral scheme-theoretic closure of its original residue-field inclusion. -/
abbrev curve : Scheme.{u} := (X.fromSpecResidueField (point C)).image

/-- The original closed immersion of the actual curve into its ambient model. -/
abbrev inclusion : curve C ⟶ X := (X.fromSpecResidueField (point C)).imageι

instance curve_isIntegral : IsIntegral (curve C) :=
  schemeImage_isIntegral (X.fromSpecResidueField (point C))

instance inclusion_isClosedImmersion : IsClosedImmersion (inclusion C) := inferInstance

/-- The support is exactly the selected curve, not an arbitrarily chosen component. -/
theorem range_inclusion : Set.range (inclusion C) = (C : Set X) := by
  change Set.range (X.fromSpecResidueField (point C)).ker.subschemeι = _
  rw [IdealSheafData.range_subschemeι, Hom.support_ker, range_fromSpecResidueField]
  exact C.isIrreducible.closure_genericPoint C.isClosed

/-- Its original closed immersion identifies the actual curve topology. -/
def curveHomeomorph : curve C ≃ₜ (C : Set X) :=
  (inclusion C).isEmbedding.toHomeomorph.trans (Homeomorph.setCongr (range_inclusion C))

omit [IsProper p] in
include hC in
/-- The actual integral curve scheme has dimension exactly one. -/
theorem curve_dimension : topologicalKrullDim (curve C) = 1 := by
  exact (IsHomeomorph.topologicalKrullDim_eq _ (curveHomeomorph C).isHomeomorph).trans hC.1

include hC in
/-- The image of the actual generic point is closed, by properness and the
actual contracted-curve property. -/
theorem isClosed_image_point : IsClosed ({p (point C)} : Set Y) := by
  have hpC : p '' (C : Set X) = {p (point C)} := by
    apply Set.Subset.antisymm
    · intro z hz
      exact hC.2 hz ⟨point C, (C.isIrreducible.isGenericPoint_genericPoint C.isClosed).mem, rfl⟩
    · exact Set.singleton_subset_iff.mpr
        ⟨point C, (C.isIrreducible.isGenericPoint_genericPoint C.isClosed).mem, rfl⟩
  exact hpC ▸ p.isClosedMap _ C.isClosed

/-- The original curve map factors through the original image-point residue
field, using reducedness rather than mere set-theoretic factorization. -/
def toPoint : curve C ⟶ Spec (Y.residueField (p (point C))) := by
  let : IsClosedImmersion (Y.fromSpecResidueField (p (point C))) :=
    isClosed_singleton_iff_isClosedImmersion.mp (isClosed_image_point p C hC)
  exact liftReducedToClosed (Y.fromSpecResidueField (p (point C))) (inclusion C ≫ p) (by
    rw [range_fromSpecResidueField]
    rintro z ⟨a, rfl⟩
    exact hC.2
      ⟨inclusion C a, (range_inclusion C) ▸ Set.mem_range_self a, rfl⟩
      ⟨point C, (C.isIrreducible.isGenericPoint_genericPoint C.isClosed).mem, rfl⟩)

/-- The field structure retains the exact original scheme triangle. -/
@[reassoc] theorem toPoint_comp :
    toPoint p C hC ≫ Y.fromSpecResidueField (p (point C)) = inclusion C ≫ p := by
  let : IsClosedImmersion (Y.fromSpecResidueField (p (point C))) :=
    isClosed_singleton_iff_isClosedImmersion.mp (isClosed_image_point p C hC)
  unfold toPoint
  exact liftReducedToClosed_fac _ _ _

/-- The original generic residue-field inclusion into its actual image. -/
abbrev fromGeneric : Spec (X.residueField (point C)) ⟶ curve C :=
  (X.fromSpecResidueField (point C)).toImage

instance fromGeneric_isDominant : IsDominant (fromGeneric C) := inferInstance

/-- The curve's structural constants agree with the original morphism's
residue-field map at the selected generic point. This is an equality of
actual scheme arrows, not a chosen abstract field isomorphism. -/
@[reassoc] theorem fromGeneric_toPoint :
    fromGeneric C ≫ toPoint p C hC = Spec.map (p.residueFieldMap (point C)) := by
  let : IsClosedImmersion (Y.fromSpecResidueField (p (point C))) :=
    isClosed_singleton_iff_isClosedImmersion.mp (isClosed_image_point p C hC)
  apply (cancel_mono (Y.fromSpecResidueField (p (point C)))).mp
  rw [Category.assoc, toPoint_comp, ← Category.assoc]
  change ((X.fromSpecResidueField (point C)).toImage ≫
    (X.fromSpecResidueField (point C)).imageι) ≫ p = _
  rw [Hom.toImage_imageι]
  exact (p.SpecMap_residueFieldMap_fromSpecResidueField (point C)).symm

/-- An actual affine unit transcendental for the original image-point scalars.
The later DVR argument must transport this section through the original
closed-immersion residue map; no abstract field identification is installed. -/
theorem exists_affine_transcendental_unit :
    ∃ U : (curve C).affineOpens, Nonempty U.1 ∧
      ∃ a : Γ(curve C, U.1),
        letI : Algebra (Y.residueField (p (point C))) Γ(curve C, U.1) :=
          (constantSection (Over.mk (toPoint p C hC)) U.1).toAlgebra
        Transcendental (Y.residueField (p (point C))) a ∧ IsUnit a := by
  let : IsIntegral (Over.mk (toPoint p C hC)).left := curve_isIntegral C
  exact OverField.Curve.GraphInput.exists_affine_transcendental_unit
    (Over.mk (toPoint p C hC)) (curve_dimension p C hC)

end AlgebraicGeometry.Scheme.NormalizedPointDomination.CurveResidue
