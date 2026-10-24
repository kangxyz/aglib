/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.BoundedFamily.TorsionLocus
public import Aglib.AlgebraicGeometry.Modules.Invertible.Power.Pullback

/-! # The closed power locus has exactly the actual torsion fibres

Membership in the actual closed nonvanishing support is equivalent to an
actual unit isomorphism for the power of the original parameter fibre.
All points retain their own residue fields; neither algebraic closure nor
a set of abstract Picard representatives replaces the parameter scheme.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

variable {k : Type u} [Field k] (X : FScheme k)
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)

/-- The actual power-family fibre on the original curve after the indicated
residue-field extension. -/
def powerPointFibreLineBundle (g n : ℕ) (y : (parameter X.hom g).left) :
    LineBundle (pullback X.hom
      ((parameter X.hom g).left.fromSpecResidueField y ≫ (parameter X.hom g).hom)) :=
  pullbackLineBundle (Hom.familyMap X.hom (parameter X.hom g).hom
    ((parameter X.hom g).left.fromSpecResidueField y ≫ (parameter X.hom g).hom)
    ((parameter X.hom g).left.fromSpecResidueField y) rfl)
    (powerLineBundle X.hom o ho g n)

variable (hX : Properties X)

include hX

/-- The actual H0 threshold is exactly actual power-fibre triviality. -/
theorem powerH0Dimension_pos_iff_fibre_trivial (g n : ℕ)
    (y : (parameter X.hom g).left) :
    0 < powerH0Dimension X.hom o ho g n y ↔
      Nonempty ((powerPointFibreLineBundle X o ho g n y).val ≅
        SheafOfModules.unit (pullback X.hom
          ((parameter X.hom g).left.fromSpecResidueField y ≫
            (parameter X.hom g).hom)).ringCatSheaf) := by
  let t := (parameter X.hom g).left.fromSpecResidueField y ≫ (parameter X.hom g).hom
  let a := (parameter X.hom g).left.fromSpecResidueField y
  let Z : FScheme ((parameter X.hom g).left.residueField y) := Over.mk (pullback.snd X.hom t)
  have hZ : Properties Z := curveProperties_baseChange hX _ t
  let : IsIntegral Z.left := PointDivisor.isIntegral_of_properties Z hZ
  let : IsNoetherian Z.left := curveProperties_isNoetherian hZ
  let (x : ClosedPoint Z.left) := PointDivisor.isDiscreteValuationRing_stalk Z hZ x
  let : IsProper Z.hom := hZ.proper
  let : GeometricallyIntegral Z.hom :=
    curveProperties_geometricallyIntegral smoothFieldNormality normalComponentsOpen hZ
  let L := powerPointFibreLineBundle X o ho g n y
  have hd := powerLineBundle_degree_at_field_point X.hom o ho t a rfl hZ n
  have hdim := curveProperties_dimension smoothFieldDimension hZ
  have hdegree : Picard.Degree.lineBundleDegree Z.left Z.hom hdim.le
      (Picard.Degree.properCurveProductFormula _ Z.left Z.hom hdim) L = 0 := hd
  rw [powerH0Dimension_eq_fibre]
  exact Picard.TorsionSections.lineBundle_pos_h0_finrank_iff_trivial_of_proper
    Z hdim L hdegree

/-- The actual closed support consists precisely of points whose actual
power fibre has a unit isomorphism. -/
theorem mem_powerNonvanishingSupport_iff_fibre_trivial (g n : ℕ)
    (y : (parameter X.hom g).left) :
    y ∈ powerNonvanishingSupport X.hom o ho g n ↔
      Nonempty ((powerPointFibreLineBundle X o ho g n y).val ≅
        SheafOfModules.unit (pullback X.hom
          ((parameter X.hom g).left.fromSpecResidueField y ≫
            (parameter X.hom g).hom)).ringCatSheaf) := by
  rw [mem_powerNonvanishingSupport]
  exact powerH0Dimension_pos_iff_fibre_trivial X o ho hX g n y

/-- Every point of the actual reduced closed locus supplies an actual power
trivialization on its original residue-field fibre. -/
theorem powerPointFibreLineBundle_trivial_on_locus (g n : ℕ)
    (z : powerNonvanishingLocus X.hom o ho g n) :
    Nonempty ((powerPointFibreLineBundle X o ho g n
      (powerNonvanishingι X.hom o ho g n z)).val ≅
        SheafOfModules.unit (pullback X.hom
          ((parameter X.hom g).left.fromSpecResidueField
            (powerNonvanishingι X.hom o ho g n z) ≫
              (parameter X.hom g).hom)).ringCatSheaf) :=
  (powerH0Dimension_pos_iff_fibre_trivial X o ho hX g n _).mp
    (powerH0Dimension_pos_on_locus X.hom o ho g n z)

/-- Membership is also expressed as a trivialization of the actual tensor
power of the actual original fibre, using the canonical power-pullback map. -/
theorem mem_powerNonvanishingSupport_iff_fibre_power_trivial (g n : ℕ)
    (y : (parameter X.hom g).left) :
    let a := (parameter X.hom g).left.fromSpecResidueField y
    let f := Hom.familyMap X.hom (parameter X.hom g).hom
      (a ≫ (parameter X.hom g).hom) a rfl
    y ∈ powerNonvanishingSupport X.hom o ho g n ↔
      Nonempty ((tensorPowerLineBundle _
        (pullbackLineBundle f (lineBundle X.hom o ho g)) n).val ≅
          SheafOfModules.unit (pullback X.hom
            (a ≫ (parameter X.hom g).hom)).ringCatSheaf) := by
  dsimp only
  rw [mem_powerNonvanishingSupport_iff_fibre_trivial X o ho hX]
  let f := Hom.familyMap X.hom (parameter X.hom g).hom
    ((parameter X.hom g).left.fromSpecResidueField y ≫ (parameter X.hom g).hom)
    ((parameter X.hom g).left.fromSpecResidueField y) rfl
  let e := PowerPullback.pullbackPowerIso f (lineBundle X.hom o ho g) n
  exact ⟨fun ⟨d⟩ => ⟨e.symm ≪≫ d⟩, fun ⟨d⟩ => ⟨e ≪≫ d⟩⟩

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily
