/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Actual local rings and residue fields of rational points

A `RationalPoint F X` consists of a structure morphism `X ⟶ Spec F` and an actual
section of that morphism. Its point is the image of the unique point of `Spec F`,
and its local ring is the actual structure-sheaf stalk at that point.

The constants map is constructed using the structure morphism's `stalkMap` and
the canonical field-stalk isomorphism. The residue-field equivalence is
constructed using the section's `residueFieldMap`; no residue-field
identification is supplied as input. The section equation proves that
reduction retracts constants, including on units.

For an integral scheme, the fraction field is mathlib's `Scheme.functionField`,
which is the actual generic stalk with its canonical stalk-specialization map.
The constants map through the rational-point stalk is proved equal to the
structure morphism's constants map at the generic stalk. Regularity and Krull
dimension one of this exact local ring imply that it is a DVR. Deriving these
local hypotheses from global curve hypotheses remains a separate obligation.

## Source correspondence

Auxiliary rational-origin local algebra for
`research/exposes/K2/018/expose.tex`, `K2-018#sec:k2018-splitting`, lines 240–249,
and `K2-018#lem:k2018-residue-bockstein`, lines 308–339, at baseline commit
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Complete source-file SHA-256:
`e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299`.
The declarations supply elementary scheme and local-ring background for these
locators. They do not identify Milnor and Quillen K₂ or prove a Quillen
local-specialization square.

Implementation basis: `11577226da1f35a07a643107cbf374fb261f99f0`;
Lean `4.34.1`, mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
-/

@[expose] public section




noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme

/-- An actual rational section of the structure morphism of a scheme over a field. -/
structure RationalPoint (F : Type u) [Field F] (X : Scheme.{u}) where
  /-- The actual structure morphism from X to the base field spectrum. -/
  structureMap : X ⟶ Spec (.of F)
  /-- The specified rational section of the actual structure morphism. -/
  sectionMap : Spec (.of F) ⟶ X
  section_comp : sectionMap ≫ structureMap = 𝟙 _

namespace RationalPoint
variable {F : Type u} [Field F] {X : Scheme.{u}}

/-- The canonical identification of any stalk of `Spec F` with the field `F`. -/
def fieldStalkIso (F : Type u) [Field F] (s : Spec (.of F)) :
    (Spec (.of F)).presheaf.stalk s ≅ CommRingCat.of F :=
  (Spec (.of F)).presheaf.stalkCongr (.of_eq (Subsingleton.elim s (IsLocalRing.closedPoint F))) ≪≫
    stalkClosedPointIso (.of F)

/-- The actual scheme point selected by the rational section. -/
abbrev point (q : RationalPoint F X) : X := q.sectionMap (IsLocalRing.closedPoint F)
/-- The structure-sheaf stalk at the rational point. -/
abbrev localRing (q : RationalPoint F X) : CommRingCat := X.presheaf.stalk q.point

/-- Constants in an actual stalk, obtained from the structure morphism. -/
def constantsAt (q : RationalPoint F X) (x : X) : F →+* X.presheaf.stalk x :=
  ((fieldStalkIso F (q.structureMap x)).inv ≫ q.structureMap.stalkMap x).hom

/-- Constants in the actual rational-point local ring. -/
abbrev constants (q : RationalPoint F X) : F →+* q.localRing := q.constantsAt q.point

/-- The section induces an actual local map from the origin stalk to `F`. -/
def evaluation (q : RationalPoint F X) : q.localRing →+* F :=
  (Scheme.stalkClosedPointTo q.sectionMap).hom

/-- The section equation makes evaluation retract the stalk constants map. -/
lemma evaluation_comp_constants (q : RationalPoint F X) :
    q.evaluation.comp q.constants = RingHom.id F := by
  change ((fieldStalkIso F (q.structureMap q.point)).inv ≫
    q.structureMap.stalkMap q.point ≫
      (q.sectionMap.stalkMap (IsLocalRing.closedPoint F) ≫
        (stalkClosedPointIso (.of F)).hom)).hom =
      (𝟙 (CommRingCat.of F) : CommRingCat.of F ⟶ CommRingCat.of F).hom
  apply CommRingCat.hom_ext_iff.mp
  rw [← Category.assoc (q.structureMap.stalkMap q.point)]
  rw [← Scheme.Hom.stalkMap_comp]
  rw [Scheme.Hom.stalkMap_congr_hom _ _ q.section_comp,
    Scheme.Hom.stalkMap_id]
  simp [fieldStalkIso, TopCat.Presheaf.stalkCongr]

@[simp] lemma evaluation_constants (q : RationalPoint F X) (a : F) :
    q.evaluation (q.constants a) = a :=
  DFunLike.congr_fun q.evaluation_comp_constants a

instance fieldStalkHom_isLocal (F : Type u) [Field F] :
    IsLocalHom (stalkClosedPointIso (.of F)).hom.hom :=
  ⟨fun a ha => (isUnit_map_iff
    (stalkClosedPointIso (.of F)).commRingCatIsoToRingEquiv a).mp ha⟩

/-- The residue field at the unique point of `Spec F` is canonically `F`. -/
def fieldResidueEquiv (F : Type u) [Field F] :
    (Spec (.of F)).residueField (IsLocalRing.closedPoint F) ≃+* F :=
  RingEquiv.ofBijective
    (IsLocalRing.ResidueField.lift (stalkClosedPointIso (.of F)).hom.hom)
    ⟨RingHom.injective _, fun a => ⟨IsLocalRing.residue _
      ((stalkClosedPointIso (.of F)).inv a), by
      change (stalkClosedPointIso (.of F)).commRingCatIsoToRingEquiv
        ((stalkClosedPointIso (.of F)).commRingCatIsoToRingEquiv.symm a) = a
      exact (stalkClosedPointIso (.of F)).commRingCatIsoToRingEquiv.apply_symm_apply a⟩⟩

@[simp] lemma fieldResidueEquiv_residue (F : Type u) [Field F]
    (a : (Spec (.of F)).presheaf.stalk (IsLocalRing.closedPoint F)) :
    fieldResidueEquiv F (IsLocalRing.residue _ a) = (stalkClosedPointIso (.of F)).hom a := rfl

/-- The section's actual residue-field map, followed by the `Spec F` identification. -/
def residueToBase (q : RationalPoint F X) : X.residueField q.point →+* F :=
  (fieldResidueEquiv F).toRingHom.comp
    (q.sectionMap.residueFieldMap (IsLocalRing.closedPoint F)).hom

@[simp] lemma residueToBase_residue (q : RationalPoint F X) (r : q.localRing) :
    q.residueToBase (IsLocalRing.residue q.localRing r) = q.evaluation r := by
  change fieldResidueEquiv F
    (q.sectionMap.residueFieldMap (IsLocalRing.closedPoint F) (X.residue q.point r)) = _
  have h := ConcreteCategory.congr_hom
    (Scheme.residue_residueFieldMap q.sectionMap (IsLocalRing.closedPoint F)) r
  simp only [ConcreteCategory.comp_apply] at h
  rw [h]
  rfl

lemma residueToBase_constants (q : RationalPoint F X) (a : F) :
    q.residueToBase (IsLocalRing.residue q.localRing (q.constants a)) = a := by
  rw [residueToBase_residue, evaluation_constants]

/-- The actual residue field of a rational point is the base field. -/
def residueEquiv (q : RationalPoint F X) : X.residueField q.point ≃+* F :=
  RingEquiv.ofBijective q.residueToBase
    ⟨q.residueToBase.injective, fun a =>
      ⟨IsLocalRing.residue q.localRing (q.constants a), q.residueToBase_constants a⟩⟩

@[simp] lemma residueEquiv_residue (q : RationalPoint F X) (r : q.localRing) :
    q.residueEquiv (IsLocalRing.residue q.localRing r) = q.evaluation r :=
  q.residueToBase_residue r

lemma residueEquiv_constants (q : RationalPoint F X) (a : F) :
    q.residueEquiv (IsLocalRing.residue q.localRing (q.constants a)) = a :=
  q.residueToBase_constants a

@[simp] lemma residueEquiv_symm_apply (q : RationalPoint F X) (a : F) :
    q.residueEquiv.symm a = IsLocalRing.residue q.localRing (q.constants a) := by
  apply q.residueEquiv.injective
  simp

/-- Base-field units mapped to units of the actual origin stalk. -/
def constantUnits (q : RationalPoint F X) : Fˣ →* q.localRingˣ :=
  Units.map q.constants.toMonoidHom

/-- Actual residue reduction on stalk units, identified with the base field by the section. -/
def reductionUnits (q : RationalPoint F X) : q.localRingˣ →* Fˣ :=
  Units.map (q.residueEquiv.toRingHom.comp (IsLocalRing.residue q.localRing)).toMonoidHom

@[simp] lemma reductionUnits_constants (q : RationalPoint F X) (u : Fˣ) :
    q.reductionUnits (q.constantUnits u) = u := by
  apply Units.ext
  exact q.residueEquiv_constants (u : F)

lemma constants_isUnit (q : RationalPoint F X) {a : F} (ha : a ≠ 0) :
    IsUnit (q.constants a) :=
  (isUnit_iff_ne_zero.mpr ha).map q.constants

lemma fieldStalkIso_inv_stalkSpecializes (F : Type u) [Field F]
    {s t : Spec (.of F)} (h : s ⤳ t) :
    (fieldStalkIso F t).inv ≫ (Spec (.of F)).presheaf.stalkSpecializes h =
      (fieldStalkIso F s).inv := by
  have e : s = t := Subsingleton.elim _ _
  subst t
  simp

variable (q : RationalPoint F X)

section FunctionField
variable [IsIntegral X]

/-- Constants embedded through the origin stalk into the actual generic stalk. -/
def functionFieldConstants : F →+* X.functionField :=
  (algebraMap q.localRing X.functionField).comp q.constants

/-- Origin-stalk constants agree with constants from the structure map at the generic point. -/
lemma functionFieldConstants_eq_generic_stalkMap :
    q.functionFieldConstants = q.constantsAt (genericPoint X) := by
  change (((fieldStalkIso F (q.structureMap q.point)).inv ≫
    q.structureMap.stalkMap q.point) ≫
      X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)).hom = _
  apply CommRingCat.hom_ext_iff.mp
  rw [Category.assoc, ← Scheme.Hom.stalkSpecializes_stalkMap]
  rw [← Category.assoc, fieldStalkIso_inv_stalkSpecializes]

/-- The actual generic stalk is the fraction field of the actual origin stalk. -/
lemma localRing_isFractionRing : IsFractionRing q.localRing X.functionField := inferInstance

end FunctionField

/-- An integral scheme's regular local ring of dimension one is an actual DVR.
The local regularity and dimension hypotheses remain explicit. -/
lemma localRing_isDiscreteValuationRing [IsIntegral X] [IsRegularLocalRing q.localRing]
    (hdim : ringKrullDim q.localRing = 1) : IsDiscreteValuationRing q.localRing := by
  have hn : ¬ IsField q.localRing := by
    intro hf
    have hzero := ringKrullDim_eq_zero_of_isField hf
    rw [hdim] at hzero
    exact one_ne_zero hzero
  have hspan : (IsLocalRing.maximalIdeal q.localRing).spanFinrank = 1 := by
    have h := (IsRegularLocalRing.spanFinrank_maximalIdeal (R := q.localRing)).trans hdim
    exact_mod_cast h
  exact ((IsDiscreteValuationRing.TFAE q.localRing hn).out 5 1).mp
    ((Submodule.spanFinrank_eq_one_iff _).mp hspan).1

end RationalPoint
end AlgebraicGeometry.Scheme

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/Stalk/RationalPoint.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 685e6c8bdd684459b21599d3d01992f65d07cd1c99fcdb114a48b94a2260d83c.
Native names and imports replace the source wrappers; stated conditions and maps are retained. -/
