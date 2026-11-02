/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.RiemannRoch.EulerCharacteristic
public import Aglib.AlgebraicGeometry.Cohomology.Proper.EulerCharacteristic
public import Aglib.AlgebraicGeometry.Cohomology.Fibers.SeparatedFieldPoint
public import Aglib.AlgebraicGeometry.Modules.Invertible.RelativeFlat
public import Aglib.AlgebraicGeometry.Modules.Invertible.Power.Pullback
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.QuasiCoherent
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.FinitePresentation

/-!
# Locally constant genus of the original proper smooth curve fibres

The structure coefficient has original point-fibre Euler characteristic `1-g`.
The proper coherent Euler theorem makes this invariant locally constant. The
canonical residue-field factorization compares every field-valued fibre with
that same point-fibre invariant. An actual open neighbourhood therefore fixes
the genus, without a supplied uniform-genus certificate. Geometric connectedness
uses Mathlib's `ConnectedSpace` convention, including nonempty geometric fibres.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

variable {Y S : Scheme.{u}} (p : Y ⟶ S)

/-- The genus read from the original structure-coefficient Euler characteristic.
Its identification with the actual coherent genus is proved below. -/
def relativeGenus (x : S) : ℕ :=
  (1 - modulePointFiberEulerChar p (SheafOfModules.unit Y.ringCatSheaf) x).toNat

/-- The structural unit has Euler characteristic `1-g` on an actual curve. -/
theorem moduleEulerChar_unit_eq_one_sub_genus
    {K : Type u} [Field K] (C : FScheme K) (hC : Properties C) :
    moduleEulerChar C.hom (SheafOfModules.unit C.left.ringCatSheaf) =
      1 - (coherentGenus K C : ℤ) := by
  have h := moduleEulerChar_eq_curveDegree_add_one_sub_genus C hC (trivialLineBundle C.left)
  simp only [classOf_trivial, map_zero, zero_add] at h
  exact (moduleEulerChar_congr C.hom (PowerPullback.freeUnitIso C.left)).symm.trans h

/-- The actual field fibre and the original point fibre have the same structural
Euler characteristic, through the canonical residue-field map. -/
theorem moduleEulerChar_unit_fieldFibre [QuasiCompact p] [IsSeparated p]
    {K : Type u} [Field K] (t : Spec (.of K) ⟶ S) :
    moduleEulerChar (pullback.snd p t)
        (SheafOfModules.unit (pullback p t).ringCatSheaf) =
      modulePointFiberEulerChar p (SheafOfModules.unit Y.ringCatSheaf)
        (t (IsLocalRing.closedPoint K)) := by
  let x := t (IsLocalRing.closedPoint K)
  let σ := Scheme.descResidueField (Scheme.stalkClosedPointTo t)
  have ht : Spec.map σ ≫ S.fromSpecResidueField x = t :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K S t
  let b : pullback p t ⟶ pullback p (S.fromSpecResidueField x) :=
    pullback.map _ _ _ _ (𝟙 Y) (Spec.map σ) (𝟙 S) (by simp) (by simp [ht])
  let :
      (SheafOfModules.unit (pullback p (S.fromSpecResidueField x)).ringCatSheaf).IsQuasicoherent :=
    Modules.isQuasicoherent_unit _
  have hd (q : ℕ) :
      moduleCohomologyDimension (pullback.snd p t)
          (SheafOfModules.unit (pullback p t).ringCatSheaf) q =
        moduleCohomologyDimension (p.fiberToSpecResidueField x)
          ((Modules.pullback (p.fiberι x)).obj
            (SheafOfModules.unit Y.ringCatSheaf)) q := by
    have h := moduleCohomologyDimension_pullbackMap_of_eq_of_isSeparated p
      (S.fromSpecResidueField x) σ t ht
      (SheafOfModules.unit (pullback p (S.fromSpecResidueField x)).ringCatSheaf) q
    exact (moduleCohomologyDimension_congr (pullback.snd p t)
      (Modules.pullbackUnitIso b) q).symm.trans
        (h.trans (moduleCohomologyDimension_congr (p.fiberToSpecResidueField x)
          (Modules.pullbackUnitIso (p.fiberι x)) q).symm)
  rw [modulePointFiberEulerChar_eq_moduleEulerChar]
  unfold moduleEulerChar
  congr 1
  funext q
  rw [hd]

variable [SmoothOfRelativeDimension 1 p] [IsProper p] [GeometricallyConnected p]

/-- The actual fibre conditions follow by geometric base change. -/
theorem properties_fieldFibre {K : Type u} [Field K] (t : Spec (.of K) ⟶ S) :
    Properties (Over.mk (pullback.snd p t)) := by
  refine ⟨?_, ?_, ?_⟩
  · change SmoothOfRelativeDimension 1 (pullback.snd p t)
    exact MorphismProperty.pullback_snd p t inferInstance
  · change IsProper (pullback.snd p t)
    infer_instance
  · change GeometricallyConnected (pullback.snd p t)
    infer_instance

/-- Every original field-valued fibre has exactly the locally defined genus. -/
theorem coherentGenus_fieldFibre_eq_relativeGenus
    {K : Type u} [Field K] (t : Spec (.of K) ⟶ S) :
    coherentGenus K (Over.mk (pullback.snd p t)) =
      relativeGenus p (t (IsLocalRing.closedPoint K)) := by
  have h := moduleEulerChar_unit_eq_one_sub_genus
    (Over.mk (pullback.snd p t)) (properties_fieldFibre p t)
  change moduleEulerChar (pullback.snd p t)
    (SheafOfModules.unit (pullback p t).ringCatSheaf) = _ at h
  rw [moduleEulerChar_unit_fieldFibre p t] at h
  unfold relativeGenus
  rw [h]
  omega

variable [IsLocallyNoetherian S]

omit [GeometricallyConnected p] in
/-- Proper coherent Euler local constancy supplies genus local constancy. -/
theorem isLocallyConstant_relativeGenus : IsLocallyConstant (relativeGenus p) := by
  let : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  have hM : Modules.QuasiCoherent.affineLocallyFiniteType Y
      (SheafOfModules.unit Y.ringCatSheaf) := by
    let := lineBundle_isFinitePresentation Y (trivialLineBundle Y)
    exact (Modules.QuasiCoherent.affineLocallyFiniteType Y).prop_of_iso
      (PowerPullback.freeUnitIso Y)
      (Modules.QuasiCoherent.affineLocallyFiniteType_of_finitePresentation _)
  have hflat : Modules.relativeFlat p (SheafOfModules.unit Y.ringCatSheaf) :=
    Modules.relativeFlat_unit_of_flat p
  exact (isLocallyConstant_modulePointFiberEulerChar_of_proper p _ hM hflat).comp
    (fun z : ℤ => (1 - z).toNat)

/-- The actual genus level open containing a specified base point. -/
def genusNeighbourhood (x : S) : S.Opens :=
  ⟨{s | relativeGenus p s = relativeGenus p x},
    (isLocallyConstant_relativeGenus p).isOpen_fiber _⟩

omit [GeometricallyConnected p] in
@[simp]
theorem mem_genusNeighbourhood (x : S) : x ∈ genusNeighbourhood p x := rfl

/-- On this explicit neighbourhood every field-valued fibre has the same genus.
The value comes from the specified point, not a uniformity assumption. -/
theorem coherentGenus_eq_on_genusNeighbourhood (x : S)
    {K : Type u} [Field K] (t : Spec (.of K) ⟶ S)
    (ht : t (IsLocalRing.closedPoint K) ∈ genusNeighbourhood p x) :
    coherentGenus K (Over.mk (pullback.snd p t)) = relativeGenus p x :=
  (coherentGenus_fieldFibre_eq_relativeGenus p t).trans ht

end AlgebraicGeometry.Scheme.OverField.Curve
