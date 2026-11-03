/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Differentials.RegularPair.OnePoleChart
public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.Cartier
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Frame
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.FrameCoefficient
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.AffineMultiplication


/-!
# Original exceptional section in its actual regular-pair chart frame

The original positive exceptional section is the transpose of the actual
centre ideal inclusion. Its pullback through the original structural unit
has coefficient exactly x in the actual dual ideal frame. This follows
from original dual-frame evaluation and the original chart ideal inclusion.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Blowup.RegularPoint AlgebraicGeometry.Scheme.Blowup.IdealFrames

universe u


open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Blowup.RegularPair

private theorem cartier_section_eq {D Y : Scheme.{u}} (i : D ⟶ Y) :
    cartierDualIdealSection i = InternalHom.transpose Y (Scheme.Hom.idealInclusion i) := rfl

private theorem retained_line_frame_coefficient {X Y : Scheme.{u}}
    (L : LineBundle Y) (φ : L.val ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ (dualLineBundle Y L).val)
    (hs : s = InternalHom.transpose Y φ) (f : X ⟶ Y)
    (e : SheafOfModules.unit X.ringCatSheaf ≅ (pullback f).obj L.val)
    (r : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (hr : e.hom ≫ (pullback f).map φ ≫ (pullbackUnitIso f).hom = r) :
    ((pullbackUnitIso f).inv ≫ (pullback f).map s) ≫
      (Scheme.Modules.Invertible.dualPullbackFrame f L e).inv = r := by
  have he := dualPullbackFrame_transpose_coordinate f L e φ
  have ht := congrArg (fun v =>
    ((pullbackUnitIso f).inv ≫ (pullback f).map v) ≫
      (Scheme.Modules.Invertible.dualPullbackFrame f L e).inv) hs
  exact ht.trans (he.trans hr)

private theorem coordinate_transport {C : Type*} [Category C] {A B D : C}
    {s : A ⟶ B} {a b : B ⟶ D} {r t : A ⟶ D}
    (h : s ≫ a = r) (ha : b = a) (hr : r = t) : s ≫ b = t :=
  (congrArg (fun q => s ≫ q) ha).trans (h.trans hr)

variable (R : Type u) [CommRing R] (x y : R)

local notation "I" => Ideal.span (Set.insert x (Set.singleton y))
local notation "S" => Localization.Away.saturatedChart R I x
local notation "B" => Blowup.blowupDatum (Blowup.affineCenter R I)
local notation "a" => firstGenerator I x y rfl
local notation "c" => chartMap B a

private theorem exceptionalPositiveFrame_inv_eq :
    (saturatedPairExceptionalPositiveFrame R x y).inv =
      (Scheme.Modules.Invertible.dualPullbackFrame c (centreIdealLine I)
        (chartFrame B a)).inv := rfl

private theorem exceptionalScalar_eq :
    tilde.map (ModuleCat.ofHom (LinearMap.mulLeft (Blowup.affineBlowupAlgebra R I a)
      (algebraMap R (Blowup.affineBlowupAlgebra R I a) a))) =
    Scheme.Modules.affineMultiplication S (algebraMap R S x) := rfl

/-- The original exceptional positive section has the original denominator
as its coordinate in the actual dual chart ideal frame. -/
theorem saturatedPair_exceptionalPositiveSection_coordinate :
    let f : Spec (.of S) ⟶ canonicalBlowup I := c
    let s : SheafOfModules.unit (canonicalBlowup I).ringCatSheaf ⟶
        (dualLineBundle (canonicalBlowup I) (centreIdealLine I)).val :=
      cartierDualIdealSection (centreι B)
    ((pullbackUnitIso f).inv ≫ (pullback f).map s) ≫
      (saturatedPairExceptionalPositiveFrame R x y).inv =
    Scheme.Modules.affineMultiplication S (algebraMap R S x) := by
  intro f s
  let e : SheafOfModules.unit (Spec (.of S)).ringCatSheaf ≅
      (pullback f).obj (centreIdealLine I).val := chartFrame B a
  have h := retained_line_frame_coefficient (X := Spec (.of S)) (centreIdealLine I)
    (Scheme.Hom.idealInclusion (centreι B)) s
    (cartier_section_eq (centreι B)) f e _ (chartFrame_inclusion B a)
  exact coordinate_transport (C := (Spec (.of S)).Modules) h
    (exceptionalPositiveFrame_inv_eq R x y) (exceptionalScalar_eq R x y)

/-- The original positive section is multiplication by the actual denominator
followed by the actual inverse-ideal frame, with positive sign. -/
theorem saturatedPair_exceptionalPositiveSection_frame :
    let f : Spec (.of S) ⟶ canonicalBlowup I := c
    let s : SheafOfModules.unit (canonicalBlowup I).ringCatSheaf ⟶
        (dualLineBundle (canonicalBlowup I) (centreIdealLine I)).val :=
      cartierDualIdealSection (centreι B)
    (pullbackUnitIso f).inv ≫ (pullback f).map s =
      Scheme.Modules.affineMultiplication S (algebraMap R S x) ≫
        (saturatedPairExceptionalPositiveFrame R x y).hom := by
  intro f s
  let t := (pullbackUnitIso f).inv ≫
    (pullback f).map s
  let e := saturatedPairExceptionalPositiveFrame R x y
  have hs : (t ≫ e.inv) ≫ e.hom = t :=
    (Category.assoc t e.inv e.hom).trans
      ((congrArg (fun q => t ≫ q) e.inv_hom_id).trans (Category.comp_id t))
  exact hs.symm.trans (congrArg (fun t => t ≫ e.hom)
    (saturatedPair_exceptionalPositiveSection_coordinate R x y))

end AlgebraicGeometry.Scheme.Blowup.RegularPair
