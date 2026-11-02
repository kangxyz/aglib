/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.HomSection

public import Aglib.AlgebraicGeometry.IdealSheaf.Modules

public import Aglib.AlgebraicGeometry.Blowup.IdealFrames
public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Normal.TwistedLine
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Basic
public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.Restriction
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Section.Basic
public import Aglib.AlgebraicGeometry.Modules.Tensor.Section


/-!
# The original global right-hand side of the one-pole unit square

The map is the original pulled-back coefficient followed by insertion of
the original dual ideal section. Its tensor pullback comparison is proved
before specializing to either parameter chart. No global one-pole map or
chart overlap is asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Blowup.RegularPoint AlgebraicGeometry.Scheme.Blowup.IdealFrames

universe u


open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Blowup

variable (Λ R : Type u) [CommRing Λ] [CommRing R] [Algebra Λ R]
  (I : Ideal R) (n : ℕ) (L : Invertible.LineBundle (Spec (.of R)))
  (φ : moduleExteriorPower (Spec (.of R))
    (relativeDifferentialSheaf (Spec.map (CommRingCat.ofHom (algebraMap Λ R)))) n ⟶ L.val)

local notation "Y" => canonicalBlowup I
local notation "P" => CategoryTheory.Functor.obj (pullback (blowdown I)) (Subtype.val L)
local notation "Q" => Subtype.val (Invertible.dualLineBundle Y (centreIdealLine I))
local notation "M" => moduleExteriorPower (Spec (CommRingCat.of R))
  (relativeDifferentialSheaf (Spec.map (CommRingCat.ofHom (algebraMap Λ R)))) n

/-- The same original exceptional section defines the intrinsic global unit-square target map. -/
def pairIdeal_onePoleUnitMap :
    (pullback (blowdown I)).obj M ⟶ (centreTwistedPullbackLine I L).val :=
  (pullback (blowdown I)).map φ ≫
    (positiveCartierTensorSection Y Q
      (InternalHom.transpose Y
        (Scheme.Hom.idealInclusion
          (centreι (Blowup.blowupDatum (Blowup.affineCenter R I)))))).app P ≫
    (tensorSheafBraiding Y Q P).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original global right-hand side pulls back using the same section and tensor map. -/
theorem pairIdeal_onePoleUnitMap_pullback {U : Scheme.{u}} (f : U ⟶ Y) :
    let s : SheafOfModules.unit (canonicalBlowup I).ringCatSheaf ⟶ Q :=
      InternalHom.transpose Y
        (Scheme.Hom.idealInclusion (centreι (Blowup.blowupDatum (Blowup.affineCenter R I))))
    (pullback f).map (pairIdeal_onePoleUnitMap Λ R I n L φ) ≫ pullbackTensorMap f P Q =
      (pullback f).map ((pullback (blowdown I)).map φ) ≫
        (positiveCartierTensorSection U ((pullback f).obj Q)
          ((pullbackUnitIso f).inv ≫ (pullback f).map s)).app ((pullback f).obj P) ≫
          (tensorSheafBraiding U ((pullback f).obj Q) ((pullback f).obj P)).hom := by
  intro s
  change (pullback f).map (((pullback (blowdown I)).map φ) ≫
    ((positiveCartierTensorSection Y Q s).app P ≫ (tensorSheafBraiding Y Q P).hom)) ≫
      pullbackTensorMap f P Q = _
  rw [CategoryTheory.Functor.map_comp, Category.assoc, pullback_positiveSection]

end AlgebraicGeometry.Scheme.Blowup
