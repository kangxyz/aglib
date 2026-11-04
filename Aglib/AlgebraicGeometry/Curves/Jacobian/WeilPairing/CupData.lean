/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.WeilPairing.AbelKummer
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.ConstantCoefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.Trace
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.PointPurity

/-! The original Kummer classes and signed cup trace for the Weil comparison. -/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonObj
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Scheme.Group Scheme.RelativePicard Scheme.EtaleCohomology
open Scheme.EtaleCohomology.Coefficients

universe u

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Properties X)
  (P : LocallyNoetherianOver (Base k)) [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Base k)).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : k))

set_option hygiene false in
local notation "Λ" => ULift.{u + 1} (ZMod n)
set_option hygiene false in
local notation "J" => picardIdentityComponent X.hom P R
set_option hygiene false in
local notation "T₀" => 𝟙_ (FScheme k)

/-- The standard Ext realization for the original abelian sheaves. -/
local instance originalAbelianExt (Y : Scheme.{u}) : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Y) :=
  hasExtStandard Y
/-- The standard Ext realization for the original finite coefficient modules. -/
local instance originalModuleExt (Y : Scheme.{u}) : HasExt.{u + 2} (ModuleSheaf Y Λ) :=
  SheafOfModules.hasExt (constantRing Y Λ)

/-- The original inverse Kummer class of the original field kernel point. -/
abbrev jacobianKernelPointRootsOne
    (x : letI := picardCommGrpObj X.hom P R
      letI : GrpObj (J) := grpObjPicardIdentityComponent X.hom P R
      letI : IsCommMonObj (J) := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
      (T₀) ⟶ (MultiplicationKernel.kernelGroup (Grp.mk (J)) n).X) :=
  letI := picardCommGrpObj X.hom P R
  letI : GrpObj (J) := grpObjPicardIdentityComponent X.hom P R
  letI : IsCommMonObj (J) := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
  (rootsOneJacobianTorsionAddEquiv.{u, u + 2} hX P R n hn hu).symm
    (jacobianRationalTorsionOfKernelPoint P R n x)

/-- The same original class in the original module-unit Ext group. -/
abbrev jacobianKernelPointModuleRootsOne
    (x : letI := picardCommGrpObj X.hom P R
      letI : GrpObj (J) := grpObjPicardIdentityComponent X.hom P R
      letI : IsCommMonObj (J) := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
      (T₀) ⟶ (MultiplicationKernel.kernelGroup (Grp.mk (J)) n).X) :=
  (moduleRootsUnitExtCohomologyAddEquiv X.left n 1).symm
    (jacobianKernelPointRootsOne hX P R n hn hu x)

/-- The original field constant-root identification pulled to the original curve. -/
abbrev jacobianCupRootsIso :
    moduleUnit X.left Λ ≅ moduleRootsOfUnity X.left n :=
  let e := moduleUnitRootsIso k n hn hu (𝟙 (Base k))
  let F := moduleInverseImage X.hom Λ
  (moduleUnitInverseImageIso X.hom n).symm ≪≫ F.mapIso e ≪≫
    moduleRootsOfUnityInverseImageIso X.hom n hn
      (modulePoint_globalLevelInvertible (C := (T₀)) n hu)

/-- The signed trace of the original Yoneda product with the character
slot first and the point slot second. -/
abbrev jacobianSignedCupTrace
    (x y : letI := picardCommGrpObj X.hom P R
      letI : GrpObj (J) := grpObjPicardIdentityComponent X.hom P R
      letI : IsCommMonObj (J) := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
      (T₀) ⟶ (MultiplicationKernel.kernelGroup (Grp.mk (J)) n).X) : ZMod n :=
  let e := jacobianCupRootsIso (X := X) n hn hu
  let x₁ := jacobianKernelPointModuleRootsOne hX P R n hn hu x
  let y₁ := jacobianKernelPointModuleRootsOne hX P R n hn hu y
  let u := y₁.comp (Ext.mk₀ e.inv) (add_zero 1)
  let w := -(u.comp x₁ (rfl : 1 + 1 = 2))
  Curves.traceAddEquiv hX n hn hu (modulePoint_globalLevelInvertible (C := X) n hu)
    (moduleRootsUnitExtCohomologyAddEquiv X.left n 2 w)

end AlgebraicGeometry.Scheme.OverField.Curve
