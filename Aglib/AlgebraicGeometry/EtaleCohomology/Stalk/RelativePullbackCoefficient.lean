/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.PullbackLimitCoefficient

/-! # Fixed coefficients on actual relative inverse scheme systems -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe u uI vI
attribute [local instance] hasSheafifyLarge
open Continuity

variable {I : Type uI} [Category.{vI} I] {X : Scheme.{u}} (D : I ⥤ Over X)

/-- Structural maps of the actual relative system, in the coefficient direction. -/
def relativeCoefficientBaseCone : Cone (D ⋙ Over.forget X).op :=
  ((Over.forgetCocone X).whisker D).op

/-- The actual relative inverse system carries the fixed original coefficients. -/
def relativePullbackCoefficientSystem (F : AbelianSheaf.{u, u + 1} X) :
    DiagramCoefficientSystem (D ⋙ Over.forget X).op :=
  pullbackCoefficientSystem _ (relativeCoefficientBaseCone D) F

/-- The structural map of a relative cone is exactly the compatible composite. -/
theorem relativeCoefficient_cone_composite (c : Cone D) (i : Iᵒᵖ) :
    (relativeCoefficientBaseCone D).π.app i ≫
        (((Over.forget X).mapCone c).op).ι.app i = c.pt.hom.op :=
  congrArg Quiver.Hom.op (Over.w (c.π.app i.unop))

variable [IsConnected Iᵒᵖ] (c : Cone D) (F : AbelianSheaf.{u, u + 1} X)
  [hcolim : HasColimit (coneCoefficientFunctor (D ⋙ Over.forget X).op
    (((Over.forget X).mapCone c).op) (relativePullbackCoefficientSystem D F))]

/-- The original coefficient colimit is the literal pullback to the actual relative cone point. -/
def relativePullbackLimitCoefficientIso :
    colimit (coneCoefficientFunctor (D ⋙ Over.forget X).op
      (((Over.forget X).mapCone c).op) (relativePullbackCoefficientSystem D F)) ≅
        (inverseImage c.pt.hom).obj F := by
  let : HasColimit (coneCoefficientFunctor (D ⋙ Over.forget X).op
      (((Over.forget X).mapCone c).op)
      (pullbackCoefficientSystem _ (relativeCoefficientBaseCone D) F)) := hcolim
  exact pullbackLimitCoefficientIso _ (relativeCoefficientBaseCone D)
    (((Over.forget X).mapCone c).op) c.pt.hom.op
    (relativeCoefficient_cone_composite D c) F

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
