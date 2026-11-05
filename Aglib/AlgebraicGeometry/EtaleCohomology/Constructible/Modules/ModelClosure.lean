/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteDiagrams

/-! # Actual model descent through the native finite-colimit closure

The original object-model property is stable under finite colimits. The proof
first descends the whole finite diagram, including its original arrows and
functor equations, and then takes its actual colimit at that stage. The
native original inverse image supplies the comparison isomorphism.

The final closure induction isolates the geometric generator-model input.
It does not assert that an affine-base etale model theorem applies to a
nonaffine base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule
namespace ModelDescent

universe u v

attribute [local instance] ModuleCat.Sheaf.hasSheafify Cardinal.fact_isRegular_aleph0

open Constructible.Modules.NativeFreePresentation

variable {I : Type u} [SmallCategory I]
  (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X) (R : Type (u + 1)) [Ring R]


private instance coefficientColimits (S : Scheme.{u}) :
    HasColimitsOfSize.{u + 1, u + 1} (Coefficient R S) where
  has_colimits_of_shape J _ := by
    let : HasColimitsOfShape J AddCommGrpCat.{u + 1} := AddCommGrpCat.hasColimitsOfShape
    let : HasColimitsOfShape J (ModuleCat.{u + 1} R) := ModuleCat.hasColimitsOfShape R J
    exact CategoryTheory.Sheaf.instHasColimitsOfShape (J := S.smallEtaleTopology) (K := J)

private instance inverseImage_leftAdjoint {S T : Scheme.{u}} (f : S ⟶ T) :
    (inverseImage R f).IsLeftAdjoint := (imageAdjunction R f).isLeftAdjoint

/-- Actual model isomorphisms compose with original coefficient isomorphisms. -/
instance hasStageModel_closedIso :
    (HasStageModel X c R).IsClosedUnderIsomorphisms := by
  unfold HasStageModel
  infer_instance

variable [IsFiltered I]
  [∀ {i j} (q : i ⟶ j), IsAffineHom (X.map q).unop] (hc : IsColimit c)

include hc in
/-- The actual finite colimit of modeled bounded stages has an actual
canonical stage model, above every specified original base stage. -/
theorem hasStageModel_of_finiteColimit {J : Type (u + 1)} [SmallCategory J]
    [FinCategory J] {A : Coefficient R c.pt.unop}
    (p : (HasStageModel X c R).ColimitOfShape J A) : HasStageModel X c R A := by
  have hJ : HasCardinalLT (Arrow J) Cardinal.aleph0.{u + 1} := by
    rw [hasCardinalLT_aleph0_iff]
    infer_instance
  let (i : I) :
      (finiteColimitStages R (X.obj i).unop).IsClosedUnderColimitsOfShape J :=
    ObjectProperty.isClosedUnderColimitsOfShape_colimitsCardinalClosure
      (generators R (X.obj i).unop) Cardinal.aleph0.{u + 1} J hJ
  exact (@FiniteDiagramDescent.hasStageModel_of_finiteColimit
    I inferInstance
    (fun i : I => Coefficient R (X.obj i).unop)
    (fun i => inferInstanceAs
      (Category.{u + 1} (Coefficient R (X.obj i).unop)))
    (Coefficient R c.pt.unop)
    (inferInstanceAs (Category.{u + 1} (Coefficient R c.pt.unop))))
    (fun {_ _} q => inverseImage R (X.map q).unop)
    (fun i : I => inverseImage R (c.ι.app i).unop)
    (fun {_ _} q => coneCompIso X c _ R q)
    (fun i => finiteColimitStages R (X.obj i).unop)
    (fun {_ _} q A hA => finiteColimitStage_inverseImage R (X.map q).unop A hA)
    (fun i A hA B γ => exists_nativeHom_above X c i R hc A hA B γ)
    (fun i A hA B f g h => nativeHom_eventually_equal_above X c i R hc A hA B f g h)
    p

include hc in
/-- Native canonical stages descend once their actual affine-etale free
generators have been modeled. The output retains native stage membership,
the actual original base transition, and its original inverse-image iso. -/
theorem finiteColimitStage_hasStageModel
    (hgen : ∀ U : c.pt.unop.AffineEtale,
      HasStageModel X c R (free R c.pt.unop
        ((Scheme.AffineEtale.Spec c.pt.unop).obj U)))
    (A : Coefficient R c.pt.unop)
    (hA : finiteColimitStages R c.pt.unop A) :
    HasStageModel X c R A := by
  apply (@FiniteDiagramDescent.finiteColimitClosure_le_hasStageModel
    I inferInstance
    (fun i : I => Coefficient R (X.obj i).unop)
    (fun i => inferInstanceAs
      (Category.{u + 1} (Coefficient R (X.obj i).unop)))
    (Coefficient R c.pt.unop)
    (inferInstanceAs (Category.{u + 1} (Coefficient R c.pt.unop))))
    (fun {_ _} q => inverseImage R (X.map q).unop)
    (fun i : I => inverseImage R (c.ι.app i).unop)
    (fun {_ _} q => coneCompIso X c _ R q)
    (fun i => finiteColimitStages R (X.obj i).unop)
    (fun {_ _} q A hA => finiteColimitStage_inverseImage R (X.map q).unop A hA)
    (fun i A hA B γ => exists_nativeHom_above X c i R hc A hA B γ)
    (fun i A hA B f g h => nativeHom_eventually_equal_above X c i R hc A hA B f g h)
    (fun J _ _ i =>
      ObjectProperty.isClosedUnderColimitsOfShape_colimitsCardinalClosure
        (generators R (X.obj i).unop) Cardinal.aleph0.{u + 1} J (by
          rw [hasCardinalLT_aleph0_iff]
          infer_instance))
    (generators R c.pt.unop) (by
      rintro _ ⟨U⟩
      exact hgen U) A hA

end ModelDescent
end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule
