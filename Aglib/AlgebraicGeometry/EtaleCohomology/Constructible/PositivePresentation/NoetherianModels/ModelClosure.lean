/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.NoetherianModels.FiniteDiagrams

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

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
namespace NoetherianModels

universe u v

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard
  Cardinal.fact_isRegular_aleph0

variable {I : Type u} [SmallCategory I]
  (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X) (n : ℕ)

/-- Actual model isomorphisms compose with original coefficient isomorphisms. -/
instance hasStageModel_closedIso :
    (HasStageModel X c n).IsClosedUnderIsomorphisms := by
  unfold HasStageModel
  infer_instance

variable [IsFiltered I]
  [∀ {i j} (q : i ⟶ j), IsAffineHom (X.map q).unop] (hc : IsColimit c)

include hc in
/-- The actual finite colimit of modeled bounded stages has an actual
canonical stage model, above every specified original base stage. -/
theorem hasStageModel_of_finiteColimit {J : Type (u + 1)} [SmallCategory J]
    [FinCategory J] {A : BoundedPresentation.Coefficient c.pt.unop n}
    (p : (HasStageModel X c n).ColimitOfShape J A) : HasStageModel X c n A := by
  have hJ : HasCardinalLT (Arrow J) Cardinal.aleph0.{u + 1} := by
    rw [hasCardinalLT_aleph0_iff]
    infer_instance
  let (i : I) :
      (BoundedPresentation.finiteColimitStages (X.obj i).unop n).IsClosedUnderColimitsOfShape J :=
    ObjectProperty.isClosedUnderColimitsOfShape_colimitsCardinalClosure
      (BoundedPresentation.generators (X.obj i).unop n) Cardinal.aleph0.{u + 1} J hJ
  exact (@FiniteDiagramDescent.hasStageModel_of_finiteColimit
    I inferInstance
    (fun i : I => BoundedPresentation.Coefficient (X.obj i).unop n)
    (fun i => inferInstanceAs
      (Category.{u + 1} (BoundedPresentation.Coefficient (X.obj i).unop n)))
    (BoundedPresentation.Coefficient c.pt.unop n)
    (inferInstanceAs (Category.{u + 1} (BoundedPresentation.Coefficient c.pt.unop n))))
    (fun {_ _} q => boundedInverseImage (X.map q).unop n)
    (fun i : I => boundedInverseImage (c.ι.app i).unop n)
    (fun {_ _} q => boundedConeCompIso X c n q)
    (fun i => BoundedPresentation.finiteColimitStages (X.obj i).unop n)
    (fun {_ _} q A hA => finiteColimitStage_inverseImage (X.map q).unop n A hA)
    (fun i A hA B γ => exists_boundedHom_above X c i hc n A hA B γ)
    (fun i A hA B f g h => boundedHom_eventually_equal_above X c i hc n A hA B f g h)
    p

include hc in
/-- Native canonical stages descend once their actual affine-etale free
generators have been modeled. The output retains native stage membership,
the actual original base transition, and its original inverse-image iso. -/
theorem finiteColimitStage_hasStageModel
    (hgen : ∀ U : c.pt.unop.AffineEtale,
      HasStageModel X c n (BoundedPresentation.free c.pt.unop n
        ((Scheme.AffineEtale.Spec c.pt.unop).obj U)))
    (A : BoundedPresentation.Coefficient c.pt.unop n)
    (hA : BoundedPresentation.finiteColimitStages c.pt.unop n A) :
    HasStageModel X c n A := by
  apply (@FiniteDiagramDescent.finiteColimitClosure_le_hasStageModel
    I inferInstance
    (fun i : I => BoundedPresentation.Coefficient (X.obj i).unop n)
    (fun i => inferInstanceAs
      (Category.{u + 1} (BoundedPresentation.Coefficient (X.obj i).unop n)))
    (BoundedPresentation.Coefficient c.pt.unop n)
    (inferInstanceAs (Category.{u + 1} (BoundedPresentation.Coefficient c.pt.unop n))))
    (fun {_ _} q => boundedInverseImage (X.map q).unop n)
    (fun i : I => boundedInverseImage (c.ι.app i).unop n)
    (fun {_ _} q => boundedConeCompIso X c n q)
    (fun i => BoundedPresentation.finiteColimitStages (X.obj i).unop n)
    (fun {_ _} q A hA => finiteColimitStage_inverseImage (X.map q).unop n A hA)
    (fun i A hA B γ => exists_boundedHom_above X c i hc n A hA B γ)
    (fun i A hA B f g h => boundedHom_eventually_equal_above X c i hc n A hA B f g h)
    (fun J _ _ i =>
      ObjectProperty.isClosedUnderColimitsOfShape_colimitsCardinalClosure
        (BoundedPresentation.generators (X.obj i).unop n) Cardinal.aleph0.{u + 1} J (by
          rw [hasCardinalLT_aleph0_iff]
          infer_instance))
    (BoundedPresentation.generators c.pt.unop n) (by
      rintro _ ⟨U⟩
      exact hgen U) A hA

end NoetherianModels
end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
