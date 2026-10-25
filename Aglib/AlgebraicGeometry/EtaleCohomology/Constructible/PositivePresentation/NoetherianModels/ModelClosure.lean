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
    (HasStageModel X c n).IsClosedUnderIsomorphisms where
  of_iso e hA i₀ := by
    obtain ⟨i, q, M, hM, ⟨eM⟩⟩ := hA i₀
    exact ⟨i, q, M, hM, ⟨eM ≪≫ e⟩⟩

variable [IsFiltered I]
  [∀ {i j} (q : i ⟶ j), IsAffineHom (X.map q).unop] (hc : IsColimit c)

include hc in
/-- The actual finite colimit of modeled bounded stages has an actual
canonical stage model, above every specified original base stage. -/
theorem hasStageModel_of_finiteColimit {J : Type (u + 1)} [SmallCategory J]
    [FinCategory J] {A : BoundedPresentation.Coefficient c.pt.unop n}
    (p : (HasStageModel X c n).ColimitOfShape J A) : HasStageModel X c n A := by
  classical
  intro i₀
  obtain ⟨i, q, Lᵢ, hLᵢ, ⟨e⟩⟩ :=
    exists_finiteDiagram_model X c n hc i₀ p.diag p.prop_diag_obj
  have hJ : HasCardinalLT (Arrow J) Cardinal.aleph0.{u + 1} := by
    rw [hasCardinalLT_aleph0_iff]
    infer_instance
  let P := BoundedPresentation.finiteColimitStages (X.obj i).unop n
  let : P.IsClosedUnderColimitsOfShape J :=
    ObjectProperty.isClosedUnderColimitsOfShape_colimitsCardinalClosure
      (BoundedPresentation.generators (X.obj i).unop n) Cardinal.aleph0.{u + 1} J hJ
  have hM : P (colimit Lᵢ) := P.prop_colimit Lᵢ hLᵢ
  let E := boundedInverseImage (c.ι.app i).unop n
  have := p.hasColimit
  let eM : E.obj (colimit Lᵢ) ≅ A :=
    preservesColimitIso E Lᵢ ≪≫ HasColimit.isoOfNatIso e ≪≫
      colimit.isoColimitCocone ⟨_, p.isColimit⟩
  exact ⟨i, q, colimit Lᵢ, hM, ⟨eM⟩⟩

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
  have hclosed : BoundedPresentation.finiteColimitStages c.pt.unop n ≤
      HasStageModel X c n := by
    change (BoundedPresentation.generators c.pt.unop n).colimitsCardinalClosure
      Cardinal.aleph0.{u + 1} ≤ HasStageModel X c n
    refine ObjectProperty.colimitsCardinalClosure_le
      (BoundedPresentation.generators c.pt.unop n) Cardinal.aleph0.{u + 1}
      (Q := HasStageModel X c n) ?_ ?_
    · intro J _ hJ
      have : Finite (Arrow J) := (hasCardinalLT_aleph0_iff _).mp hJ
      let : FinCategory J := ((Arrow.finite_iff J).mp inferInstance).some
      exact ⟨fun _ ⟨p⟩ => hasStageModel_of_finiteColimit X c n hc p⟩
    · rintro _ ⟨U⟩
      exact hgen U
  exact hclosed A hA

end NoetherianModels
end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
