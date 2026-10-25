/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.NoetherianModels.GeneratorModels
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.FiniteOpenCover

/-! # Original generator descent through two fixed affine charts

The two fixed affine model charts pull back to affine opens of an original
affine etale generator. Their affine overlap is modeled on the first chart.
The original bounded free-generator pushout then supplies its actual model
by the finite-diagram and finite-colimit construction. This applies at every
modulus and preserves the native original stage predicate.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
namespace NoetherianModels

universe u

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard
  Cardinal.fact_isRegular_aleph0

private theorem affineOpen_inf_of_isAffine
    {Y : Scheme.{u}} [IsAffine Y] (V W : Y.Opens)
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) : IsAffineOpen (V ⊓ W) := by
  let : IsAffine V.toScheme := hV
  let : IsAffine W.toScheme := hW
  let P : MorphismProperty Scheme.{u} := @IsAffineHom
  let : P.IsStableUnderBaseChange := isAffineHom_isStableUnderBaseChange
  have hsnd : IsAffineHom (pullback.snd V.ι W.ι) :=
    MorphismProperty.pullback_snd (P := P) _ _ (inferInstanceAs (IsAffineHom V.ι))
  have : IsAffine (pullback V.ι W.ι) :=
    @isAffine_of_isAffineHom _ W.toScheme _ hsnd inferInstance
  change IsAffine (V ⊓ W).toScheme
  exact IsAffine.of_isIso (AlgebraicGeometry.isPullback_opens_inf V W).isoPullback.hom

/-- The original free generator on an affine open lying in one specified
model chart has an actual canonical stage model. -/
theorem free_openChart_hasStageModel
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (q : i ⟶ j), IsAffineHom (D.map q)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    (V : (D.obj i).Opens) (hV : IsAffineOpen V)
    (U : c.pt.Etale) (W : U.left.Opens) (hW : IsAffineOpen W)
    (hWV : W ≤ (U.hom ≫ c.π.app i) ⁻¹ᵁ V) (n : ℕ) :
    HasStageModel D.op c.op n
      (BoundedPresentation.free c.pt n (FiniteOpenCover.openChart U W)) := by
  let : IsAffine V.toScheme := hV
  let : Etale U.hom := U.prop
  let A := FiniteOpenCover.openChart U W
  have : IsAffine A.left := hW
  let t := U.hom ≫ c.π.app i
  let f : A.left ⟶ pullback (c.π.app i) V.ι :=
    pullback.lift (W.ι ≫ U.hom) (t.resLE V W hWV)
      ((Category.assoc W.ι U.hom (c.π.app i)).trans
        (Scheme.Hom.resLE_comp_ι t hWV).symm)
  have hf : f ≫ pullback.fst (c.π.app i) V.ι = A.hom := pullback.lift_fst _ _ _
  have : Etale (f ≫ pullback.fst (c.π.app i) V.ι) := by
    rw [hf]
    exact A.prop
  let : Etale f := Etale.of_comp f (pullback.fst (c.π.app i) V.ι)
  exact free_hasStageModel_of_chart_factorization D c hc i V.ι A f hf n

/-- The actual original free generator is modeled from the original three
chart generators and their native bounded pushout. -/
theorem free_hasStageModel_of_twoCharts
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (q : i ⟶ j), IsAffineHom (D.map q)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    (V₀ V₁ : (D.obj i).Opens) (hV₀ : IsAffineOpen V₀) (hV₁ : IsAffineOpen V₁)
    (hcover : V₀ ⊔ V₁ = ⊤)
    (U : c.pt.Etale) [IsAffine U.left] [IsAffineHom U.hom] (n : ℕ) :
    HasStageModel D.op c.op n (BoundedPresentation.free c.pt n U) := by
  let : IsAffine ((𝟭 Scheme.{u}).obj U.left) := inferInstanceAs (IsAffine U.left)
  let : IsAffineHom (c.π.app i) := isAffineHom_π_app D c hc i
  let t := U.hom ≫ c.π.app i
  have : IsAffineHom t := inferInstance
  let W₀ := t ⁻¹ᵁ V₀
  let W₁ := t ⁻¹ᵁ V₁
  have hW₀ : IsAffineOpen W₀ := hV₀.preimage t
  have hW₁ : IsAffineOpen W₁ := hV₁.preimage t
  have hW₀₁ : IsAffineOpen (W₀ ⊓ W₁) := affineOpen_inf_of_isAffine W₀ W₁ hW₀ hW₁
  have hWcover : W₀ ⊔ W₁ = ⊤ := by
    change t ⁻¹ᵁ V₀ ⊔ t ⁻¹ᵁ V₁ = ⊤
    rw [← Scheme.Hom.preimage_sup, hcover, Scheme.Hom.preimage_top]
  let Q := HasStageModel D.op c.op n
  have {k l : Iᵒᵖ} (q : k ⟶ l) : IsAffineHom (D.op.map q).unop :=
    inferInstanceAs (IsAffineHom (D.map q.unop))
  let : Q.IsClosedUnderFiniteColimits :=
    hasStageModel_closedFiniteColimits D.op c.op hc.op n
  have hQ₀ : Q (BoundedPresentation.free c.pt n (FiniteOpenCover.openChart U W₀)) :=
    free_openChart_hasStageModel D c hc i V₀ hV₀ U W₀ hW₀ le_rfl n
  have hQ₁ : Q (BoundedPresentation.free c.pt n (FiniteOpenCover.openChart U W₁)) :=
    free_openChart_hasStageModel D c hc i V₁ hV₁ U W₁ hW₁ le_rfl n
  have hQ₀₁ : Q (BoundedPresentation.free c.pt n
      (FiniteOpenCover.openChart U (W₀ ⊓ W₁))) :=
    free_openChart_hasStageModel D c hc i V₀ hV₀ U (W₀ ⊓ W₁) hW₀₁ inf_le_left n
  have hp := FiniteOpenCover.coefficientSquare_isPushout c.pt n
    (FiniteOpenCover.openSquare U W₀ W₁)
    (FiniteOpenCover.openSquare_isPullback U W₀ W₁)
    (FiniteOpenCover.openSquare_cover U W₀ W₁ hWcover)
  exact Q.prop_of_isColimit hp.isColimit (by
    intro a
    cases a with
    | none => exact hQ₀₁
    | some a => cases a <;> assumption)

/-- Two actual affine opens at one original stage supply model descent for
every canonical bounded stage on a separated limit scheme. -/
theorem finiteColimitStage_hasStageModel_of_twoCharts
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (q : i ⟶ j), IsAffineHom (D.map q)]
    (c : Cone D) (hc : IsLimit c) [c.pt.IsSeparated] (i : I)
    (V₀ V₁ : (D.obj i).Opens) (hV₀ : IsAffineOpen V₀) (hV₁ : IsAffineOpen V₁)
    (hcover : V₀ ⊔ V₁ = ⊤) (n : ℕ)
    (A : BoundedPresentation.Coefficient c.pt n)
    (hA : BoundedPresentation.finiteColimitStages c.pt n A) :
    HasStageModel D.op c.op n A := by
  have {k l : Iᵒᵖ} (q : k ⟶ l) : IsAffineHom (D.op.map q).unop :=
    inferInstanceAs (IsAffineHom (D.map q.unop))
  apply finiteColimitStage_hasStageModel D.op c.op n hc.op ?_ A hA
  intro U
  let W := (Scheme.AffineEtale.Spec c.pt).obj U
  have : IsAffine W.left := inferInstanceAs (IsAffine (Spec U.left.unop))
  have ht : W.hom ≫ terminal.from c.pt = terminal.from W.left := terminal.comp_from _
  have hterminal : IsAffineHom (terminal.from W.left) := inferInstance
  have hcomp : IsAffineHom (W.hom ≫ terminal.from c.pt) := ht.symm ▸ hterminal
  have hsep : IsSeparated (terminal.from c.pt) :=
    (inferInstance : c.pt.IsSeparated).isSeparated_terminal_from
  let : IsAffineHom W.hom := @IsAffineHom.of_comp W.left c.pt (⊤_ Scheme.{u})
    W.hom (terminal.from c.pt) hcomp hsep
  exact free_hasStageModel_of_twoCharts D c hc i V₀ V₁ hV₀ hV₁ hcover W n

end NoetherianModels
end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
