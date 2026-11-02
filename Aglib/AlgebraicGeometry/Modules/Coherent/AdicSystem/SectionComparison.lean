/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.SectionCone
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Evaluation
public import Aglib.CategoryTheory.Limits.NatTransCoproduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Comparison with the limit of the original section diagram

The comparison is the native limit lift of the original quotient-unit cone.
Finite free coefficients inherit its invertibility from the actual unit cone;
no completeness or unit-cone existence is asserted here.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

variable (X : Scheme.{u}) (K : X.IdealSheafData)

private theorem sectionEvaluationAdditive : (SheafOfModules.evaluation X.ringCatSheaf (op ⊤) :
    X.Modules ⥤ ModuleCat.{u} Γ(X, ⊤)).Additive where
  map_add := by intros; rfl


/-- The original section diagrams, functorially in the original coefficient. -/
def idealSheafSectionDiagramFunctor : X.Modules ⥤ (ℕᵒᵖ ⥤ ModuleCat.{u} Γ(X, ⊤)) where
  obj := idealSheafSectionDiagram X K
  map := idealSheafSectionDiagramHom X K
  map_id M := by
    apply NatTrans.ext
    funext n
    exact ((idealSheafQuotientFunctor X (K ^ n.unop)) ⋙
      SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map_id M
  map_comp f g := by
    apply NatTrans.ext
    funext n
    exact ((idealSheafQuotientFunctor X (K ^ n.unop)) ⋙
      SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map_comp f g

instance idealSheafSectionDiagramFunctor_additive :
    (idealSheafSectionDiagramFunctor X K).Additive where
  map_add {M N f g} := by
    apply NatTrans.ext
    funext n
    let Q : X.Modules ⥤ X.Modules := idealSheafQuotientFunctor X (K ^ n.unop)
    let E : X.Modules ⥤ ModuleCat.{u} Γ(X, ⊤) :=
      SheafOfModules.evaluation X.ringCatSheaf (op ⊤)
    let : E.Additive := sectionEvaluationAdditive X
    change E.map (Q.map (f + g)) = E.map (Q.map f) + E.map (Q.map g)
    rw [Q.map_add, E.map_add]

/-- The native limit of the original section diagram, functorially in coefficients. -/
def idealSheafSectionLimitFunctor : X.Modules ⥤ ModuleCat.{u} Γ(X, ⊤) :=
  idealSheafSectionDiagramFunctor X K ⋙ lim

instance idealSheafSectionLimitFunctor_additive :
    (idealSheafSectionLimitFunctor X K).Additive where
  map_add {M N f g} := by
    apply limit.hom_ext
    intro n
    change lim.map ((idealSheafSectionDiagramFunctor X K).map (f + g)) ≫ _ =
      (lim.map ((idealSheafSectionDiagramFunctor X K).map f) +
        lim.map ((idealSheafSectionDiagramFunctor X K).map g)) ≫ _
    simp only [Functor.map_add, limit.map_π, Preadditive.add_comp,
      Preadditive.comp_add, NatTrans.app_add]

/-- The canonical comparison from original global sections to their quotient-diagram limit. -/
def idealSheafSectionComparison :
    SheafOfModules.evaluation X.ringCatSheaf (op ⊤) ⟶
      idealSheafSectionLimitFunctor X K where
  app M := limit.lift _ (idealSheafSectionCone X K M)
  naturality {M N} f := by
    apply limit.hom_ext
    intro n
    change (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map f ≫
        limit.lift _ (idealSheafSectionCone X K N) ≫
          limit.π (idealSheafSectionDiagram X K N) n =
      (limit.lift _ (idealSheafSectionCone X K M) ≫
        lim.map (idealSheafSectionDiagramHom X K f)) ≫
          limit.π (idealSheafSectionDiagram X K N) n
    simp only [Category.assoc, limit.map_π, limit.lift_π_assoc, limit.lift_π]
    exact congrArg (fun t => t.app n) (idealSheafSectionCone_naturality X K f)

/-- Every comparison projection is the original quotient unit on sections. -/
@[reassoc (attr := simp)]
theorem idealSheafSectionComparison_π (M : X.Modules) (n : ℕᵒᵖ) :
    (idealSheafSectionComparison X K).app M ≫
        limit.π (idealSheafSectionDiagram X K M) n =
      (idealSheafSectionCone X K M).π.app n :=
  limit.lift_π _ _

/-- The original cone is limiting precisely when its native comparison is invertible. -/
theorem idealSheafSectionCone_isLimit_iff (M : X.Modules) :
    Nonempty (IsLimit (idealSheafSectionCone X K M)) ↔
      IsIso ((idealSheafSectionComparison X K).app M) :=
  (limit.isLimit (idealSheafSectionDiagram X K M)).nonempty_isLimit_iff_isIso_lift

attribute [local instance] Abelian.hasFiniteBiproducts

/-- A limiting original unit cone implies the same for every original finite free sheaf. -/
theorem idealSheafSectionCone_finiteFree_isLimit (I : Type u) [Finite I]
    (h : IsLimit (idealSheafSectionCone X K (SheafOfModules.unit X.ringCatSheaf))) :
    Nonempty (IsLimit (idealSheafSectionCone X K
      (SheafOfModules.free (R := X.ringCatSheaf) I))) := by
  have : IsIso ((idealSheafSectionComparison X K).app
      (SheafOfModules.unit X.ringCatSheaf)) :=
    (idealSheafSectionCone_isLimit_iff X K _).mp ⟨h⟩
  apply (idealSheafSectionCone_isLimit_iff X K _).mpr
  let F : X.Modules ⥤ ModuleCat.{u} Γ(X, ⊤) :=
    SheafOfModules.evaluation X.ringCatSheaf (op ⊤)
  let G : X.Modules ⥤ ModuleCat.{u} Γ(X, ⊤) := idealSheafSectionLimitFunctor X K
  let : F.Additive := sectionEvaluationAdditive X
  let : G.Additive := idealSheafSectionLimitFunctor_additive X K
  let : PreservesColimitsOfShape (Discrete I) F := inferInstance
  let : PreservesColimitsOfShape (Discrete I) G := inferInstance
  exact NatTrans.isIso_app_coproduct
    (SheafOfModules.evaluation X.ringCatSheaf (op ⊤))
    (idealSheafSectionLimitFunctor X K) (idealSheafSectionComparison X K)
    (fun _ : I => SheafOfModules.unit X.ringCatSheaf)

end AlgebraicGeometry.Scheme.Modules.Coherent
