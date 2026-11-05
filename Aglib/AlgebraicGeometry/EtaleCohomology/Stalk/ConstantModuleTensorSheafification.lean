/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ConstantModuleTensorResize
public import Aglib.AlgebraicGeometry.Sites.AffineSheafification
public import Aglib.Algebra.Category.ModuleCat.FunctorTensorRightScalarsAdjunction
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantLinear
public import Mathlib.CategoryTheory.Sites.Adjunction

/-! # Sheafification of the actual constant-module tensor comparison

The actual affine-test bijections suffice after sheafification. Forgetting
scalars and the existing affine criterion prove this; the original module
structures are retained. The source is the sheafified original rank-one
cohomology tensored by the actual coefficient left adjoint.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u r w s e l

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

/-- The original abelian affine criterion reflects through scalar forgetting. -/
private theorem module_isIso_sheafify_map_of_affine
    (S : Scheme.{u}) (Λ : Type r) [Ring Λ]
    {P Q : S.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ} (a : P ⟶ Q)
    (h : ∀ U : S.Etale, IsAffine U.left → Function.Bijective (a.app (op U))) :
    IsIso ((presheafToSheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map a) := by
  let : S.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    ModuleCat.Sheaf.forget_preservesSheafification Λ S.smallEtaleTopology
  let V := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  have ha := Scheme.Etale.isIso_sheafify_map_of_affine S (Functor.whiskerRight a V) h
  let E := sheafComposeNatIso S.smallEtaleTopology V
    (sheafificationAdjunction S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (sheafificationAdjunction S.smallEtaleTopology AddCommGrpCat.{u + 1})
  let : IsIso ((ModuleCat.Sheaf.underlying Λ S.smallEtaleTopology).map
      ((presheafToSheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map a)) :=
    (NatIso.isIso_map_iff E a).mp ha
  exact isIso_of_reflects_iso
    ((presheafToSheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map a)
    (ModuleCat.Sheaf.underlying Λ S.smallEtaleTopology)

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{max (u + 1) e}
    (AbelianSheaf.{u, u + 1} (pullback U.hom f))]

local instance constantTensorSheafificationSmall (A : Type l) [Ring A]
    (N : ModuleCat.{u + 1} A) (q : ℕ) :
    ∀ U, Small.{u + 1} ((constantModuleCohomologyPresheaf f A N q).obj U) :=
  fun U => fibreProductCohomology_small.{u, w, s, max (u + 1) e} f
    ((constantModuleUnderlying (X := X) A).obj N) q U.unop

variable (R : Type) [Field R] (Λ : Type r) [Ring Λ]
  (M : ModuleCat.{u + 1} R) [Module Λ M] [SMulCommClass Λ R M] [IsProper f]

local instance constantModuleTensorSheafification_isLeftAdjoint :
    (ModuleCat.tensorRightScalarsFunctor.{0, r, u + 1, u + 1} R Λ M).IsLeftAdjoint :=
  (ModuleCat.tensorRightScalarsAdjunction.{0, r, u + 1, u + 1} R Λ M).isLeftAdjoint

/-- The actual original tensor comparison becomes an isomorphism after sheafification. -/
instance smallConstantModuleTensorPresheafComparison_sheafify_isIso (q : ℕ) :
    IsIso ((presheafToSheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
      (smallConstantModuleTensorPresheafComparison f R Λ M q)) :=
  module_isIso_sheafify_map_of_affine S Λ _ (fun U hU => by
    let := hU
    exact smallConstantModuleTensorComparison_bijective_of_affine f R Λ M U q)

/-- Tensor the original rank-one cohomology sheaf, obtaining precisely the
sheafification of the original constant-M cohomology diagram. -/
def constantModuleTensorSheafificationIso (q : ℕ) :
    (Sheaf.composeAndSheafify S.smallEtaleTopology
      (ModuleCat.tensorRightScalarsFunctor.{0, r, u + 1, u + 1} R Λ M)).obj
        ((presheafToSheaf S.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
          (ModuleCat.resizeDiagram.{u + 1} R
            (constantModuleCohomologyPresheaf f R
              (ModuleCat.liftedUnit.{0, u + 1} R) q))) ≅
      (presheafToSheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.resizeDiagram.{u + 1} Λ
          (constantModuleCohomologyPresheaf f Λ (ModuleCat.of Λ M) q)) := by
  let P := ModuleCat.resizeDiagram.{u + 1} R
    (constantModuleCohomologyPresheaf.{u, 0, w, s, max (u + 1) e} f R
      (ModuleCat.liftedUnit.{0, u + 1} R) q)
  let Q := ModuleCat.resizeDiagram.{u + 1} Λ
    (constantModuleCohomologyPresheaf.{u, r, w, s, max (u + 1) e} f Λ (ModuleCat.of Λ M) q)
  let T := ModuleCat.tensorRightScalarsFunctor.{0, r, u + 1, u + 1} R Λ M
  let L := presheafToSheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let a : P ⋙ T ⟶ Q :=
    smallConstantModuleTensorPresheafComparison.{u, r, w, s, e} f R Λ M q
  let : IsIso (L.map a) :=
    smallConstantModuleTensorPresheafComparison_sheafify_isIso.{u, r, w, s, e}
      f R Λ M q
  exact (presheafToSheafCompComposeAndSheafifyIso S.smallEtaleTopology T).app P ≪≫
    asIso (L.map a)

end AlgebraicGeometry.Scheme.EtaleCohomology
