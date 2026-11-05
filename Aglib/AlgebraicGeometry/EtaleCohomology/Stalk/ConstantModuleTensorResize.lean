/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ConstantModuleTensor
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductPresheaf
public import Aglib.Algebra.Category.ModuleCat.ResizeTensor

/-! # The original constant-module tensor comparison at the native value size

Only the original cohomology factors are resized. The tensor of the resized
rank-one cohomology and the original coefficient module already has the native
value size. Its comparison is the conjugate of the original comparison by the
native Shrink linear equivalences and the native tensor congruence. No smallness
of a large tensor or new cohomology realization is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u r w s e l

attribute [local instance] hasSheafifyLarge

section Presheaf

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{max (u + 1) e}
    (AbelianSheaf.{u, u + 1} (pullback U.hom f))]

/-- Smallness is inherited from the original fibre-product cohomology theorem. -/
local instance constantModuleCohomologyValue_small (A : Type l) [Ring A]
    (N : ModuleCat.{u + 1} A) (q : ℕ) (U : S.Etaleᵒᵖ) :
    Small.{u + 1} ((constantModuleCohomologyPresheaf f A N q).obj U) :=
  fibreProductCohomology_small f ((constantModuleUnderlying (X := X) A).obj N) q U.unop

local instance constantModuleFibreValue_small (A : Type l) [Ring A]
    (N : ModuleCat.{u + 1} A) (q : ℕ) (U : S.Etale) :
    Small.{u + 1} ((constantModuleFibreCohomology f A U q).obj N) :=
  fibreProductCohomology_small.{u, w, s, max (u + 1) e} f
    ((constantModuleUnderlying (X := X) A).obj N) q U

variable (R : Type) [Field R] (Λ : Type r) [Ring Λ]
  (M : ModuleCat.{u + 1} R) [Module Λ M] [SMulCommClass Λ R M]

/-- Resize the original rank-one diagram before tensoring with the unchanged module. -/
abbrev smallConstantModuleTensorPresheaf (q : ℕ) :
    S.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ :=
  ModuleCat.resizeDiagram.{u + 1} R
      (constantModuleCohomologyPresheaf f R (ModuleCat.liftedUnit.{0, u + 1} R) q) ⋙
    ModuleCat.tensorRightScalarsFunctor R Λ M

/-- The same original natural comparison at the native value universe. -/
def smallConstantModuleTensorPresheafComparison (q : ℕ) :
    smallConstantModuleTensorPresheaf f R Λ M q ⟶
      ModuleCat.resizeDiagram.{u + 1} Λ
        (constantModuleCohomologyPresheaf f Λ (ModuleCat.of Λ M) q) :=
  ModuleCat.resizeTensorComparison R Λ M
    (constantModuleCohomologyPresheaf f R (ModuleCat.liftedUnit.{0, u + 1} R) q)
    (constantModuleCohomologyPresheaf f Λ (ModuleCat.of Λ M) q)
    (constantModuleTensorPresheafComparison f R Λ M q)

/-- The original component of the complete native-size comparison. -/
def smallConstantModuleTensorComparison (U : S.Etale) (q : ℕ) :
    (smallConstantModuleTensorPresheaf f R Λ M q).obj (op U) ⟶
      (ModuleCat.resizeDiagram.{u + 1} Λ
        (constantModuleCohomologyPresheaf f Λ (ModuleCat.of Λ M) q)).obj (op U) :=
  (smallConstantModuleTensorPresheafComparison f R Λ M q).app (op U)

/-- Affine-test bijectivity uses the original comparison and the actual equivalences. -/
theorem smallConstantModuleTensorComparison_bijective_of_affine
    [IsProper f] (U : S.Etale) [IsAffine U.left] (q : ℕ) :
    Function.Bijective (smallConstantModuleTensorComparison f R Λ M U q) := by
  exact ModuleCat.resizeTensorComparison_bijective R Λ M
    (constantModuleCohomologyPresheaf f R (ModuleCat.liftedUnit.{0, u + 1} R) q)
    (constantModuleCohomologyPresheaf f Λ (ModuleCat.of Λ M) q)
    (constantModuleTensorPresheafComparison f R Λ M q) (op U)
    (constantModuleTensorComparison_bijective_of_affine f R Λ M U q)

end Presheaf
end AlgebraicGeometry.Scheme.EtaleCohomology
