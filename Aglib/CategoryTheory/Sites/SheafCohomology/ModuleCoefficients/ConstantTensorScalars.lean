/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.ConstantTensor
public import Aglib.Algebra.Category.ModuleCat.FunctorTensorScalars

/-!
# Original scalar-linear constant-cohomology tensor equivalence

The exact-order tensor `H(R) ⊗[R] M` carries the commuting coefficient-ring
action on its right factor. The unchanged canonical comparison is an equivalence
for this action and the actual original cohomology action. No alternate
cohomology carrier or transported target action is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace ModuleCat.Sheaf

universe u v e l

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type) [Field R]
  [HasSheafify J AddCommGrpCat.{max u v}]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{max u v})]

/-- The original coefficient-ring-linear tensor equivalence, with the original
constant cohomology as target and the actual right-factor tensor action. -/
def constantTensorEquivOver (q : ℕ) (M : ModuleCat.{max u v} R)
    [PreservesColimitsOfShape (Discrete (Module.Free.ChooseBasisIndex R M))
      (constantCohomology J R q)]
    (Λ : Type l) [CommRing Λ] [Module Λ M] [SMulCommClass Λ R M] :
    letI := TensorProduct.rightModule R Λ
      ((constantCohomology J R q).obj (liftedUnit.{0, max u v} R)) M
    (constantCohomology J R q).obj (liftedUnit.{0, max u v} R) ⊗[R] M ≃ₗ[Λ]
      (constantCohomology J Λ q).obj (ModuleCat.of Λ M) := by
  letI := TensorProduct.rightModule R Λ
    ((constantCohomology J R q).obj (liftedUnit.{0, max u v} R)) M
  let : Module Λ ((constantCohomology J R q).obj M) :=
    inferInstanceAs (Module Λ ((constantCohomology J Λ q).obj (ModuleCat.of Λ M)))
  exact functorTensorEquivOverOfBasis (constantCohomology J R q) Λ
    (fun a x => by rfl) (Module.Free.chooseBasis R M)

/-- The scalar-linear equivalence retains the canonical comparison function. -/
@[simp]
theorem constantTensorEquivOver_apply (q : ℕ) (M : ModuleCat.{max u v} R)
    [PreservesColimitsOfShape (Discrete (Module.Free.ChooseBasisIndex R M))
      (constantCohomology J R q)]
    (Λ : Type l) [CommRing Λ] [Module Λ M] [SMulCommClass Λ R M]
    (z : (constantCohomology J R q).obj (liftedUnit.{0, max u v} R) ⊗[R] M) :
    constantTensorEquivOver J R q M Λ z = constantTensorComparison J R q M z := rfl

end ModuleCat.Sheaf
