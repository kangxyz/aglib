/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.ConstantScalars
public import Aglib.Algebra.Category.ModuleCat.FunctorTensorFiniteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Canonical tensor and finite-module transport for original constant cohomology

These are consumers of the canonical original-cohomology scalar functor.
Filtered continuity is a functor-preservation input at this arbitrary-site
layer; the small-etale qcqs consumer discharges it geometrically. No finite
underlying coefficient group is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped TensorProduct

namespace ModuleCat.Sheaf

universe u v e i j l

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type) [Field R]
  [HasSheafify J AddCommGrpCat.{max u v}]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{max u v})]

/-- Preservation for original additive cohomology lifts to the original scalar-enriched
constant-coefficient functor, without any change of its target universe. -/
theorem constantCohomology_preservesColimitsOfShape
    (I : Type i) [Category.{j} I]
    [HasColimitsOfShape I AddCommGrpCat.{max u v}]
    [HasColimitsOfShape I AddCommGrpCat.{e}] (q : ℕ)
    [PreservesColimitsOfShape I (CategoryTheory.Sheaf.functorH J q :
      Sheaf J AddCommGrpCat.{max u v} ⥤ AddCommGrpCat.{e})] :
    PreservesColimitsOfShape I (constantCohomology J R q) := by
  let F := constantCohomology J R q
  let U := forget₂ (ModuleCat.{e} R) AddCommGrpCat.{e}
  let : PreservesColimitsOfShape I (constantSheaf J AddCommGrpCat.{max u v}) := by
    unfold constantSheaf
    infer_instance
  let : PreservesColimitsOfShape I (constantCohomologyAb J R q) := by
    infer_instance
  let : PreservesColimitsOfShape I (F ⋙ U) :=
    preservesColimitsOfShape_of_natIso
      (Functor.moduleValuedForgetIso R (constantCohomologyAb J R q)).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves F U

/-- The original cohomology tensor map is induced by the actual maps `r ↦ r • m`. -/
abbrev constantTensorComparison (q : ℕ) (M : ModuleCat.{max u v} R) :
    (constantCohomology J R q).obj (liftedUnit.{0, max u v} R) ⊗[R] M →ₗ[R]
      (constantCohomology J R q).obj M :=
  functorTensorComparison (constantCohomology J R q) M


/-- The canonical tensor comparison for original constant cohomology, once its
actual basis-indexed coproduct is preserved. -/
def constantTensorEquiv (q : ℕ) (M : ModuleCat.{max u v} R)
    [PreservesColimitsOfShape (Discrete (Module.Free.ChooseBasisIndex R M))
      (constantCohomology J R q)] :
    (constantCohomology J R q).obj (liftedUnit.{0, max u v} R) ⊗[R] M ≃ₗ[R]
      (constantCohomology J R q).obj M :=
  functorTensorEquivOfBasis (constantCohomology J R q) (Module.Free.chooseBasis R M)

/-- Finiteness over the original coefficient ring follows from finite-dimensional
rank-one cohomology, not from finiteness of the coefficient set or its base-field rank. -/
theorem finite_constantCohomology (q : ℕ) (M : ModuleCat.{max u v} R)
    [PreservesColimitsOfShape (Discrete (Module.Free.ChooseBasisIndex R M))
      (constantCohomology J R q)]
    [Module.Finite R ((constantCohomology J R q).obj (liftedUnit.{0, max u v} R))]
    (Λ : Type l) [CommRing Λ] [Module Λ M] [SMulCommClass Λ R M]
    [Module.Finite Λ M] :
    Module.Finite Λ ((constantCohomology J Λ q).obj (ModuleCat.of Λ M)) := by
  let : Module Λ ((constantCohomology J R q).obj M) :=
    inferInstanceAs (Module Λ ((constantCohomology J Λ q).obj (ModuleCat.of Λ M)))
  change Module.Finite Λ ((constantCohomology J R q).obj M)
  exact finite_functorObj_of_basis (constantCohomology J R q) Λ
    (fun a x => by rfl) (Module.Free.chooseBasis R M)
    (Module.Free.chooseBasis R
      ((constantCohomology J R q).obj (liftedUnit.{0, max u v} R)))

end ModuleCat.Sheaf
