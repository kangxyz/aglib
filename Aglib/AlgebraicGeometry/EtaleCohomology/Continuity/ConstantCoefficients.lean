/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.QcqsCoefficientContinuity
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.ConstantTensor
public import Aglib.CategoryTheory.Limits.CoproductsFromFiltered

/-!
# Constant coefficients on a qcqs small étale site

Actual filtered coefficient continuity, followed by finite-sum additivity,
proves preservation of arbitrary coefficient coproducts. The canonical tensor
comparison therefore computes original cohomology with arbitrary vector-space
coefficients. The independent Ext universe is retained; only the required
filtered colimits in its value category are requested.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u e

attribute [local instance] hasSheafifyLarge

variable (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]

/-- The original fixed-site cohomology functor preserves actual filtered
coefficient colimits on a qcqs scheme. -/
theorem qcqsCohomology_preservesFilteredColimits
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I AddCommGrpCat.{e}] (q : ℕ) :
    PreservesColimitsOfShape I (Sheaf.functorH X.smallEtaleTopology q :
      AbelianSheaf.{u, u + 1} X ⥤ AddCommGrpCat.{e}) where
  preservesColimit {G} := by
    let : IsIso (colimit.post G (Sheaf.functorH X.smallEtaleTopology q)) :=
      isIso_qcqsCoefficientColimitComparison G q
    exact preservesColimit_of_isIso_post (Sheaf.functorH X.smallEtaleTopology q) G

/-- Original scalar-enriched constant cohomology preserves coefficient
coproducts, by its native finite-subcoproduct filtered diagram. -/
theorem qcqsConstantCohomology_preservesCoproducts
    (R : Type) [Field R] (ι : Type (u + 1))
    [HasColimitsOfShape (Finset (Discrete ι)) AddCommGrpCat.{e}] (q : ℕ) :
    PreservesColimitsOfShape (Discrete ι)
      (ModuleCat.Sheaf.constantCohomology X.smallEtaleTopology R q) := by
  classical
  let : PreservesColimitsOfShape (Finset (Discrete ι))
      (Sheaf.functorH X.smallEtaleTopology q :
        AbelianSheaf.{u, u + 1} X ⥤ AddCommGrpCat.{e}) :=
    qcqsCohomology_preservesFilteredColimits X (Finset (Discrete ι)) q
  let : PreservesColimitsOfShape (Finset (Discrete ι))
      (ModuleCat.Sheaf.constantCohomology X.smallEtaleTopology R q) :=
    ModuleCat.Sheaf.constantCohomology_preservesColimitsOfShape
      X.smallEtaleTopology R (Finset (Discrete ι)) q
  let (f : ι → ModuleCat.{u + 1} R) : PreservesColimit (Discrete.functor f)
      (ModuleCat.Sheaf.constantCohomology X.smallEtaleTopology R q) :=
    preservesCoproduct_of_finiteSubcoproducts
      (ModuleCat.Sheaf.constantCohomology X.smallEtaleTopology R q) f
  exact preservesColimitsOfShape_of_discrete _

/-- The canonical original cohomology tensor comparison is an equivalence for
arbitrary constant vector-space coefficients on a qcqs scheme. -/
def qcqsConstantTensorEquiv (R : Type) [Field R] (q : ℕ) (M : ModuleCat.{u + 1} R)
    [HasColimitsOfShape (Finset (Discrete (Module.Free.ChooseBasisIndex R M)))
      AddCommGrpCat.{e}] :
    (ModuleCat.Sheaf.constantCohomology X.smallEtaleTopology R q).obj
        (ModuleCat.liftedUnit.{0, u + 1} R) ⊗[R] M ≃ₗ[R]
      (ModuleCat.Sheaf.constantCohomology X.smallEtaleTopology R q).obj M := by
  let := qcqsConstantCohomology_preservesCoproducts X R
    (Module.Free.ChooseBasisIndex R M) q
  exact ModuleCat.Sheaf.constantTensorEquiv X.smallEtaleTopology R q M

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
