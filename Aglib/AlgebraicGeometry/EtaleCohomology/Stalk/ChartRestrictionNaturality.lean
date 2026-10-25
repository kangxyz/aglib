/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartHomSections

/-! # Original chart-variable restriction in every cohomological degree -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u w₀ w₁ w₂ s₁ s₂

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} {U V : X.Etale} (g : V ⟶ U)

/-- The actual constant-source square for the original inverse-image chart pullback. -/
theorem chartComparisonSource_restriction :
    ((((inverseImageConstantIso g.left).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv ≫
      (inverseImage g.left).map (chartComparisonSource U)) ≫
        (pullbackTriangleIso V.hom U.hom g.left
          (MorphismProperty.Over.w g)).inv.app
          (Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
            (Scheme.smallEtaleTopology X) U)) =
    chartComparisonSource V ≫ (inverseImage V.hom).map
      ((Sheaf.Hypercohomology.freeAbelianSheafFunctor.{u + 1}
        (Scheme.smallEtaleTopology X)).map g) := by
  apply (chartHomSectionsEquiv V
    (Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
      (Scheme.smallEtaleTopology X) U)).injective
  rw [chartHomSectionsEquiv_restriction, chartHomSectionsEquiv_naturality,
    chartHomSectionsEquiv_source, chartHomSectionsEquiv_source]
  change (Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
    (Scheme.smallEtaleTopology X) U).obj.map g.op
      (Sheaf.Hypercohomology.sectionsEquiv (Scheme.smallEtaleTopology X) U _ (𝟙 _)) =
    ((Sheaf.Hypercohomology.freeAbelianSheafFunctor.{u + 1}
      (Scheme.smallEtaleTopology X)).map g).hom.app (op V)
      (Sheaf.Hypercohomology.sectionsEquiv (Scheme.smallEtaleTopology X) V _ (𝟙 _))
  rw [← Sheaf.Hypercohomology.sectionsEquiv_naturality, Category.id_comp]
  exact (Sheaf.SliceCohomology.freeSections_naturality (Scheme.smallEtaleTopology X) g
    (Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
      (Scheme.smallEtaleTopology X) U) (𝟙 _)).symm

variable [hBaseExt : HasExt.{w₀} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{s₁} (Sheaf ((Scheme.smallEtaleTopology X).over U) AddCommGrpCat.{u + 1})]
  [HasExt.{s₂} (Sheaf ((Scheme.smallEtaleTopology X).over V) AddCommGrpCat.{u + 1})]
  [hUExt : HasExt.{w₁} (AbelianSheaf.{u, u + 1} U.left)]
  [hVExt : HasExt.{w₂} (AbelianSheaf.{u, u + 1} V.left)]

local instance chartRestrictionNaturality_uBaseExt : HasExt.{w₀}
    (AbelianSheaf.{u, u + 1} ((Functor.fromPUnit X).obj U.right)) := hBaseExt

local instance chartRestrictionNaturality_vBaseExt : HasExt.{w₀}
    (AbelianSheaf.{u, u + 1} ((Functor.fromPUnit X).obj V.right)) := hBaseExt

local instance chartRestrictionNaturality_uChartExt : HasExt.{w₁}
    (Sheaf ((𝟭 Scheme.{u}).obj U.left).smallEtaleTopology AddCommGrpCat.{u + 1}) := hUExt

local instance chartRestrictionNaturality_vChartExt : HasExt.{w₂}
    (Sheaf ((𝟭 Scheme.{u}).obj V.left).smallEtaleTopology AddCommGrpCat.{u + 1}) := hVExt

/-- Chart-variable comparison uses the original scheme cohomology pullback and
its actual commuting-triangle coefficient transport in every degree. -/
theorem originalCohomologyChartEquiv_restriction
    (F : AbelianSheaf.{u, u + 1} X) (n : ℕ)
    (x : Sheaf.LargeCohomology.H.{w₀, u + 1, u, u + 1}
      (Scheme.smallEtaleTopology X) F n U) :
    originalCohomologyChartEquiv V F n
      ((Sheaf.LargeCohomology.presheaf.{w₀, u + 1, u, u + 1}
        (Scheme.smallEtaleTopology X) F n).map g.op x) =
      Sheaf.H.map
        ((pullbackTriangleIso V.hom U.hom g.left
          (MorphismProperty.Over.w g)).inv.app F) n
        (cohomologyPullback g.left ((inverseImage U.hom).obj F) n
          (originalCohomologyChartEquiv U F n x)) := by
  rw [originalCohomologyChartEquiv_apply, originalCohomologyChartEquiv_apply,
    cohomologyPullback_apply, Sheaf.H.map_apply]
  exact (Sheaf.SliceCohomology.extRestrictionCompatibility
    (inverseImage U.hom) (inverseImage V.hom) (inverseImage g.left)
    (pullbackTriangleIso V.hom U.hom g.left (MorphismProperty.Over.w g)).inv
    (((inverseImageConstantIso g.left).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv)
    (chartComparisonSource U) (chartComparisonSource V)
    ((Sheaf.Hypercohomology.freeAbelianSheafFunctor.{u + 1}
      (Scheme.smallEtaleTopology X)).map g)
    (by simpa only [Category.assoc] using chartComparisonSource_restriction g) x).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
