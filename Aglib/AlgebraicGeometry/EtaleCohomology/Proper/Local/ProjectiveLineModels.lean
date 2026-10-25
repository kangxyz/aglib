/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.NoetherianModels.ChartGenerators
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.NoetherianModels.ProjectiveLineSystem
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.NoetherianModels.ModelEmbedding
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.ProjectiveLineCriterion

/-! # Original local P1 comparison from actual Noetherian stage models

Every native canonical bounded stage on P1 over an arbitrary ring descends
through the original integer-subalgebra system. Its two-chart generators,
finite diagram and finite colimit are modeled as actual native objects.
Noetherian global finite embeddings and original exact inverse image then
produce the actual finite constant product embedding on the original P1.

Ambient finite presentation reduces the accepted all-stage predicate to
these canonical original stages by splitting the identity through the
original bounded presentation. This discharges the actual geometric premise
of the accepted local projective-line criterion, without a Noetherian
assumption on the henselian local ring or an order-invertibility premise.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
open AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation.NoetherianModels
open AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard HasExt.standard
  Cardinal.fact_isRegular_aleph0

variable (R : Type u) [CommRing R]

/-- A canonical original bounded coefficient on native P1 has an actual
canonical stage model on its original integer-subalgebra scheme system.
This model assertion holds also at moduli zero and one. -/
theorem projectiveLine_canonicalStage_hasModel (n : ℕ)
    (A : Constructible.BoundedPresentation.Coefficient (ProjectiveLine.projectiveP1 R) n)
    (hA : Constructible.BoundedPresentation.finiteColimitStages
      (ProjectiveLine.projectiveP1 R) n A) :
    HasStageModel (ProjectiveLineSystem.diagram R).op (ProjectiveLineSystem.cone R).op n
      ((boundedInverseImage (ProjectiveLineSystem.pointIso R).inv n).obj A) := by
  let M := (boundedInverseImage (ProjectiveLineSystem.pointIso R).inv n).obj A
  have hM : Constructible.BoundedPresentation.finiteColimitStages
      (ProjectiveLineSystem.cone R).pt n M :=
    finiteColimitStage_inverseImage (ProjectiveLineSystem.pointIso R).inv n A hA
  exact finiteColimitStage_hasStageModel_of_twoCharts
    (ProjectiveLineSystem.diagram R) (ProjectiveLineSystem.cone R)
    (ProjectiveLineSystem.coneIsLimit R) (ProjectiveLineSystem.initialStage R)
    (ProjectiveLineSystem.initialChartOpen R 0) (ProjectiveLineSystem.initialChartOpen R 1)
    (ProjectiveLineSystem.initialChart_affine R 0)
    (ProjectiveLineSystem.initialChart_affine R 1)
    (ProjectiveLineSystem.initialCharts_cover R) n M hM

/-- Every canonical original positive stage on native P1 over an arbitrary
ring has an actual finite constant product embedding on that same P1. -/
theorem projectiveLine_canonicalStage_embedding (n : ℕ) (hn : n ≠ 0)
    (A : Constructible.BoundedPresentation.Coefficient (ProjectiveLine.projectiveP1 R) n)
    (hA : Constructible.BoundedPresentation.finiteColimitStages
      (ProjectiveLine.projectiveP1 R) n A) : Nonempty (FiniteConstantProductEmbedding A.obj) := by
  let e := ProjectiveLineSystem.pointIso R
  let M := (boundedInverseImage e.inv n).obj A
  have hM : HasStageModel (ProjectiveLineSystem.diagram R).op
      (ProjectiveLineSystem.cone R).op n M := projectiveLine_canonicalStage_hasModel R n A hA
  have (i : ((Finset R)ᵒᵖ)ᵒᵖ) :
      IsNoetherian (((ProjectiveLineSystem.diagram R).op.obj i).unop) :=
    inferInstanceAs (IsNoetherian ((ProjectiveLineSystem.diagram R).obj i.unop))
  have (i : ((Finset R)ᵒᵖ)ᵒᵖ) :
      (((ProjectiveLineSystem.diagram R).op.obj i).unop).IsSeparated :=
    inferInstanceAs (((ProjectiveLineSystem.diagram R).obj i.unop).IsSeparated)
  obtain ⟨t⟩ := exists_finiteConstantProductEmbedding_of_hasStageModel
    (ProjectiveLineSystem.diagram R).op (ProjectiveLineSystem.cone R).op n hn M hM
  let t' := finiteConstantProductEmbeddingInverseImage e.hom t
  let E : (inverseImage e.hom).obj M.obj ≅ A.obj :=
    (Constructible.FiniteCogenerators.inverseImageEquivalenceOfIso e).counitIso.app A.obj
  exact ⟨finiteConstantProductEmbeddingOfMono E.inv t'⟩

/-- The exact accepted constructible-stage predicate on original native P1
has an actual finite constant product embedding, for every original ring. -/
theorem projectiveLine_finiteStage_embedding (n : ℕ) (hn : n ≠ 0)
    (M : Reduction.ZModSheaf (ProjectiveLine.projectiveP1 R) n)
    (hM : IsConstructibleFiniteStage (ProjectiveLine.projectiveP1 R) n M) :
    Nonempty (FiniteConstantProductEmbedding
      ((Reduction.zmodUnderlying (ProjectiveLine.projectiveP1 R) n).obj M)) :=
  exists_finiteConstantProductEmbedding_of_canonicalStages n
    (fun A hA => projectiveLine_canonicalStage_embedding R n hn A hA) M hM

variable [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]

/-- Original closed-residue pullback on native P1 is bijective in every
degree for every genuine positive-modulus coefficient, over an arbitrary
henselian local ring with separably closed residue field. -/
theorem projectiveLine_residuePullback_bijective (n : ℕ) (hn : n ≠ 0)
    (M : Reduction.ZModSheaf (ProjectiveLine.projectiveP1 R) n) (q : ℕ) :
    Function.Bijective (cohomologyPullback.{u, u + 2, u + 2}
      (pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))
      ((Reduction.zmodUnderlying (ProjectiveLine.projectiveP1 R) n).obj M) q) :=
  projectiveLine_residuePullback_bijective_of_finiteEmbeddings n hn
    (fun N hN => projectiveLine_finiteStage_embedding R n hn N hN) M q

/-- The actual original all-degree closed-residue comparison for every
original abelian coefficient killed by a positive modulus. -/
theorem projectiveLine_residuePullback_bijective_of_killed (n : ℕ) (hn : n ≠ 0)
    (F : AbelianSheaf.{u, u + 1} (ProjectiveLine.projectiveP1 R))
    (hF : n • 𝟙 F = 0) (q : ℕ) :
    Function.Bijective (cohomologyPullback.{u, u + 2, u + 2}
      (pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)) F q) :=
  projectiveLine_residuePullback_bijective_of_killed_finiteEmbeddings n hn
    (fun N hN => projectiveLine_finiteStage_embedding R n hn N hN) F hF q

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
