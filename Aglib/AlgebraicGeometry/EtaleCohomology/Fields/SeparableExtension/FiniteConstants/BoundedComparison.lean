/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.SeparableExtension.FiniteConstants.FiniteImageTests
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.ConstructibleComparison

/-! # Original bounded-coefficient field comparison on the projective line

The published generic comparison criterion is applied to the original
projective line. Global Noetherian cogeneration supplies its genuine stages;
the original finite-over-line field comparison supplies its annihilator tests.
No general proper field-invariance theorem is used or asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard HasExt.standard

variable (k K : Type u) [Field k] [Field K] [IsSepClosed k] [IsSepClosed K]
  [Algebra k K]

/-- Original all-degree field comparison for every genuine positive-modulus
coefficient on the projective line. -/
theorem projectiveLine_fieldExtension_cohomologyPullback_bijective
    (n : ℕ) (hn : n ≠ 0)
    (M : Reduction.ZModSheaf (ProjectiveLine.projectiveP1 k) n) (q : ℕ) :
    Function.Bijective (cohomologyPullback.{u, u + 2, u + 2}
      (pullback.fst (ProjectiveLine.structureMap k) (Spec.algebraMap k K))
      ((Reduction.zmodUnderlying (ProjectiveLine.projectiveP1 k) n).obj M) q) := by
  let : IsNoetherian (ProjectiveLine.projectiveP1 k) := projectiveLine_isNoetherian k
  let : (ProjectiveLine.projectiveP1 k).IsSeparated := projectiveLine_isSeparated k
  let S := pullback (ProjectiveLine.structureMap k) (Spec.algebraMap k K)
  let pS := pullback.snd (ProjectiveLine.structureMap k) (Spec.algebraMap k K)
  let : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace pS
  let : QuasiSeparatedSpace S := quasiSeparatedSpace_of_quasiSeparated pS
  exact cohomologyPullback_bijective_of_constructible_finiteEmbeddings n
    (pullback.fst (ProjectiveLine.structureMap k) (Spec.algebraMap k K)) hn
    (fun N hN => ⟨finiteStageEmbeddingOfIsNoetherian n N hN⟩)
    (fun N hN =>
      (projectiveLine_fieldExtension_finiteConstantAnnihilator_bijective
        k K n N hN 0).injective)
    (fun N hN j =>
      (projectiveLine_fieldExtension_finiteConstantAnnihilator_bijective
        k K n N hN j).surjective)
    M q

/-- Every original bounded abelian coefficient on the projective line has
bijective original pullback over an arbitrary extension of separably closed fields. -/
theorem projectiveLine_fieldExtension_cohomologyPullback_bijective_of_killed
    (n : ℕ) (hn : n ≠ 0)
    (F : AbelianSheaf.{u, u + 1} (ProjectiveLine.projectiveP1 k))
    (hF : n • 𝟙 F = 0) (q : ℕ) :
    Function.Bijective (cohomologyPullback.{u, u + 2, u + 2}
      (pullback.fst (ProjectiveLine.structureMap k) (Spec.algebraMap k K)) F q) := by
  let M := TorsionZMod.sheaf (ProjectiveLine.projectiveP1 k).smallEtaleTopology n F hF
  let e : (Reduction.zmodUnderlying (ProjectiveLine.projectiveP1 k) n).obj M ≅ F :=
    TorsionZMod.sheafUnderlyingIso (ProjectiveLine.projectiveP1 k).smallEtaleTopology n F hF
  have h := projectiveLine_fieldExtension_cohomologyPullback_bijective k K n hn M q
  exact ⟨cohomologyPullback_injective_of_iso _ e q h.injective,
    cohomologyPullback_surjective_of_iso _ e q h.surjective⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
