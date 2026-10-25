/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.ConstructibleComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.ProjectiveLineCogenerators

/-! # Original projective-line comparison from geometric finite embeddings

The actual curve tests, genuine module injectives, geometric presentations
and cohomological colimits supply all inputs of the local criterion except
global finite cogeneration of its actual stages. The conclusion concerns the
original closed-fibre pullback in every degree. Global finite cogeneration
and conversion to universal proper exchange are not asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard HasExt.standard

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)] (n : ℕ)

/-- Original all-degree closed-fibre comparison for genuine positive-modulus
coefficients, from actual global finite embeddings of the geometric stages.
All categorical presentation and continuity hypotheses are constructed. -/
theorem projectiveLine_residuePullback_bijective_of_finiteEmbeddings
    (hn : n ≠ 0)
    (hfinite : ∀ M : Reduction.ZModSheaf (ProjectiveLine.projectiveP1 R) n,
      IsConstructibleFiniteStage (ProjectiveLine.projectiveP1 R) n M →
        Nonempty (FiniteConstantProductEmbedding
          ((Reduction.zmodUnderlying (ProjectiveLine.projectiveP1 R) n).obj M)))
    (M : Reduction.ZModSheaf (ProjectiveLine.projectiveP1 R) n) (q : ℕ) :
    Function.Bijective (cohomologyPullback.{u, u + 2, u + 2}
      (pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))
      ((Reduction.zmodUnderlying (ProjectiveLine.projectiveP1 R) n).obj M) q) := by
  let : CompactSpace (ProjectiveLine.projectiveP1 R) :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine.structureMap R)
  let S₀ : Scheme.{u} :=
    pullback (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)
  let : CompactSpace S₀ :=
    QuasiCompact.compactSpace_of_compactSpace
      (pullback.snd (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))
  exact cohomologyPullback_bijective_of_constructible_finiteEmbeddings n
    (pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)) hn hfinite
    (fun N hN => finiteConstantAnnihilator_residuePullback_injective_zero N hN)
    (fun N hN k => finiteConstantAnnihilator_residuePullback_surjective N hN k) M q

/-- Canonical scalar conversion retains the actual original abelian
coefficient and its closed-fibre map. No forgotten injectivity is assumed. -/
theorem projectiveLine_residuePullback_bijective_of_killed_finiteEmbeddings
    (hn : n ≠ 0)
    (hfinite : ∀ M : Reduction.ZModSheaf (ProjectiveLine.projectiveP1 R) n,
      IsConstructibleFiniteStage (ProjectiveLine.projectiveP1 R) n M →
        Nonempty (FiniteConstantProductEmbedding
          ((Reduction.zmodUnderlying (ProjectiveLine.projectiveP1 R) n).obj M)))
    (F : AbelianSheaf.{u, u + 1} (ProjectiveLine.projectiveP1 R))
    (hF : n • 𝟙 F = 0) (q : ℕ) :
    Function.Bijective (cohomologyPullback.{u, u + 2, u + 2}
      (pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)) F q) := by
  let M := TorsionZMod.sheaf (ProjectiveLine.projectiveP1 R).smallEtaleTopology n F hF
  let e : (Reduction.zmodUnderlying (ProjectiveLine.projectiveP1 R) n).obj M ≅ F :=
    TorsionZMod.sheafUnderlyingIso (ProjectiveLine.projectiveP1 R).smallEtaleTopology n F hF
  have h := projectiveLine_residuePullback_bijective_of_finiteEmbeddings n hn hfinite M q
  exact ⟨cohomologyPullback_injective_of_iso _ e q h.injective,
    cohomologyPullback_surjective_of_iso _ e q h.surjective⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
