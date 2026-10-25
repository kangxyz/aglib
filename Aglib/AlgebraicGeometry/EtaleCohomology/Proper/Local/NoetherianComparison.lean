/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.ProjectiveLineCriterion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.AffineFPTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Original Noetherian projective-line comparison

The genuine constructible stages have original finite constant product
embeddings on a Noetherian base. Their actual affine-open FP hypothesis
transports to every original open spectrum chart, as required by the global
finite-cogenerator theorem. This discharges the geometric premise of the
projective-line criterion.

The conclusion uses the literal residue-fibre inclusion and every original
abelian coefficient killed by a positive modulus. No finite family,
constructibility or finite-presentation premise is imposed on that coefficient.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard HasExt.standard

/-- The actual proper projective-line structure map over an affine base
supplies separatedness, hence native quasi-separatedness of the source. -/
theorem projectiveLine_isSeparated (R : Type u) [CommRing R] :
    (ProjectiveLine.projectiveP1 R).IsSeparated := by
  constructor
  rw [← terminal.comp_from (ProjectiveLine.structureMap R)]
  infer_instance

/-- The literal residue fibre is separated over its affine residue-field
base by the base change of the same proper projective-line structure map. -/
theorem projectiveLine_residueFiber_isSeparated
    (R : Type u) [CommRing R] [IsLocalRing R] :
    (pullback (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)).IsSeparated := by
  constructor
  rw [← terminal.comp_from
    (pullback.snd (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))]
  infer_instance

/-- The actual projective-line structure map over a Noetherian ring gives a
locally Noetherian, compact source. -/
theorem projectiveLine_isNoetherian (R : Type u) [CommRing R] [IsNoetherianRing R] :
    IsNoetherian (ProjectiveLine.projectiveP1 R) := {
  toIsLocallyNoetherian :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine.structureMap R)
  toCompactSpace :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine.structureMap R) }

/-- The literal residue fibre is Noetherian by its base-changed proper
structure map over the original residue field. The local base ring itself
need not be Noetherian for this fact. -/
theorem projectiveLine_residueFiber_isNoetherian
    (R : Type u) [CommRing R] [IsLocalRing R] :
    IsNoetherian
      (pullback (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)) := {
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
    (pullback.snd (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
    (pullback.snd (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)) }

/-- A genuine constructible stage on a Noetherian scheme has an original
finite constant product embedding. The stage's actual affine-open restrictions
supply the full original spectrum-chart FP input. -/
def finiteStageEmbeddingOfIsNoetherian
    {X : Scheme.{u}} [IsNoetherian X] (n : ℕ)
    (M : Reduction.ZModSheaf X n) (hM : IsConstructibleFiniteStage X n M) :
    FiniteConstantProductEmbedding ((Reduction.zmodUnderlying X n).obj M) :=
  Global.finiteConstantProductEmbeddingOfIsNoetherian X
    ((Reduction.zmodUnderlying X n).obj M) hM.1
    (affineRestriction_isFinitelyPresentable_spec_open _ hM.2.2)

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)] (n : ℕ)

/-- Original all-degree closed-residue comparison for every genuine
positive-modulus coefficient on the native projective line over a Noetherian
henselian local ring with separably closed residue field. -/
theorem projectiveLine_residuePullback_bijective_of_isNoetherian
    (hn : n ≠ 0) (M : Reduction.ZModSheaf (ProjectiveLine.projectiveP1 R) n) (q : ℕ) :
    Function.Bijective (cohomologyPullback.{u, u + 2, u + 2}
      (pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))
      ((Reduction.zmodUnderlying (ProjectiveLine.projectiveP1 R) n).obj M) q) := by
  let : IsNoetherian (ProjectiveLine.projectiveP1 R) := projectiveLine_isNoetherian R
  exact projectiveLine_residuePullback_bijective_of_finiteEmbeddings n hn
    (fun N hN => ⟨finiteStageEmbeddingOfIsNoetherian n N hN⟩) M q

/-- Every original abelian coefficient killed by a positive modulus has
bijective original closed-residue pullback in every degree. All finite
cogeneration, presentation and geometric hypotheses are constructed. -/
theorem projectiveLine_residuePullback_bijective_of_killed_of_isNoetherian
    (hn : n ≠ 0) (F : AbelianSheaf.{u, u + 1} (ProjectiveLine.projectiveP1 R))
    (hF : n • 𝟙 F = 0) (q : ℕ) :
    Function.Bijective (cohomologyPullback.{u, u + 2, u + 2}
      (pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)) F q) := by
  let : IsNoetherian (ProjectiveLine.projectiveP1 R) := projectiveLine_isNoetherian R
  exact projectiveLine_residuePullback_bijective_of_killed_finiteEmbeddings n hn
    (fun N hN => ⟨finiteStageEmbeddingOfIsNoetherian n N hN⟩) F hF q

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
