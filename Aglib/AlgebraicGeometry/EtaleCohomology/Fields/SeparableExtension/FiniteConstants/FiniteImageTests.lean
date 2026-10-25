/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.SeparableExtension.FiniteConstants.FieldComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.FiniteProducts

/-! # Original finite-image and annihilator tests over a field extension -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u

attribute [local instance] hasSheafifyLarge HasExt.standard

variable (k K : Type u) [Field k] [Field K] [IsSepClosed k] [IsSepClosed K]
  [Algebra k K]

private def fieldFiniteMap {Y : Scheme.{u}} (f : Y ⟶ ProjectiveLine.projectiveP1 k) :
    pullback (f ≫ ProjectiveLine.structureMap k) (Spec.algebraMap k K) ⟶
      pullback (ProjectiveLine.structureMap k) (Spec.algebraMap k K) :=
  ((Over.pullback (Spec.algebraMap k K)).map
    (Over.homMk f rfl : Over.mk (f ≫ ProjectiveLine.structureMap k) ⟶
      Over.mk (ProjectiveLine.structureMap k))).left

omit [IsSepClosed k] [IsSepClosed K] in
private theorem fieldFiniteMap_fst {Y : Scheme.{u}}
    (f : Y ⟶ ProjectiveLine.projectiveP1 k) :
    fieldFiniteMap k K f ≫
        pullback.fst (ProjectiveLine.structureMap k) (Spec.algebraMap k K) =
      pullback.fst (f ≫ ProjectiveLine.structureMap k) (Spec.algebraMap k K) ≫ f := by
  dsimp only [fieldFiniteMap, Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

omit [IsSepClosed k] [IsSepClosed K] in
private theorem fieldFiniteMap_snd {Y : Scheme.{u}}
    (f : Y ⟶ ProjectiveLine.projectiveP1 k) :
    fieldFiniteMap k K f ≫
        pullback.snd (ProjectiveLine.structureMap k) (Spec.algebraMap k K) =
      pullback.snd (f ≫ ProjectiveLine.structureMap k) (Spec.algebraMap k K) := by
  dsimp only [fieldFiniteMap, Over.pullback_map_left]
  exact pullback.lift_snd _ _ _

omit [IsSepClosed k] [IsSepClosed K] in
private theorem fieldFiniteMap_isPullback {Y : Scheme.{u}}
    (f : Y ⟶ ProjectiveLine.projectiveP1 k) :
    IsPullback
      (pullback.fst (f ≫ ProjectiveLine.structureMap k) (Spec.algebraMap k K))
      (fieldFiniteMap k K f) f
      (pullback.fst (ProjectiveLine.structureMap k) (Spec.algebraMap k K)) := by
  have hOuter := IsPullback.of_hasPullback (ProjectiveLine.structureMap k) (Spec.algebraMap k K)
  have hTotal := IsPullback.of_hasPullback
    (f ≫ ProjectiveLine.structureMap k) (Spec.algebraMap k K)
  have hTotal' : IsPullback
      (pullback.fst (f ≫ ProjectiveLine.structureMap k) (Spec.algebraMap k K))
      (fieldFiniteMap k K f ≫
        pullback.snd (ProjectiveLine.structureMap k) (Spec.algebraMap k K))
      (f ≫ ProjectiveLine.structureMap k) (Spec.algebraMap k K) := by
    simpa only [fieldFiniteMap_snd] using hTotal
  exact (hTotal'.flip.of_right (fieldFiniteMap_fst k K f) hOuter.flip).flip

/-- The original finite-H square transfers the finite-over-line field comparison
to each actual finite constant direct-image coefficient on the line. -/
theorem projectiveLine_fieldExtension_finiteConstantDirectImage_bijective
    {Y : Scheme.{u}} (f : Y ⟶ ProjectiveLine.projectiveP1 k) [IsFinite f]
    (A : Type u) [AddCommGroup A] [Finite A] (q : ℕ) :
    Function.Bijective (cohomologyPullback.{u, u + 2, u + 2}
      (pullback.fst (ProjectiveLine.structureMap k) (Spec.algebraMap k K))
      ((directImage f).obj (ConstantFinite.coefficient A Y)) q) := by
  let i := pullback.fst (f ≫ ProjectiveLine.structureMap k) (Spec.algebraMap k K)
  have hc := Curves.finite_projectiveLine_fieldExtension_constantRestriction_bijective
    k K f A q
  let E := (inverseImageConstantIso i).app (ConstantFinite.value A)
  have hsource : Function.Bijective
      (cohomologyPullback.{u, u + 2, u + 2} i (ConstantFinite.coefficient A Y) q) := by
    constructor
    · intro a b hab
      apply hc.injective
      exact congrArg (Sheaf.H.map E.hom q) hab
    · intro z
      obtain ⟨a, ha⟩ := hc.surjective (Sheaf.H.map E.hom q z)
      exact ⟨a, (cohomologyMapIso_bijective E q).injective ha⟩
  exact ⟨cohomologyPullback_finiteDirectImage_injective f (fieldFiniteMap k K f)
      (pullback.fst (ProjectiveLine.structureMap k) (Spec.algebraMap k K)) i
      (fieldFiniteMap_isPullback k K f) (ConstantFinite.coefficient A Y) q hsource.injective,
    cohomologyPullback_finiteDirectImage_surjective f (fieldFiniteMap k K f)
      (pullback.fst (ProjectiveLine.structureMap k) (Spec.algebraMap k K)) i
      (fieldFiniteMap_isPullback k K f) (ConstantFinite.coefficient A Y) q hsource.surjective⟩

private theorem exists_small_finiteValueIso (A : AddCommGrpCat.{u + 1}) [Finite A] :
    ∃ (B : Type u) (_ : AddCommGroup B) (_ : Finite B),
      Nonempty (ConstantFinite.value B ≅ A) := by
  let := Fintype.ofFinite A
  have : Small.{u} A := Small.mk'
    ((Fintype.equivFin A).trans (Equiv.ulift.{u}).symm)
  let B := Shrink.{u} A
  have : Finite B := Finite.of_equiv A (equivShrink A)
  exact ⟨B, inferInstance, inferInstance,
    ⟨AddEquiv.toAddCommGrpIso (AddEquiv.ulift.trans (Shrink.addEquiv (α := A)))⟩⟩

/-- Finite values in the native sheaf-value universe are transported through
their actual additive equivalence to a small finite value. -/
theorem projectiveLine_fieldExtension_finiteValueDirectImage_bijective
    {Y : Scheme.{u}} (f : Y ⟶ ProjectiveLine.projectiveP1 k) [IsFinite f]
    (A : AddCommGrpCat.{u + 1}) [Finite A] (q : ℕ) :
    Function.Bijective (cohomologyPullback.{u, u + 2, u + 2}
      (pullback.fst (ProjectiveLine.structureMap k) (Spec.algebraMap k K))
      ((directImage f).obj
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)) q) := by
  obtain ⟨B, _, _, ⟨e⟩⟩ := exists_small_finiteValueIso A
  let eF := (directImage f).mapIso
    ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso e)
  have hb := projectiveLine_fieldExtension_finiteConstantDirectImage_bijective k K f B q
  exact ⟨cohomologyPullback_injective_of_iso _ eF q hb.injective,
    cohomologyPullback_surjective_of_iso _ eF q hb.surjective⟩

/-- Every actual geometric finite-constant annihilator target has bijective
original field-extension pullback. No comparison property is part of its predicate. -/
theorem projectiveLine_fieldExtension_finiteConstantAnnihilator_bijective
    (n : ℕ) (M : Reduction.ZModSheaf (ProjectiveLine.projectiveP1 k) n)
    (hM : IsFiniteConstantAnnihilator (ProjectiveLine.projectiveP1 k) n M) (q : ℕ) :
    Function.Bijective (cohomologyPullback.{u, u + 2, u + 2}
      (pullback.fst (ProjectiveLine.structureMap k) (Spec.algebraMap k K))
      ((Reduction.zmodUnderlying (ProjectiveLine.projectiveP1 k) n).obj M) q) := by
  obtain ⟨I, hI, Y, f, A, hf, hA, ⟨e⟩⟩ := hM
  let := hI
  let := hf
  let := hA
  let B : I → AddCommGrpCat.{u + 1} := fun i => kernel (n • 𝟙 (ConstantFinite.value (A i)))
  have (i : I) : Finite (B i) := finite_nsmulKernelValue n (ConstantFinite.value (A i))
  let G : AbelianSheaf.{u, u + 1} (ProjectiveLine.projectiveP1 k) :=
    ∏ᶜ fun i => (directImage (f i)).obj
      ((constantSheaf (Y i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj (B i))
  let g := pullback.fst (ProjectiveLine.structureMap k) (Spec.algebraMap k K)
  have hG : Function.Bijective (cohomologyPullback.{u, u + 2, u + 2} g G q) :=
    ⟨cohomologyPullback_injective_finiteProduct g _ q (fun i =>
        (projectiveLine_fieldExtension_finiteValueDirectImage_bijective
          k K (f i) (B i) q).injective),
      cohomologyPullback_surjective_finiteProduct g _ q (fun i =>
        (projectiveLine_fieldExtension_finiteValueDirectImage_bijective
          k K (f i) (B i) q).surjective)⟩
  let E : (Reduction.zmodUnderlying (ProjectiveLine.projectiveP1 k) n).obj M ≅ G :=
    e ≪≫ constantDirectImageProductAnnihilatorIsoFiniteIndex n Y f
      (fun i => ConstantFinite.value (A i))
  exact ⟨cohomologyPullback_injective_of_iso g E.symm q hG.injective,
    cohomologyPullback_surjective_of_iso g E.symm q hG.surjective⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
