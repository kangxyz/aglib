/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteFieldLocalMaps

/-! One actual finite field stage carrying all models on the finite intersection cover. -/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange baseChangeComp)
namespace AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent
universe u
variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (Y : Scheme.FiniteEtale
    (pullback p (Spec.algebraMap K Ω)))
  {J : Type u} [Finite J] (U : J → X.Opens) (hU : IsOpenCover U) (hAffine : ∀ j, IsAffineOpen (U j))

/-- Starting with the real affine producer, enlarge its finitely many stages and restrict
one containing affine model to each intersection. No model or arrow input is assumed. -/
def intersectionModels :
    Σ s : Finset Ω,
      Σ M : ∀ i : (intersectionCover U hU).I₀,
        Scheme.FiniteEtale (((FieldLimit.schemeDiagram K Ω ((intersectionCover U hU).f i ≫ p)).obj
          (op s)).left),
      ∀ i : (intersectionCover U hU).I₀,
        (baseChange (FieldLimit.fieldProjection K Ω ((intersectionCover U hU).f i ≫ p) (op
          s))).obj (M i) ≅
          (baseChange (geometricMap K Ω ((intersectionCover U hU).f i ≫ p) p
            ((intersectionCover U hU).f i) rfl)).obj Y := by
  classical
  let := Fintype.ofFinite J
  have (j : J) : IsAffine (U j).toScheme := hAffine j
  let D (j : J) := affineCoverDescent K Ω ((U j).ι ≫ p)
    ((baseChange (geometricMap K Ω ((U j).ι ≫ p) p (U j).ι rfl)).obj Y)
  let s := Finset.univ.biUnion fun j ↦ (D j).1
  have hs (j : J) : (D j).1 ⊆ s := Finset.subset_biUnion_of_mem (fun j ↦ (D j).1)
    (Finset.mem_univ j)
  let Z (j : J) := enlargeStage K Ω ((U j).ι ≫ p) (hs j) (D j).2.1
  let e (j : J) := enlargeStageIso K Ω ((U j).ι ≫ p) (hs j) (D j).2.1
    ((baseChange (geometricMap K Ω ((U j).ι ≫ p) p (U j).ι rfl)).obj Y) (D j).2.2
  let 𝒰 := intersectionCover U hU
  let v (i : 𝒰.I₀) : J := (intersectionOpen_le_chart U i).choose
  let l (i : 𝒰.I₀) : 𝒰.X i ⟶ (U (v i)).toScheme :=
    X.homOfLE (intersectionOpen_le_chart U i).choose_spec
  have hl (i : 𝒰.I₀) : l i ≫ (U (v i)).ι = 𝒰.f i := by
    exact X.homOfLE_ι _
  have hp (i : 𝒰.I₀) : l i ≫ ((U (v i)).ι ≫ p) = 𝒰.f i ≫ p := by
    rw [← Category.assoc, hl]
  let a (i : 𝒰.I₀) := stageMap K Ω (𝒰.f i ≫ p) ((U (v i)).ι ≫ p) (l i) (hp i) s
  let r (i : 𝒰.I₀) := geometricMap K Ω (𝒰.f i ≫ p) ((U (v i)).ι ≫ p) (l i) (hp i)
  let M (i : 𝒰.I₀) := (baseChange (a i)).obj (Z (v i))
  refine ⟨s, M, fun i ↦ ?_⟩
  exact restrictDescentIso _ _ (a i) (r i)
    (geometricMap_projection K Ω (𝒰.f i ≫ p) ((U (v i)).ι ≫ p) (l i) (hp i) s).symm
      (Z (v i)) _ (e (v i)) ≪≫
    (baseChangeComp (geometricMap K Ω ((U (v i)).ι ≫ p) p (U (v i)).ι rfl) (r i)).symm.app Y ≪≫
    eqToIso (congrArg (fun k ↦ (baseChange k).obj Y)
      (geometricMap_comp_of_triangle K Ω (𝒰.f i ≫ p) ((U (v i)).ι ≫ p) (l i) (hp i)
        p (U (v i)).ι rfl (𝒰.f i) rfl (hl i)))

end AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 d587b3a3af73c59b665c80db5f4a3f5cdb6450bc1631a24b0dd8f722090e46c2.
Definitions, hypotheses and universes are retained modulo native names. -/
