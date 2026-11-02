/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.SelectedElimination

/-!
# Strict finite-cardinality induction on actual contracted curves

A selected curve is eliminated by the constructed finite normalized-point
block. Its actual proper-image embedding misses that curve, so the finite
cardinality strictly decreases. At zero the actual morphism is an isomorphism;
its inverse supplies the comparison map. All chains and scheme arrows compose
literally.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.NormalizedPointDomination

universe u
open Blowup

private def pointChainDomination {Q S : Scheme.{u}} [IsIntegral Q] [IsIntegral S]
    (q : Q ⟶ S) : Prop :=
  ∃ (T : Scheme.{u}) (beta : T ⟶ S) (a : T ⟶ Q) (hT : IsIntegral T),
    letI := hT
    ∃ (hbeta : IsDominant beta) (ha : IsDominant a),
      letI := hbeta
      letI := ha
      ∃ (_ : NormalizedPointBlowupChain beta),
        a ≫ q = beta ∧ NormalStalks T ∧ IsNoetherian T ∧ topologicalKrullDim T ≤ 2 ∧
          IsProper beta ∧ IsProper a ∧
          IsIso (CommRingCat.ofHom (functionFieldMap beta)) ∧
          IsIso (CommRingCat.ofHom (functionFieldMap a))

private theorem exists_domination_by_curve_count
    {P : Scheme.{u}} [IsIntegral P] [IsNoetherian P]
    (hNagata : ∀ V : P.affineOpens, Nonempty V.1 → IsNagataRing.{u, 0} Γ(P, V.1))
    (hdP : topologicalKrullDim P ≤ 2)
    {S Q : Scheme.{u}} [IsIntegral S] [IsIntegral Q] [IsNoetherian S] [IsNoetherian Q]
    (b : S ⟶ P) [IsProper b] [IsDominant b]
    (hb : IsIso (CommRingCat.ofHom (functionFieldMap b)))
    (hS : NormalStalks S) (hQ : NormalStalks Q) (hdQ : topologicalKrullDim Q ≤ 2)
    (q : Q ⟶ S) [IsProper q] [IsDominant q]
    (hq : IsIso (CommRingCat.ofHom (functionFieldMap q)))
    (n : ℕ) (hcount : contractedCurveCount q = n) : pointChainDomination q := by
  classical
  induction n using Nat.strong_induction_on generalizing S Q with
  | h n ih =>
    by_cases hzero : contractedCurveCount q = 0
    · have hdS := dimension_le_two_of_birational b hNagata hdP hb
      let : IsIso q := isIso_of_contractedCurveCount_eq_zero q hq hS hdQ hdS hzero
      refine ⟨S, 𝟙 S, inv q, inferInstance, inferInstance, inferInstance,
        NormalizedPointBlowupChain.refl S, ?_, hS, inferInstance, hdS,
        inferInstance, inferInstance, ?_, ?_⟩
      · simp only [IsIso.inv_hom_id]
      · exact FunctionField.fieldMap_isIso (𝟙 S)
      · exact FunctionField.fieldMap_isIso (inv q)
    · let : Finite (contractedCurves q) := (finite_contractedCurves q hq hS hdQ).to_subtype
      have hnonempty : Nonempty (contractedCurves q) :=
        (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hzero)).1
      obtain ⟨C⟩ := hnonempty
      obtain ⟨B, hmiss⟩ := exists_comparison_missing_curve b hb hNagata hdP hS hQ hdQ q hq C
      let e := B.curveEmbedding hQ hdQ
      let : Finite (contractedCurves B.p) := Finite.of_injective e e.injective
      let : Fintype (contractedCurves q) := Fintype.ofFinite _
      let : Fintype (contractedCurves B.p) := Fintype.ofFinite _
      have hlt : contractedCurveCount B.p < contractedCurveCount q := by
        simpa only [contractedCurveCount, Nat.card_eq_fintype_card] using
          Fintype.card_lt_of_injective_of_notMem e e.injective hmiss
      have hlt' : contractedCurveCount B.p < n := hcount ▸ hlt
      have hBb : IsIso (CommRingCat.ofHom (functionFieldMap (B.beta ≫ b))) := by
        let := B.betaBirational
        let := hb
        rw [functionFieldMap_comp, CommRingCat.ofHom_comp]
        infer_instance
      obtain ⟨T, beta, a, hT, hbetaD, haD, c, he, hTN, hTNoeth, hdT, hbetaP, haP,
        hbetaff, haff⟩ := ih (contractedCurveCount B.p) hlt' (b := B.beta ≫ b) hBb
          B.baseNormal B.modelNormal B.modelDimension B.p B.pBirational rfl
      let := hT
      let := hbetaD
      let := haD
      let := hbetaP
      let := haP
      refine ⟨T, beta ≫ B.beta, a ≫ B.g, inferInstance, inferInstance, inferInstance,
        B.chain.comp c, ?_, hTN, hTNoeth, hdT, inferInstance, inferInstance, ?_, ?_⟩
      · calc
          (a ≫ B.g) ≫ q = a ≫ (B.g ≫ q) := Category.assoc _ _ _
          _ = a ≫ (B.p ≫ B.beta) := congrArg (fun k ↦ a ≫ k) B.comm
          _ = (a ≫ B.p) ≫ B.beta := (Category.assoc _ _ _).symm
          _ = beta ≫ B.beta := congrArg (fun k ↦ k ≫ B.beta) he
      · let := hbetaff
        let := B.betaBirational
        rw [functionFieldMap_comp, CommRingCat.ofHom_comp]
        infer_instance
      · let := haff
        let := B.gBirational
        rw [functionFieldMap_comp, CommRingCat.ofHom_comp]
        infer_instance

/-- Domination of an actual proper birational normal-source model over a
normal surface by a constructed finite normalized-point chain. No resolving
chain or termination certificate is an input; both finite inductions are
performed on the actual curve data and maps. -/
theorem exists_normalSource_domination
    {P S Q : Scheme.{u}} [IsIntegral P] [IsIntegral S] [IsIntegral Q]
    [IsNoetherian P] [IsNoetherian S] [IsNoetherian Q]
    (b : S ⟶ P) [IsProper b] [IsDominant b]
    (hb : IsIso (CommRingCat.ofHom (functionFieldMap b)))
    (hNagata : ∀ V : P.affineOpens, Nonempty V.1 → IsNagataRing.{u, 0} Γ(P, V.1))
    (hdP : topologicalKrullDim P ≤ 2)
    (hS : NormalStalks S) (hQ : NormalStalks Q) (hdQ : topologicalKrullDim Q ≤ 2)
    (q : Q ⟶ S) [IsProper q] [IsDominant q]
    (hq : IsIso (CommRingCat.ofHom (functionFieldMap q))) :
    ∃ (T : Scheme.{u}) (beta : T ⟶ S) (a : T ⟶ Q) (hT : IsIntegral T),
      letI := hT
      ∃ (hbeta : IsDominant beta) (ha : IsDominant a),
        letI := hbeta
        letI := ha
        ∃ (_ : NormalizedPointBlowupChain beta),
          a ≫ q = beta ∧ NormalStalks T ∧ IsNoetherian T ∧ topologicalKrullDim T ≤ 2 ∧
            IsProper beta ∧ IsProper a ∧
            IsIso (CommRingCat.ofHom (functionFieldMap beta)) ∧
            IsIso (CommRingCat.ofHom (functionFieldMap a)) :=
  exists_domination_by_curve_count hNagata hdP b hb hS hQ hdQ q hq _ rfl

end AlgebraicGeometry.Scheme.NormalizedPointDomination
