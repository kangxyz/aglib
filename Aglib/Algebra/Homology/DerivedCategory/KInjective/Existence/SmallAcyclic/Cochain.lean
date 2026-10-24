/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.SmallAcyclic.Countable
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.TruncLEHomology

/-!
# Small bounded-above acyclic subcomplexes

Every map from a separator into a term of an acyclic integer cochain complex
factors through a bounded-above acyclic subcomplex with a uniform bound on
all terms. The construction uses the actual native truncation, the countable
compatible construction, and native extension of complex shapes.

This is the factorization assertion underlying Stacks 079K. Set-sized
representatives and the K-injective detection argument are separate results.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.IsGrothendieckAbelian
  HomologicalComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {G : C} (hG : IsSeparator G)

/-- A separator map into an acyclic complex factors through an actual small
acyclic subcomplex supported in degrees at most one above the given degree.
The cardinal bound depends only on the separator, not on the complex or degree. -/
lemma exists_small_acyclic_subcomplex (M : CochainComplex C ℤ) (hM : M.Acyclic)
    (n : ℤ) (ψ : G ⟶ M.X n) :
    ∃ (L : CochainComplex C ℤ) (i : L ⟶ M),
      (∀ m, Mono (i.f m)) ∧ L.Acyclic ∧ L.IsStrictlyLE (n + 1) ∧
        (∀ m, HasCardinalLT (Subobject (L.X m)) (smallAcyclicCardinal hG)) ∧
        ∃ a : G ⟶ L.X n, a ≫ i.f n = ψ := by
  let e := ComplexShape.embeddingUpIntLE (n + 1)
  let T := M.truncLE' e
  have hn : e.f 1 = n := by simp [e]
  have hb : ¬ e.BoundaryLE 1 := by
    simp [e, ComplexShape.boundaryLE_embeddingUpIntLE_iff]
  have hT : T.Acyclic := by
    intro j
    apply (T.extend_exactAt_iff e (j := j) rfl).1
    exact ((hM.truncLE e) (e.f j)).of_iso (M.truncLEIso e)
  have hι : IsIso ((HomologicalComplex.ιTruncLE M e).f n) := by
    have h₁ : IsIso ((M.op.restrictionToTruncGE' e.op).f 1) :=
      M.op.isIso_restrictionToTruncGE' e.op 1 (by simpa using hb)
    have h₂ : IsIso ((M.op.πTruncGE e.op).f n) := by
      dsimp only [HomologicalComplex.πTruncGE]
      exact (e.op.isIso_liftExtend_f_iff _ _ hn).2 h₁
    exact inferInstanceAs (IsIso (((M.op.πTruncGE e.op).f n).unop))
  let u : T.extend e ⟶ M := (M.truncLEIso e).inv ≫ HomologicalComplex.ιTruncLE M e
  have : IsIso (u.f n) := by
    dsimp [u]
    infer_instance
  let ψ' : G ⟶ T.X 1 := ψ ≫ inv (u.f n) ≫ (T.extendXIso e hn).hom
  let hT' : ∀ j : ℕ, T.ExactAt (j + 1) := fun j ↦ hT (j + 1)
  let J := ChainComplex.SmallAcyclicPair.complex hG T ψ' hT'
  let φ : J ⟶ T := ChainComplex.SmallAcyclicPair.inclusion hG T ψ' hT'
  let L := J.extend e
  let i : L ⟶ M := HomologicalComplex.extendMap φ e ≫ u
  have hφ (j : ℕ) : Mono (φ.f j) :=
    ChainComplex.SmallAcyclicPair.inclusion_f_mono hG T ψ' hT' j
  have hJ : J.Acyclic := ChainComplex.SmallAcyclicPair.complex_acyclic hG T ψ' hT'
  have hsize (j : ℕ) : HasCardinalLT (Subobject (J.X j)) (smallAcyclicCardinal hG) :=
    ChainComplex.SmallAcyclicPair.complex_size hG T ψ' hT' j
  refine ⟨L, i, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    have hu : Mono (u.f m) := by
      dsimp [u]
      infer_instance
    have he : Mono ((HomologicalComplex.extendMap φ e).f m) := by
      by_cases hm : ∃ j, e.f j = m
      · obtain ⟨j, hj⟩ := hm
        rw [HomologicalComplex.extendMap_f φ e hj]
        have := hφ j
        infer_instance
      · exact (J.isZero_extend_X e m (by simpa using hm)).mono _
    change Mono ((HomologicalComplex.extendMap φ e).f m ≫ u.f m)
    infer_instance
  · intro m
    by_cases hm : ∃ j, e.f j = m
    · obtain ⟨j, hj⟩ := hm
      exact (J.extend_exactAt_iff e hj).2 (hJ j)
    · exact J.extend_exactAt e m (by simpa using hm)
  · exact inferInstanceAs ((J.extend e).IsStrictlySupported e)
  · intro m
    by_cases hm : ∃ j, e.f j = m
    · obtain ⟨j, hj⟩ := hm
      exact Subobject.hasCardinalLT_of_mono (hsize j) (J.extendXIso e hj).hom
    · have hz := J.isZero_extend_X e m (by simpa using hm)
      have : Mono (0 : L.X m ⟶ G) := hz.mono _
      exact Subobject.hasCardinalLT_of_mono
        ((hasCardinalLT_separator_ladder_zero hG).of_le
          (smallAcyclicCardinalLadder_lt hG 0).le) (0 : L.X m ⟶ G)
  · refine ⟨ChainComplex.SmallAcyclicPair.factor hG T ψ' hT' ≫
      (J.extendXIso e hn).inv, ?_⟩
    change (_ ≫ _) ≫ (HomologicalComplex.extendMap φ e).f n ≫ u.f n = ψ
    rw [HomologicalComplex.extendMap_f φ e hn]
    simp [φ, ψ', Category.assoc]

end CochainComplex
