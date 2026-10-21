/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Extension.Generators.LocalizedCotangent
public import Aglib.RingTheory.Extension.Presentation.RelationSpan
public import Aglib.LinearAlgebra.Matrix.GenericProjection
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Selecting original relations at a smooth generic point

The selected relations are a subfamily of the given presentation relations.
Their classes span the actual localized conormal module, and a minor of their
literal polynomial partial derivatives is nonzero. This statement neither
replaces the source presentation by an inverted chart nor discards the
unselected equations without a separate common-annihilator argument.
-/

@[expose] public section

noncomputable section

open TensorProduct MvPolynomial
open scoped Matrix

namespace Algebra.Presentation

variable {R B K σ ι : Type*} [CommRing R] [CommRing B] [Field K]
  [Algebra R B] [Algebra R K] [Algebra B K] [IsScalarTower R B K]

omit [Algebra R K] [IsScalarTower R B K] in
/-- An injective original conormal fibre selects original relations spanning
that fibre, together with a nonzero original Jacobian minor. -/
theorem exists_selected_relations_of_cotangent_injective
    [Finite σ] [Finite ι] (P : Presentation R B σ ι)
    (hinj : Function.Injective (P.toExtension.cotangentComplex.baseChange K)) :
    ∃ (r : ℕ) (rows : Fin r ↪ ι) (cols : Fin r ↪ σ),
      Submodule.span K (Set.range fun i => (1 : K) ⊗ₜ[B]
        Extension.Cotangent.mk (P := P.toExtension)
          ⟨P.relation (rows i), P.relation_mem_ker (rows i)⟩) = ⊤ ∧
      Matrix.det (Matrix.of fun i j => algebraMap B K
        (aeval P.val (pderiv (cols j) (P.relation (rows i))))) ≠ 0 := by
  classical
  let := Fintype.ofFinite σ
  let v : ι → K ⊗[B] P.toExtension.Cotangent := fun i =>
    (1 : K) ⊗ₜ[B] Extension.Cotangent.mk
      ⟨P.relation i, P.relation_mem_ker i⟩
  have hvspan : Submodule.span K (Set.range v) = ⊤ := by
    have h := congrArg (fun N : Submodule B P.toExtension.Cotangent =>
      N.baseChange K) P.span_relation_cotangent_eq_top
    rw [Submodule.baseChange_span, Submodule.baseChange_top, ← Set.range_comp'] at h
    exact h
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K v
  let : Finite κ := Finite.of_injective a ha
  let := Fintype.ofFinite κ
  let r := Fintype.card κ
  let e : Fin r ≃ κ := (Fintype.equivFin κ).symm
  let rows : Fin r ↪ ι := ⟨a ∘ e, ha.comp e.injective⟩
  have hrange : Set.range (v ∘ rows) = Set.range (v ∘ a) := by
    exact e.surjective.range_comp (v ∘ a)
  have hrows : Submodule.span K (Set.range (v ∘ rows)) = ⊤ := by
    rw [hrange, hspan, hvspan]
  have hrowsli : LinearIndependent K (v ∘ rows) := hli.comp e e.injective
  let b := P.toGenerators.cotangentSpaceBasis.baseChange K
  let L : K ⊗[B] P.toExtension.Cotangent →ₗ[K] (σ → K) :=
    b.equivFun.toLinearMap.comp (P.toExtension.cotangentComplex.baseChange K)
  have hL : Function.Injective L := b.equivFun.injective.comp
    hinj
  let A : Matrix (Fin r) σ K := fun i j => algebraMap B K
    (aeval P.val (pderiv j (P.relation (rows i))))
  have hLA : L ∘ (v ∘ rows) = A := by
    funext i j
    change b.equivFun ((P.toExtension.cotangentComplex.baseChange K) (v (rows i))) j = _
    rw [Module.Basis.equivFun_apply]
    exact P.toGenerators.cotangentSpaceBasis_baseChange_repr_cotangentComplex_mk
      ⟨P.relation (rows i), P.relation_mem_ker (rows i)⟩ j
  have hAli : LinearIndependent K A := by
    rw [← hLA]
    exact hrowsli.map' L (LinearMap.ker_eq_bot.mpr hL)
  have hA : Submodule.span K (Set.range Aᵀ) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    change Module.finrank K (Submodule.span K (Set.range A.col)) =
      Module.finrank K (Fin r → K)
    rw [← Matrix.rank_eq_finrank_span_cols A, hAli.rank_matrix, Module.finrank_pi]
  obtain ⟨cols, hdet⟩ := Matrix.exists_fullRow_minor_ne_zero_of_span_eq_top A hA
  have hcols : Function.Injective cols := by
    intro i j hij
    by_contra hne
    apply hdet
    apply Matrix.det_zero_of_column_eq hne
    intro k
    simp only [Matrix.submatrix_apply, hij]
  refine ⟨r, rows, ⟨cols, hcols⟩, hrows, ?_⟩
  exact hdet

/-- The generic smooth-localization specialization. -/
theorem exists_selected_relations_of_formallySmooth_localization
    [Finite σ] [Finite ι] (P : Presentation R B σ ι) (M : Submonoid B)
    [IsLocalization M K] [Algebra.FormallySmooth R K] :
    ∃ (r : ℕ) (rows : Fin r ↪ ι) (cols : Fin r ↪ σ),
      Submodule.span K (Set.range fun i => (1 : K) ⊗ₜ[B]
        Extension.Cotangent.mk (P := P.toExtension)
          ⟨P.relation (rows i), P.relation_mem_ker (rows i)⟩) = ⊤ ∧
      Matrix.det (Matrix.of fun i j => algebraMap B K
        (aeval P.val (pderiv (cols j) (P.relation (rows i))))) ≠ 0 :=
  P.exists_selected_relations_of_cotangent_injective
    (P.toGenerators.cotangentComplex_baseChange_injective_of_formallySmooth_localization M)

end Algebra.Presentation
