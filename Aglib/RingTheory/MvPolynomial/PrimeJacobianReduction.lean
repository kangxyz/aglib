/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Extension.Presentation.SelectedRelations
public import Aglib.RingTheory.Extension.ConormalResidueSpan
public import Aglib.RingTheory.Ideal.ResidueSpan
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Selecting equations at the original generic prime

For a prime of a finite polynomial algebra whose actual residue field is
formally smooth over the coefficient ring, this theorem selects original
relations and variable columns with a nonvanishing Jacobian determinant.
One common multiplier outside the same prime recovers every element of the
original prime ideal. Formal smoothness of the residue field is an explicit
intermediate hypothesis, not a replacement for the separability step in Artin
approximation and not an assumption justified at a mixed-characteristic
closed center.
-/

@[expose] public section

noncomputable section

open TensorProduct

namespace MvPolynomial

variable {R σ ι : Type*} [CommRing R] [IsNoetherianRing R]
  [Finite σ] [Finite ι]

/-- Select a nonzero original Jacobian minor and one common multiplier which
recovers the entire original prime ideal from the selected original relations. -/
theorem exists_selected_jacobian_minor_and_multiplier
    (q : Ideal (MvPolynomial σ R)) [q.IsPrime]
    [Algebra.FormallySmooth R q.ResidueField]
    (F : ι → MvPolynomial σ R) (hF : Ideal.span (Set.range F) = q) :
    ∃ (r : ℕ) (rows : Fin r ↪ ι) (cols : Fin r ↪ σ) (h : MvPolynomial σ R),
      h ∉ q ∧
      Matrix.det (Matrix.of fun i j => pderiv (cols j) (F (rows i))) ∉ q ∧
      ∀ f ∈ q, h * f ∈ Ideal.span (Set.range fun i => F (rows i)) := by
  classical
  let B := MvPolynomial σ R ⧸ q
  let K := q.ResidueField
  let G : Algebra.Generators R B σ := Algebra.Generators.naive
  have hker : G.ker = q := Algebra.Generators.ker_naive _ _
  let P : Algebra.Presentation R B σ ι :=
    { G with relation := F, span_range_relation_eq_ker := hF.trans hker.symm }
  obtain ⟨r, rows, cols, hspan, hdet⟩ :=
    P.exists_selected_relations_of_formallySmooth_localization (K := K) (nonZeroDivisors B)
  let v : Fin r → P.ker := fun i => ⟨F (rows i), P.relation_mem_ker (rows i)⟩
  have htransport := @Algebra.Extension.span_kernel_tmul_eq_top_iff
    R B K (Fin r) _ _ _ _ P.toExtension
    (inferInstance : Algebra B K)
    (inferInstance : Algebra (MvPolynomial σ R) K)
    (inferInstance : IsScalarTower (MvPolynomial σ R) B K) v
  have hspan' : Submodule.span K (Set.range fun i =>
      (1 : K) ⊗ₜ[MvPolynomial σ R] v i) = ⊤ := htransport.mpr hspan
  let e : P.ker ≃ₗ[MvPolynomial σ R] q := LinearEquiv.ofEq _ _ hker
  let eK : K ⊗[MvPolynomial σ R] P.ker ≃ₗ[K] K ⊗[MvPolynomial σ R] q :=
    e.baseChange (MvPolynomial σ R) K _ _
  let w : Fin r → q := fun i => e (v i)
  have hspanq : Submodule.span K (Set.range fun i =>
      (1 : K) ⊗ₜ[MvPolynomial σ R] w i) = ⊤ := by
    have hm := congrArg (Submodule.map eK.toLinearMap) hspan'
    rw [Submodule.map_span, ← Set.range_comp', Submodule.map_top,
      LinearMap.range_eq_top.mpr eK.surjective] at hm
    simpa only [Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.baseChange_tmul, eK, w] using hm
  obtain ⟨h, hh, hmul⟩ := q.exists_notMem_mul_mem_span_of_residue_span w hspanq
  refine ⟨r, rows, cols, h, hh, ?_, ?_⟩
  · intro hz
    apply hdet
    have hzero := Ideal.algebraMap_residueField_eq_zero.mpr hz
    rw [RingHom.map_det] at hzero
    convert hzero using 1
    congr 1
    funext i j
    change algebraMap B K (aeval G.val (pderiv (cols j) (F (rows i)))) = _
    rw [← G.algebraMap_apply]
    exact (IsScalarTower.algebraMap_apply (MvPolynomial σ R) B K _).symm
  · simpa only [w, e, LinearEquiv.coe_ofEq_apply, v] using hmul

end MvPolynomial
