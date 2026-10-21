/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPolynomial.PrimeJacobianReduction
public import Mathlib.RingTheory.Smooth.Locus

/-! # Selecting original equations at a smooth centre

The residue field need not be smooth over the coefficient ring. Smoothness is
assumed only at the actual local ring of the quotient. The resulting original
Jacobian minor and common multiplier both avoid the same actual centre.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open TensorProduct

namespace MvPolynomial

variable {R σ ι : Type*} [CommRing R] [IsNoetherianRing R]
  [Finite σ] [Finite ι]

/-- Select original equations at a smooth prime of their actual quotient.
The multiplier recovers every original relation, not only its conormal class. -/
theorem exists_selected_jacobian_minor_and_multiplier_at_smooth_centre
    (I : Ideal (MvPolynomial σ R))
    (q : Ideal (MvPolynomial σ R ⧸ I)) [q.IsPrime]
    [Algebra.IsSmoothAt R q]
    (F : ι → MvPolynomial σ R) (hF : Ideal.span (Set.range F) = I) :
    ∃ (r : ℕ) (rows : Fin r ↪ ι) (cols : Fin r ↪ σ) (h : MvPolynomial σ R),
      h ∉ q.comap (Ideal.Quotient.mk I) ∧
      Matrix.det (Matrix.of fun i j => pderiv (cols j) (F (rows i))) ∉
        q.comap (Ideal.Quotient.mk I) ∧
      ∀ f ∈ I, h * f ∈ Ideal.span (Set.range fun i => F (rows i)) := by
  classical
  let B := MvPolynomial σ R ⧸ I
  let J := q.comap (Ideal.Quotient.mk I)
  let K := J.ResidueField
  let L := Localization.AtPrime q
  have hIJ : I ≤ J := by
    intro x hx
    change Ideal.Quotient.mk I x ∈ q
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact q.zero_mem
  let f : B →+* K := Ideal.Quotient.lift I (algebraMap (MvPolynomial σ R) K)
    (fun x hx => Ideal.algebraMap_residueField_eq_zero.mpr (hIJ hx))
  let : Algebra B K := f.toAlgebra
  have hpoly : (algebraMap B K).comp (algebraMap (MvPolynomial σ R) B) =
      algebraMap (MvPolynomial σ R) K := by
    apply RingHom.ext
    intro x
    rfl
  let : IsScalarTower (MvPolynomial σ R) B K := .of_algebraMap_eq' hpoly.symm
  let : IsScalarTower R B K := .to₁₃₄ R (MvPolynomial σ R) B K
  have hfker : RingHom.ker f = q := by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change algebraMap (MvPolynomial σ R) K a = 0 ↔ Ideal.Quotient.mk I a ∈ q
    exact Ideal.algebraMap_residueField_eq_zero
  have hunits (s : q.primeCompl) : IsUnit (f s) := by
    apply isUnit_iff_ne_zero.mpr
    intro hs
    have hs' : (s : B) ∈ RingHom.ker f := hs
    exact s.property (Eq.mp (congrArg (fun J : Ideal B => (s : B) ∈ J) hfker) hs')
  let : SMul B L := Algebra.toSMul
  let : Module B L := Algebra.toModule
  let : MulAction B L := Algebra.toModule.toDistribMulAction.toMulAction
  let l : L →+* K := IsLocalization.lift hunits
  let : Algebra L K := l.toAlgebra
  let : IsScalarTower B L K := .of_algebraMap_eq' (IsLocalization.lift_comp hunits).symm
  let G : Algebra.Generators R B σ := Algebra.Generators.naive
  have hker : G.ker = I := Algebra.Generators.ker_naive _ _
  let P : Algebra.Presentation R B σ ι :=
    { G with relation := F, span_range_relation_eq_ker := hF.trans hker.symm }
  obtain ⟨r, rows, cols, hspan, hdet⟩ :=
    P.exists_selected_relations_of_cotangent_injective (K := K)
      (P.toGenerators.cotangentComplex_baseChange_injective_of_formallySmooth_localization_tower
        (L := L) q.primeCompl)
  let v : Fin r → P.ker := fun i => ⟨F (rows i), P.relation_mem_ker (rows i)⟩
  have htransport := @Algebra.Extension.span_kernel_tmul_eq_top_iff
    R B K (Fin r) _ _ _ _ P.toExtension
    (inferInstance : Algebra B K)
    (inferInstance : Algebra (MvPolynomial σ R) K)
    (inferInstance : IsScalarTower (MvPolynomial σ R) B K) v
  have hspan' : Submodule.span K (Set.range fun i =>
      (1 : K) ⊗ₜ[MvPolynomial σ R] v i) = ⊤ := htransport.mpr hspan
  let e : P.ker ≃ₗ[MvPolynomial σ R] I := LinearEquiv.ofEq _ _ hker
  let eK : K ⊗[MvPolynomial σ R] P.ker ≃ₗ[K] K ⊗[MvPolynomial σ R] I :=
    e.baseChange (MvPolynomial σ R) K _ _
  let w : Fin r → I := fun i => e (v i)
  have hspanq : Submodule.span K (Set.range fun i =>
      (1 : K) ⊗ₜ[MvPolynomial σ R] w i) = ⊤ := by
    have hm := congrArg (Submodule.map eK.toLinearMap) hspan'
    rw [Submodule.map_span, ← Set.range_comp', Submodule.map_top,
      LinearMap.range_eq_top.mpr eK.surjective] at hm
    simpa only [Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.baseChange_tmul, eK, w] using hm
  obtain ⟨h, hh, hmul⟩ := I.exists_notMem_mul_mem_span_of_residue_span_at J w hspanq
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
