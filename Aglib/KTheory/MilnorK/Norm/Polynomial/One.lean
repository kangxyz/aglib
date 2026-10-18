/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.Split
public import Mathlib.RingTheory.Norm.Transitivity

/-!
# Degree-one polynomial norms and ordinary field norms

The actual linear branches of a split polynomial are identified with all
coefficient-field embeddings of its root field. The split Milnor norm formula
in degree one therefore agrees with the determinant field norm. Injectivity
of the original coefficient map on units descends that equality. The
all-degree projection formula then gives the ordinary norm formula for mixed
classes. Characteristic zero is retained from polynomial base change.

No generation of arbitrary higher-degree classes by mixed classes is asserted,
and no independence or tower law for higher-degree finite-extension norms is
assumed.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

/-- The existing split branch map, with its actual coefficient compatibility
recorded as an algebra homomorphism. -/
def splitBranchAlgHom (p : MonicIrreducible k) (hp : (p.val.map (algebraMap k L)).Splits)
    (q : {q // q ∈ placesAbove (algebraMap k L) p}) : AdjoinRoot p.val →ₐ[k] L :=
  { MilnorK.K3.PolynomialNorm.splitBranchMap (algebraMap k L) p hp q with
    commutes' := MilnorK.K3.PolynomialNorm.splitBranchMap_algebraMap
      (algebraMap k L) p hp q }

/-- Distinct literal polynomial branches give distinct algebra embeddings. -/
theorem splitBranchAlgHom_injective (p : MonicIrreducible k)
    (hp : (p.val.map (algebraMap k L)).Splits) :
    Function.Injective (splitBranchAlgHom p hp) := by
  intro q r h
  apply MilnorK.K3.PolynomialNorm.splitBranchMap_injective_index (algebraMap k L) p hp
  exact congrArg AlgHom.toRingHom h

/-- Every coefficient-field embedding is the actual branch defined by the
image of the distinguished root. No branch or embedding is omitted. -/
theorem splitBranchAlgHom_surjective (p : MonicIrreducible k)
    (hp : (p.val.map (algebraMap k L)).Splits) :
    Function.Surjective (splitBranchAlgHom p hp) := by
  intro σ
  let b := σ (AdjoinRoot.root p.val)
  let q : MonicIrreducible L := ⟨X - C b, monic_X_sub_C b, irreducible_X_sub_C b⟩
  have hdiv : q.val ∣ p.val.map (algebraMap k L) := by
    apply dvd_iff_isRoot.mpr
    change (p.val.map (algebraMap k L)).eval b = 0
    rw [Polynomial.eval_map]
    exact AdjoinRoot.aeval_algHom_eq_zero p.val σ
  let q' : {q // q ∈ placesAbove (algebraMap k L) p} :=
    ⟨q, (mem_placesAbove (algebraMap k L) p q).mpr hdiv⟩
  refine ⟨q', ?_⟩
  apply AdjoinRoot.algHom_ext
  change MilnorK.K3.PolynomialNorm.splitBranchMap (algebraMap k L) p hp q'
    (AdjoinRoot.root p.val) = b
  have hr := MilnorK.K3.PolynomialNorm.splitBranchMap_root (algebraMap k L) p hp q'
  exact hr.trans (by simp [q', q])

open scoped Classical in
/-- The ordinary norm is the product over exactly the same actual linear
branches used by the polynomial Milnor norm after algebraically closed extension. -/
theorem normUnits_eq_prod_splitBranches [CharZero k] [IsAlgClosed L]
    (p : MonicIrreducible k) (a : (AdjoinRoot p.val)ˣ) :
    Units.map (algebraMap k L).toMonoidHom (Units.map (Algebra.norm k) a) =
      ∏ q : {q // q ∈ placesAbove (algebraMap k L) p},
        Units.map (splitBranchAlgHom p (IsAlgClosed.splits _) q).toMonoidHom a := by
  classical
  let : Module.Finite k (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot
  apply Units.ext
  change algebraMap k L (Algebra.norm k (a : AdjoinRoot p.val)) = _
  rw [Units.coe_prod]
  change algebraMap k L (Algebra.norm k (a : AdjoinRoot p.val)) =
    ∏ q : {q // q ∈ placesAbove (algebraMap k L) p},
      splitBranchAlgHom p (IsAlgClosed.splits _) q (a : AdjoinRoot p.val)
  rw [Algebra.norm_eq_prod_embeddings k L]
  symm
  apply Fintype.prod_equiv (Equiv.ofBijective (splitBranchAlgHom p (IsAlgClosed.splits _))
    ⟨splitBranchAlgHom_injective p _, splitBranchAlgHom_surjective p _⟩)
  intro q
  rfl

/-- The actual degree-one polynomial Milnor norm is the ordinary determinant
field norm on units, on every class of the original degree-one quotient. -/
theorem oneEquiv_polynomialNorm [CharZero k] (p : MonicIrreducible k)
    (z : K (AdjoinRoot p.val) 1) :
    oneEquiv k (polynomialNorm 1 p z) =
      Additive.ofMul (Units.map (Algebra.norm k) (oneEquiv (AdjoinRoot p.val) z).toMul) := by
  classical
  let E := AlgebraicClosure k
  change (oneEquiv k (polynomialNorm 1 p z)).toMul = _
  apply Units.map_injective (f := (algebraMap k E).toMonoidHom) (algebraMap k E).injective
  have h := congrArg (fun y : K E 1 => (oneEquiv E y).toMul)
    (polynomialNorm_restrict_of_splits (algebraMap k E) 1 p (IsAlgClosed.splits _) z)
  simp only [map_sum, oneEquiv_map, toMul_ofMul, toMul_sum,
    Finset.attach_eq_univ] at h
  exact h.trans (normUnits_eq_prod_splitBranches (L := E) p
    (oneEquiv (AdjoinRoot p.val) z).toMul).symm

/-- Equivalently, the inverse degree-one comparison carries the actual field
norm to the constructed polynomial Milnor norm. -/
theorem polynomialNorm_unitsToOne [CharZero k] (p : MonicIrreducible k)
    (a : Additive (AdjoinRoot p.val)ˣ) :
    polynomialNorm 1 p ((oneEquiv (AdjoinRoot p.val)).symm a) =
      (oneEquiv k).symm (Additive.ofMul (Units.map (Algebra.norm k) a.toMul)) := by
  apply (oneEquiv k).injective
  simp only [oneEquiv_polynomialNorm, LinearEquiv.apply_symm_apply]

/-- In degree one the polynomial norm is independent of the presentation:
every actual base-field algebra equivalence intertwines the two norms. -/
theorem polynomialNorm_one_map_algEquiv [CharZero k]
    (p q : MonicIrreducible k) (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val)
    (z : K (AdjoinRoot p.val) 1) :
    polynomialNorm 1 q (MilnorK.map 1 e.toRingHom z) = polynomialNorm 1 p z := by
  apply (oneEquiv k).injective
  rw [oneEquiv_polynomialNorm, oneEquiv_polynomialNorm, oneEquiv_map]
  congr 1
  apply Units.ext
  exact Algebra.norm_eq_of_algEquiv e (oneEquiv (AdjoinRoot p.val) z).toMul

/-- In every degree, a base-field class times one extension unit has norm
obtained by applying the ordinary field norm to that final unit. No mixed
symbol generation is assumed. -/
theorem polynomialNorm_productUnit_constants [CharZero k] (m : ℕ)
    (p : MonicIrreducible k) (x : K k m) (a : Additive (AdjoinRoot p.val)ˣ) :
    polynomialNorm (m + 1) p
        (productUnit m (MilnorK.map m (algebraMap k (AdjoinRoot p.val)) x) a) =
      productUnit m x (Additive.ofMul (Units.map (Algebra.norm k) a.toMul)) := by
  change polynomialNorm (m + 1) p
    (product m 1 (MilnorK.map m (algebraMap k (AdjoinRoot p.val)) x)
      ((oneEquiv (AdjoinRoot p.val)).symm a)) = _
  rw [polynomialNorm_product_constants_left, polynomialNorm_unitsToOne]
  rfl

/-- The mixed-symbol version keeps every base coordinate and replaces only
the final extension coordinate by its actual field norm. -/
theorem polynomialNorm_symbol_constants_unit [CharZero k] (m : ℕ)
    (p : MonicIrreducible k) (a : SymbolTuple k m) (b : (AdjoinRoot p.val)ˣ) :
    polynomialNorm (m + 1) p
      (symbol (Fin.snoc (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom ∘ a) b)) =
        symbol (Fin.snoc a (Units.map (Algebra.norm k) b)) := by
  simpa only [MilnorK.map_symbol, productUnit_symbol, toMul_ofMul] using
    polynomialNorm_productUnit_constants m p (symbol a) (Additive.ofMul b)

end MilnorK.PolynomialNorm
