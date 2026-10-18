/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.FiniteComparison

/-!
# The literal root-field square in coprime scalar extension

For a commuting field square, coprime degrees keep the coefficient polynomial
irreducible. Equality of the actual target degree identifies its root field with
the target field, preserving the original maps. Singleton polynomial norm base
change then gives the transported norm square. The degree hypothesis is explicit;
there is no assumed norm compatibility or identification of unspecified branches.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue AdjoinRoot

variable {k L A B : Type*} [Field k] [Field L] [Field A] [Field B]
  [Algebra k L] [Module.Finite k L] [Algebra k A]
  [Algebra L B] [Algebra A B] [Algebra k B]
  [IsScalarTower k L B] [IsScalarTower k A B]

/-- The actual whole coefficient image, irreducible by coprimality. -/
def coprimeCoefficientPolynomial (q : MonicIrreducible k)
    (hcop : q.val.natDegree.Coprime (Module.finrank k L)) : MonicIrreducible L :=
  ⟨q.val.map (algebraMap k L), q.property.1.map _,
    q.property.1.irreducible_map_of_natDegree_coprime q.property.2 hcop⟩

/-- Evaluate the coefficient-image root at the literal image of the old root. -/
def coprimeRootAlgHom (q : MonicIrreducible k)
    (hcop : q.val.natDegree.Coprime (Module.finrank k L))
    (ε : AdjoinRoot q.val ≃ₐ[k] A) :
    AdjoinRoot (coprimeCoefficientPolynomial q hcop).val →ₐ[L] B :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId L B)
    (algebraMap A B (ε (AdjoinRoot.root q.val))) (by
      change aeval _ (q.val.map (algebraMap k L)) = 0
      rw [aeval_map_algebraMap]
      exact AdjoinRoot.aeval_algHom_eq_zero q.val
        ((IsScalarTower.toAlgHom k A B).comp ε.toAlgHom))

/-- The new root map preserves every original root-field element. -/
theorem coprimeRootAlgHom_coefficientMap (q : MonicIrreducible k)
    (hcop : q.val.natDegree.Coprime (Module.finrank k L))
    (ε : AdjoinRoot q.val ≃ₐ[k] A) (x : AdjoinRoot q.val) :
    coprimeRootAlgHom (B := B) q hcop ε (AdjoinRoot.coefficientMap q.val x) =
      algebraMap A B (ε x) := by
  have h : ((coprimeRootAlgHom (B := B) q hcop ε).restrictScalars k).comp
      (AdjoinRoot.coefficientMap q.val) =
      (IsScalarTower.toAlgHom k A B).comp ε.toAlgHom := by
    apply AdjoinRoot.algHom_ext
    change coprimeRootAlgHom (B := B) q hcop ε
      (AdjoinRoot.coefficientMap q.val (AdjoinRoot.root q.val)) = _
    rw [coefficientMap_root]
    exact liftAlgHom_root _ _ _ _
  exact AlgHom.congr_fun h x

/-- Equal actual target degree turns the literal root map into an equivalence. -/
def coprimeRootAlgEquiv [Module.Finite L B] (q : MonicIrreducible k)
    (hcop : q.val.natDegree.Coprime (Module.finrank k L))
    (ε : AdjoinRoot q.val ≃ₐ[k] A) (hdegree : Module.finrank L B = q.val.natDegree) :
    AdjoinRoot (coprimeCoefficientPolynomial q hcop).val ≃ₐ[L] B := by
  let q' := coprimeCoefficientPolynomial q hcop
  let : Module.Finite L (AdjoinRoot q'.val) := q'.property.1.finite_adjoinRoot
  let f := coprimeRootAlgHom (B := B) q hcop ε
  apply AlgEquiv.ofBijective f
  refine ⟨f.injective, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := f.toLinearMap) ?_).mp f.injective
  rw [(AdjoinRoot.powerBasis q'.property.2.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
  exact (Polynomial.natDegree_map _).trans hdegree.symm

/-- The inverse equivalence preserves the original field restriction literally. -/
theorem coprimeRootAlgEquiv_symm_comp [Module.Finite L B] (q : MonicIrreducible k)
    (hcop : q.val.natDegree.Coprime (Module.finrank k L))
    (ε : AdjoinRoot q.val ≃ₐ[k] A) (hdegree : Module.finrank L B = q.val.natDegree) :
    (coprimeRootAlgEquiv q hcop ε hdegree).symm.toRingHom.comp (algebraMap A B) =
      (AdjoinRoot.coefficientMap (L := L) q.val).toRingHom.comp ε.symm.toRingHom := by
  ext a
  apply (coprimeRootAlgEquiv q hcop ε hdegree).injective
  change coprimeRootAlgEquiv q hcop ε hdegree
      ((coprimeRootAlgEquiv q hcop ε hdegree).symm (algebraMap A B a)) = _
  rw [AlgEquiv.apply_symm_apply]
  change algebraMap A B a =
    coprimeRootAlgHom (B := B) q hcop ε (AdjoinRoot.coefficientMap q.val (ε.symm a))
  rw [coprimeRootAlgHom_coefficientMap, ε.apply_symm_apply]

/-- Singleton base change with the actual old and new root-field equivalences.
No equality between norms of distinct presentations is assumed. -/
theorem polynomialNorm_coprime_root_square [CharZero k] [Module.Finite L B]
    (n : ℕ) (q : MonicIrreducible k)
    (hcop : q.val.natDegree.Coprime (Module.finrank k L))
    (ε : AdjoinRoot q.val ≃ₐ[k] A) (hdegree : Module.finrank L B = q.val.natDegree)
    (x : K A n) :
    map n (algebraMap k L) (polynomialNorm n q (map n ε.symm.toRingHom x)) =
      polynomialNorm n (coprimeCoefficientPolynomial q hcop)
        (map n (coprimeRootAlgEquiv q hcop ε hdegree).symm.toRingHom
          (map n (algebraMap A B) x)) := by
  rw [polynomialNorm_restrict_irreducible (algebraMap k L) n q
    (coprimeCoefficientPolynomial q hcop) rfl]
  congr 1
  let : Fact (Irreducible (q.val.map (algebraMap k L))) :=
    ⟨q.property.1.irreducible_map_of_natDegree_coprime q.property.2 hcop⟩
  change map n (adjoinRootMap (algebraMap k L) q.val
    (q.val.map (algebraMap k L)) dvd_rfl) (map n ε.symm.toRingHom x) = _
  rw [adjoinRootMap_eq_coefficientMap]
  rw [← LinearMap.comp_apply, ← map_comp, ← LinearMap.comp_apply, ← map_comp,
    coprimeRootAlgEquiv_symm_comp]
  rfl

end MilnorK.PolynomialNorm
