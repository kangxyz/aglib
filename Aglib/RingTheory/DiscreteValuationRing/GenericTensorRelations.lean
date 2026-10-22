/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.GenericTensorGenerators
public import Aglib.RingTheory.DiscreteValuationRing.GenericTargetSquare
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.Tower

/-! # Transporting the original selected relations to the generic tensor source

Coefficient change transports the original relations to the literal source tensor
ring. Evaluation and differentiation commute with this transport and with the
actual target tensor map. Consequently the generic retained-minor theorem applies
to the original evaluated relation matrix, without choosing another relation
family or another coordinate matrix.
-/

@[expose] public noncomputable section

open MvPolynomial
open scoped TensorProduct

namespace GenericParameterCentre

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section Source

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {B : Type*} [CommRing B] [Algebra R B] {n : Type*}
  (p : R) [Fact (Irreducible p)]

local notation "R₁" => ParameterLocalization.Ring R (n × n) p

/-- Coefficient change and the actual tensor generators give the canonical
polynomial evaluation square, with the right scalar action on the tensor ring. -/
theorem tensorGenerators_aeval_map (P : Algebra.Generators R B n)
    (q : MvPolynomial n R) :
    aeval (tensorGenerators R p P).val (MvPolynomial.map (algebraMap R R₁) q) =
      (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] R₁) (aeval P.val q) := by
  rw [MvPolynomial.aeval_map_algebraMap]
  have hv : (tensorGenerators R p P).val =
      fun i => (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] R₁) (P.val i) :=
    funext (tensorGenerators_val R p P)
  rw [hv]
  exact (MvPolynomial.comp_aeval_apply (f := P.val)
    (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] R₁) q).symm

/-- An original relation stays a relation after the literal coefficient map. -/
theorem map_mem_tensorGenerators_ker (P : Algebra.Generators R B n)
    {q : MvPolynomial n R} (hq : q ∈ P.ker) :
    MvPolynomial.map (algebraMap R R₁) q ∈ (tensorGenerators R p P).ker := by
  rw [Algebra.Generators.ker_eq_ker_aeval_val, RingHom.mem_ker]
  rw [tensorGenerators_aeval_map, Algebra.Generators.aeval_val_eq_zero hq, map_zero]

/-- Transport a selected relation itself, retaining its original polynomial. -/
def tensorRelation (P : Algebra.Generators R B n) (f : P.ker) :
    (tensorGenerators R p P).ker :=
  ⟨MvPolynomial.map (algebraMap R R₁) (f : MvPolynomial n R),
    map_mem_tensorGenerators_ker R p P f.property⟩

@[simp] theorem tensorRelation_coe (P : Algebra.Generators R B n) (f : P.ker) :
    (tensorRelation R p P f : MvPolynomial n R₁) =
      MvPolynomial.map (algebraMap R R₁) (f : MvPolynomial n R) := rfl

end Source

section TargetAlgebra

variable (R S ι : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [Finite ι] (p : R) [Fact (Irreducible p)]
  [Fact (Irreducible (algebraMap R S p))]
  {B : Type*} [CommRing B] [Algebra R B] (χ : B →ₐ[R] S)

local notation "R₁" => ParameterLocalization.Ring R ι p
local notation "S₁" => ParameterLocalization.Ring S ι (algebraMap R S p)

/-- The existing tensor target, rebundled over the actual parameter coefficient
map. This is the target algebra homomorphism used by retained-relation results. -/
def tensorTargetOverParameters :
    letI : Algebra R₁ S₁ := (ParameterLocalization.parameterMap R S ι p).toRingHom.toAlgebra
    (B ⊗[R] R₁) →ₐ[R₁] S₁ := by
  letI : Algebra R₁ S₁ := (ParameterLocalization.parameterMap R S ι p).toRingHom.toAlgebra
  refine { (tensorTarget R S ι p χ).toRingHom with commutes' := ?_ }
  intro a
  change tensorTarget R S ι p χ (1 ⊗ₜ[R] a) =
    ParameterLocalization.parameterMap R S ι p a
  rw [tensorTarget_tmul, map_one, map_one, one_mul]

/-- Rebundling changes no values and introduces no replacement target map. -/
@[simp] theorem tensorTargetOverParameters_apply (x : B ⊗[R] R₁) :
    tensorTargetOverParameters R S ι p χ x = tensorTarget R S ι p χ x := rfl

end TargetAlgebra

section Target

variable (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  {B : Type*} [CommRing B] [Algebra R B]
  {n : Type*} [Fintype n] [DecidableEq n]
  (p : R) [Fact (Irreducible p)]
  [Fact (Irreducible (algebraMap R S p))]

local notation "R₁" => ParameterLocalization.Ring R (n × n) p
local notation "S₁" => ParameterLocalization.Ring S (n × n) (algebraMap R S p)

omit [Fintype n] [DecidableEq n] in
/-- Evaluating a coefficient-changed polynomial and then applying the actual
tensor target is the original target evaluation followed by coefficient change. -/
theorem tensorTarget_aeval_map [Finite n] (P : Algebra.Generators R B n) (χ : B →ₐ[R] S)
    (q : MvPolynomial n R) :
    tensorTarget R S (n × n) p χ
      (aeval (tensorGenerators R p P).val (MvPolynomial.map (algebraMap R R₁) q)) =
        algebraMap S S₁ (χ (aeval P.val q)) := by
  rw [tensorGenerators_aeval_map, Algebra.TensorProduct.includeLeft_apply,
    tensorTarget_tmul, map_one, mul_one]

omit [Fintype n] [DecidableEq n] in
/-- The derivative square uses the original polynomial and the same coordinate
index; it is only coefficient transport, not a second chain-rule argument. -/
theorem tensorTarget_pderiv_map [Finite n] (P : Algebra.Generators R B n) (χ : B →ₐ[R] S)
    (q : MvPolynomial n R) (i : n) :
    tensorTarget R S (n × n) p χ
      (aeval (tensorGenerators R p P).val
        (pderiv i (MvPolynomial.map (algebraMap R R₁) q))) =
      algebraMap S S₁ (χ (aeval P.val (pderiv i q))) := by
  classical
  rw [MvPolynomial.pderiv_map, tensorTarget_aeval_map]

omit [Fintype n] [DecidableEq n] in
/-- Every entry of the transported relation-row Jacobian is the image of the
corresponding entry of the original evaluated Jacobian. -/
theorem tensorTarget_pderiv_map_matrix [Finite n] (P : Algebra.Generators R B n)
    (χ : B →ₐ[R] S) {m : Type*} (f : m → MvPolynomial n R) :
    (Matrix.of fun j i => tensorTarget R S (n × n) p χ
      (aeval (tensorGenerators R p P).val
        (pderiv i (MvPolynomial.map (algebraMap R R₁) (f j))))) =
      (Matrix.of fun j i => χ (aeval P.val (pderiv i (f j)))).map
        (algebraMap S S₁) := by
  ext j i
  exact tensorTarget_pderiv_map R S p P χ (f j) i

/-- The literal selected relation family has the normalized retained minor for
the SAME generic matrix. The principal-minor hypotheses concern the ORIGINAL
matrix over `S`, rather than a newly chosen matrix over the parameter DVR. -/
theorem exists_tensorRelation_retained_minor_unit (P : Algebra.Generators R B n)
    (χ : B →ₐ[R] S) {c : ℕ} (f : Fin c → P.ker)
    (δ : S) (hδ : δ ≠ 0)
    (hI : (Matrix.of fun j i => χ (aeval P.val
      (pderiv i (f j : MvPolynomial n R)))).minorIdeal c = Ideal.span {δ})
    (cols : Fin c → n)
    (hcols : ((Matrix.of fun j i => χ (aeval P.val
      (pderiv i (f j : MvPolynomial n R)))).submatrix _root_.id cols).det = δ)
    (b : Fin c ↪ n) :
    ∃ h : S₁, IsUnit h ∧
      ((Matrix.of (fun j i => tensorTarget R S (n × n) p χ
          (aeval (tensorGenerators R p P).val
            (pderiv i (tensorRelation R p P (f j) : MvPolynomial n R₁)))) *
        ((ParameterLocalization.parameterMap R S (n × n) p).toRingHom.mapMatrix
          (ParameterLocalization.genericMatrix R n p)).adjugate).submatrix
        _root_.id b).det = algebraMap S S₁ δ * h := by
  have hmatrix :
      (Matrix.of fun j i => tensorTarget R S (n × n) p χ
        (aeval (tensorGenerators R p P).val
          (pderiv i (tensorRelation R p P (f j) : MvPolynomial n R₁)))) =
        (Matrix.of fun j i => χ (aeval P.val
          (pderiv i (f j : MvPolynomial n R)))).map (algebraMap S S₁) := by
    simpa only [tensorRelation_coe] using
      tensorTarget_pderiv_map_matrix R S p P χ
        (fun j => (f j : MvPolynomial n R))
  have hmatrixU :
      (ParameterLocalization.parameterMap R S (n × n) p).toRingHom.mapMatrix
        (ParameterLocalization.genericMatrix R n p) =
          ParameterLocalization.genericMatrix S n (algebraMap R S p) := by
    exact ParameterLocalization.parameterMap_genericMatrix R n p S
  rw [hmatrix, hmatrixU]
  exact ParameterLocalization.exists_generic_retained_minor_unit S n (algebraMap R S p)
    (Matrix.of fun j i => χ (aeval P.val (pderiv i (f j : MvPolynomial n R))))
    δ hδ hI cols hcols b

end Target

end GenericParameterCentre
