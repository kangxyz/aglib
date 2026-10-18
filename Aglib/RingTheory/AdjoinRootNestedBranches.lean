/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdjoinRootPiBranches
public import Aglib.RingTheory.AdjoinRootNestedBaseChange

/-!
# All direct and nested scalar branches in an actual root-field tower

The direct scalar branches of the original upper presentation are matched
with all pairs of lower scalar branches and relative upper scalar branches.
Every matched residue equivalence retains both original field maps.
-/

@[expose] public noncomputable section

open Polynomial Polynomial.LocalResidue
open scoped TensorProduct

namespace AdjoinRoot

variable {k S E : Type*} [Field k] [CharZero k] [Field S] [Algebra k S]
  [Field E] [Algebra k E] (p h : k[X]) (hp : p.Monic)
  [Fact (Irreducible p)] [Fact (Irreducible h)]
  [Algebra (AdjoinRoot p) E] [IsScalarTower k (AdjoinRoot p) E]
  (q : (AdjoinRoot p)[X]) [Fact (Irreducible q)]
  (η : AdjoinRoot h ≃ₐ[k] E) (ε : AdjoinRoot q ≃ₐ[AdjoinRoot p] E)

local notation "PRoot" => AdjoinRoot p
local notation "pS" => p.map (algebraMap k S)
local notation "hS" => h.map (algebraMap k S)

attribute [local instance] scalarBranchAlgebra

/-- Each actual upper tensor factor is the original relative polynomial
presentation after extension to the chosen lower branch. -/
def nestedScalarFactorEquiv (r : IrreducibleBranch pS) :
    E ⊗[PRoot] AdjoinRoot r.val.val ≃+*
      AdjoinRoot (q.map (algebraMap PRoot (AdjoinRoot r.val.val))) :=
  (Algebra.TensorProduct.comm PRoot E (AdjoinRoot r.val.val)).toRingEquiv.trans
    (((Algebra.TensorProduct.congr
      (AlgEquiv.refl : AdjoinRoot r.val.val ≃ₐ[AdjoinRoot r.val.val] AdjoinRoot r.val.val)
      ε.symm).trans (scalarExtensionEquiv (L := AdjoinRoot r.val.val) q)).toRingEquiv)

omit [CharZero k] [Algebra k E] [IsScalarTower k PRoot E] in
/-- The old upper-field component is the literal relative scalar map. -/
theorem nestedScalarFactorEquiv_tmul_one (r : IrreducibleBranch pS) (a : E) :
    nestedScalarFactorEquiv p q ε r (a ⊗ₜ[PRoot] (1 : AdjoinRoot r.val.val)) =
      scalarMap (algebraMap PRoot (AdjoinRoot r.val.val)) q (ε.symm a) := by
  change scalarExtensionEquiv (L := AdjoinRoot r.val.val) q
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : AdjoinRoot r.val.val ≃ₐ[AdjoinRoot r.val.val] AdjoinRoot r.val.val)
      ε.symm ((Algebra.TensorProduct.comm PRoot E (AdjoinRoot r.val.val))
        (a ⊗ₜ[PRoot] (1 : AdjoinRoot r.val.val)))) = _
  rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]
  exact RingHom.congr_fun
    (scalarExtensionEquiv_comp_includeRight (L := AdjoinRoot r.val.val) q) (ε.symm a)

omit [CharZero k] [Algebra k E] [IsScalarTower k PRoot E] in
/-- The chosen lower-branch coefficient is unchanged in the relative presentation. -/
theorem nestedScalarFactorEquiv_one_tmul (r : IrreducibleBranch pS)
    (b : AdjoinRoot r.val.val) :
    nestedScalarFactorEquiv p q ε r ((1 : E) ⊗ₜ[PRoot] b) =
      algebraMap (AdjoinRoot r.val.val)
        (AdjoinRoot (q.map (algebraMap PRoot (AdjoinRoot r.val.val)))) b := by
  change scalarExtensionEquiv (L := AdjoinRoot r.val.val) q
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : AdjoinRoot r.val.val ≃ₐ[AdjoinRoot r.val.val] AdjoinRoot r.val.val)
      ε.symm ((Algebra.TensorProduct.comm PRoot E (AdjoinRoot r.val.val))
        ((1 : E) ⊗ₜ[PRoot] b))) = _
  rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]
  change scalarExtensionEquiv (L := AdjoinRoot r.val.val) q
    (b ⊗ₜ[PRoot] ε.symm 1) = _
  rw [map_one]
  exact (scalarExtensionEquiv (L := AdjoinRoot r.val.val) q).commutes b

/-- The direct scalar algebra is the product of every actual relative
scalar polynomial algebra, with no branches selected or removed. -/
def nestedPolynomialProductEquiv :
    AdjoinRoot hS ≃+* ∀ r : IrreducibleBranch pS,
      AdjoinRoot (q.map (algebraMap PRoot (AdjoinRoot r.val.val))) :=
  (scalarExtensionEquiv (L := S) h).symm.toRingEquiv.trans
    (((Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) η).toRingEquiv).trans
      ((Algebra.TensorProduct.comm k S E).toRingEquiv.trans
        ((nestedScalarProductEquiv (S := S) p hp E).toRingEquiv.trans
          (RingEquiv.piCongrRight fun r => nestedScalarFactorEquiv p q ε r))))

/-- The actual original upper-field map becomes the actual relative scalar
map in every lower-branch coordinate. -/
theorem nestedPolynomialProductEquiv_scalarMap (r : IrreducibleBranch pS) (a : E) :
    nestedPolynomialProductEquiv p h hp q η ε
      (scalarMap (algebraMap k S) h (η.symm a)) r =
      scalarMap (algebraMap PRoot (AdjoinRoot r.val.val)) q (ε.symm a) := by
  have ha : (scalarExtensionEquiv (L := S) h).symm
      (scalarMap (algebraMap k S) h (η.symm a)) = (1 : S) ⊗ₜ[k] η.symm a := by
    apply (scalarExtensionEquiv (L := S) h).injective
    rw [AlgEquiv.apply_symm_apply]
    exact (RingHom.congr_fun
      (scalarExtensionEquiv_comp_includeRight (L := S) h) (η.symm a)).symm
  change nestedScalarFactorEquiv p q ε r
    (nestedScalarProductEquiv (S := S) p hp E
      (Algebra.TensorProduct.comm k S E
        (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) η
          ((scalarExtensionEquiv (L := S) h).symm
            (scalarMap (algebraMap k S) h (η.symm a))))) r) = _
  rw [ha, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  change nestedScalarFactorEquiv p q ε r
    (nestedScalarProductEquiv (S := S) p hp E
      (Algebra.TensorProduct.comm k S E ((1 : S) ⊗ₜ[k] η (η.symm a))) r) = _
  rw [AlgEquiv.apply_symm_apply, Algebra.TensorProduct.comm_tmul,
    nestedScalarProductEquiv_tmul, map_one, nestedScalarFactorEquiv_tmul_one]

/-- The original scalar field follows its native two-step coefficient map
in every lower-branch coordinate. -/
theorem nestedPolynomialProductEquiv_algebraMap (r : IrreducibleBranch pS) (b : S) :
    nestedPolynomialProductEquiv p h hp q η ε
      (algebraMap S (AdjoinRoot hS) b) r =
      algebraMap (AdjoinRoot r.val.val)
        (AdjoinRoot (q.map (algebraMap PRoot (AdjoinRoot r.val.val))))
          (algebraMap S (AdjoinRoot r.val.val) b) := by
  have hb : (scalarExtensionEquiv (L := S) h).symm
      (algebraMap S (AdjoinRoot hS) b) = b ⊗ₜ[k] (1 : AdjoinRoot h) := by
    apply (scalarExtensionEquiv (L := S) h).injective
    rw [AlgEquiv.apply_symm_apply]
    exact ((scalarExtensionEquiv (L := S) h).commutes b).symm
  change nestedScalarFactorEquiv p q ε r
    (nestedScalarProductEquiv (S := S) p hp E
      (Algebra.TensorProduct.comm k S E
        (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) η
          ((scalarExtensionEquiv (L := S) h).symm
            (algebraMap S (AdjoinRoot hS) b)))) r) = _
  rw [hb, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  change nestedScalarFactorEquiv p q ε r
    (nestedScalarProductEquiv (S := S) p hp E
      (Algebra.TensorProduct.comm k S E (b ⊗ₜ[k] η 1)) r) = _
  rw [map_one, Algebra.TensorProduct.comm_tmul, nestedScalarProductEquiv_tmul,
    nestedScalarFactorEquiv_one_tmul]

/-- The complete nested product equivalence preserves the original scalar
field with its native coefficient algebra on each polynomial quotient. -/
def nestedPolynomialProductAlgEquiv :
    AdjoinRoot hS ≃ₐ[S] ∀ r : IrreducibleBranch pS,
      AdjoinRoot (q.map (algebraMap PRoot (AdjoinRoot r.val.val))) :=
  { nestedPolynomialProductEquiv p h hp q η ε with
    commutes' b := by
      funext r
      exact nestedPolynomialProductEquiv_algebraMap p h hp q η ε r b }

/-- A nested branch is an actual lower scalar branch together with an
actual branch of the relative upper polynomial over its residue field. -/
abbrev NestedScalarBranch :=
  Σ r : IrreducibleBranch pS,
    IrreducibleBranch (q.map (algebraMap PRoot (AdjoinRoot r.val.val)))

/-- All nested branch pairs are in bijection with all direct upper branches. -/
def nestedBranchEquiv :
    NestedScalarBranch (S := S) p q ≃ IrreducibleBranch hS := by
  let : Finite (IrreducibleBranch pS) := finite_irreducibleBranch pS (hp.map _)
  exact piBranchEquiv (fun r : IrreducibleBranch pS => AdjoinRoot r.val.val)
    hS (Polynomial.map_ne_zero (Fact.out : Irreducible h).ne_zero)
    (fun r => q.map (algebraMap PRoot (AdjoinRoot r.val.val)))
    (fun _ => Polynomial.map_ne_zero (Fact.out : Irreducible q).ne_zero)
    (nestedPolynomialProductEquiv p h hp q η ε)

/-- The literal matched branch fields are equivalent over the original
scalar field, using its native two-step algebra on the nested branch. -/
def nestedBranchAlgEquiv (u : NestedScalarBranch (S := S) p q) :
    AdjoinRoot (nestedBranchEquiv p h hp q η ε u).val.val ≃ₐ[S]
      AdjoinRoot u.2.val.val := by
  let : Finite (IrreducibleBranch pS) := finite_irreducibleBranch pS (hp.map _)
  exact piBranchAlgEquiv (fun r : IrreducibleBranch pS => AdjoinRoot r.val.val)
    hS (Polynomial.map_ne_zero (Fact.out : Irreducible h).ne_zero)
    (fun r => q.map (algebraMap PRoot (AdjoinRoot r.val.val)))
    (fun _ => Polynomial.map_ne_zero (Fact.out : Irreducible q).ne_zero)
    (nestedPolynomialProductAlgEquiv p h hp q η ε) u

/-- The matched residue equivalence preserves the entire original quotient square. -/
theorem nestedBranchAlgEquiv_divisorMap (u : NestedScalarBranch (S := S) p q)
    (x : AdjoinRoot hS) :
    nestedBranchAlgEquiv p h hp q η ε u
      (divisorMap hS (nestedBranchEquiv p h hp q η ε u).val.val
        (nestedBranchEquiv p h hp q η ε u).property x) =
      divisorMap (q.map (algebraMap PRoot (AdjoinRoot u.1.val.val)))
        u.2.val.val u.2.property (nestedPolynomialProductEquiv p h hp q η ε x u.1) := by
  let : Finite (IrreducibleBranch pS) := finite_irreducibleBranch pS (hp.map _)
  exact piBranchRingEquiv_divisorMap
    (fun r : IrreducibleBranch pS => AdjoinRoot r.val.val)
    hS (Polynomial.map_ne_zero (Fact.out : Irreducible h).ne_zero)
    (fun r => q.map (algebraMap PRoot (AdjoinRoot r.val.val)))
    (fun _ => Polynomial.map_ne_zero (Fact.out : Irreducible q).ne_zero)
    (nestedPolynomialProductEquiv p h hp q η ε) u x

/-- Both original presentations give exactly the same map from E into
each matched residue field, after the constructed branch equivalence. -/
theorem nestedBranchAlgEquiv_adjoinRootMap (u : NestedScalarBranch (S := S) p q)
    (a : E) :
    nestedBranchAlgEquiv p h hp q η ε u
      (adjoinRootMap (algebraMap k S) h (nestedBranchEquiv p h hp q η ε u).val.val
        (nestedBranchEquiv p h hp q η ε u).property (η.symm a)) =
      adjoinRootMap (algebraMap PRoot (AdjoinRoot u.1.val.val)) q
        u.2.val.val u.2.property (ε.symm a) := by
  calc
    _ = nestedBranchAlgEquiv p h hp q η ε u
        (divisorMap hS (nestedBranchEquiv p h hp q η ε u).val.val
          (nestedBranchEquiv p h hp q η ε u).property
          (scalarMap (algebraMap k S) h (η.symm a))) :=
      congrArg (nestedBranchAlgEquiv p h hp q η ε u)
        (RingHom.congr_fun
          (divisorMap_comp_scalarMap (algebraMap k S) h
            (nestedBranchEquiv p h hp q η ε u).val.val
            (nestedBranchEquiv p h hp q η ε u).property).symm (η.symm a))
    _ = divisorMap (q.map (algebraMap PRoot (AdjoinRoot u.1.val.val)))
        u.2.val.val u.2.property
          (nestedPolynomialProductEquiv p h hp q η ε
            (scalarMap (algebraMap k S) h (η.symm a)) u.1) :=
      nestedBranchAlgEquiv_divisorMap p h hp q η ε u _
    _ = divisorMap (q.map (algebraMap PRoot (AdjoinRoot u.1.val.val)))
        u.2.val.val u.2.property
          (scalarMap (algebraMap PRoot (AdjoinRoot u.1.val.val)) q (ε.symm a)) :=
      congrArg (divisorMap _ u.2.val.val u.2.property)
        (nestedPolynomialProductEquiv_scalarMap p h hp q η ε u.1 a)
    _ = _ := RingHom.congr_fun
      (divisorMap_comp_scalarMap (algebraMap PRoot (AdjoinRoot u.1.val.val)) q
        u.2.val.val u.2.property) (ε.symm a)

/-- The equality of the full original E-valued field maps, in compositional form. -/
theorem nestedBranchAlgEquiv_comp_originalMap (u : NestedScalarBranch (S := S) p q) :
    (nestedBranchAlgEquiv p h hp q η ε u).toRingHom.comp
      ((adjoinRootMap (algebraMap k S) h (nestedBranchEquiv p h hp q η ε u).val.val
        (nestedBranchEquiv p h hp q η ε u).property).comp η.symm.toRingHom) =
      (adjoinRootMap (algebraMap PRoot (AdjoinRoot u.1.val.val)) q
        u.2.val.val u.2.property).comp ε.symm.toRingHom := by
  apply RingHom.ext
  intro a
  exact nestedBranchAlgEquiv_adjoinRootMap p h hp q η ε u a

end AdjoinRoot
