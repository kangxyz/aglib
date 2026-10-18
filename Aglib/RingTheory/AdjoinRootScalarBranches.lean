/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.PolynomialResidueBaseChange
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Spectrum.Maximal.Basic

/-!
# Literal branches of a scalar-extended polynomial algebra

Monic irreducible divisors parametrize every maximal quotient of the whole
polynomial algebra. Each branch map is the original polynomial quotient map.
A squarefree polynomial has local length one at all of these branches; this
applies to every scalar extension of an irreducible characteristic-zero
polynomial. The branch maps compose with coefficient extension to give the
existing concrete polynomial residue-field map.
-/

@[expose] public noncomputable section

open Polynomial

namespace AdjoinRoot

variable {k L : Type*} [Field k] [Field L]

/-- A literal monic irreducible divisor of the whole polynomial. -/
abbrev IrreducibleBranch (p : k[X]) :=
  {q : {q : k[X] // q.Monic ∧ Irreducible q} // q.val ∣ p}

instance (p : k[X]) (q : IrreducibleBranch p) : Fact (Irreducible q.val.val) :=
  ⟨q.val.property.2⟩

/-- The actual quotient map associated with a polynomial divisor. -/
def divisorMap (p q : k[X]) (hq : q ∣ p) : AdjoinRoot p →+* AdjoinRoot q :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr hq)

@[simp]
theorem divisorMap_mk (p q : k[X]) (hq : q ∣ p) (a : k[X]) :
    divisorMap p q hq (mk p a) = mk q a := rfl

theorem divisorMap_surjective (p q : k[X]) (hq : q ∣ p) :
    Function.Surjective (divisorMap p q hq) :=
  Ideal.Quotient.factor_surjective _

/-- Each irreducible factor gives its literal maximal kernel. -/
def branchMaximal (p : k[X]) (q : IrreducibleBranch p) :
    MaximalSpectrum (AdjoinRoot p) :=
  ⟨RingHom.ker (divisorMap p q.val.val q.property),
    RingHom.ker_isMaximal_of_surjective _ (divisorMap_surjective _ _ _)⟩

@[simp]
theorem branchMaximal_comap (p : k[X]) (q : IrreducibleBranch p) :
    (branchMaximal p q).asIdeal.comap (mk p) = Ideal.span {q.val.val} := by
  ext a
  change divisorMap p q.val.val q.property (mk p a) = 0 ↔ _
  rw [divisorMap_mk, mk_eq_zero, Ideal.mem_span_singleton]

/-- Distinct monic factors give distinct actual maximal quotients. -/
theorem branchMaximal_injective (p : k[X]) : Function.Injective (branchMaximal p) := by
  intro q r h
  have he := congrArg (fun s : MaximalSpectrum (AdjoinRoot p) => s.asIdeal.comap (mk p)) h
  rw [branchMaximal_comap, branchMaximal_comap] at he
  apply Subtype.ext
  apply Subtype.ext
  exact Polynomial.eq_of_monic_of_associated q.val.property.1 r.val.property.1
    (Ideal.span_singleton_eq_span_singleton.mp he)

/-- Every maximal quotient of a nonzero polynomial algebra is one of its
literal monic irreducible factors. -/
theorem branchMaximal_surjective (p : k[X]) (hp : p ≠ 0) :
    Function.Surjective (branchMaximal p) := by
  classical
  intro m
  let J := m.asIdeal.comap (mk p)
  have hJ : J.IsPrime := Ideal.comap_isPrime _ _
  have hpJ : p ∈ J := by
    change mk p p ∈ m.asIdeal
    rw [mk_self]
    exact m.asIdeal.zero_mem
  have hJ0 : J ≠ ⊥ := by
    intro h
    exact hp (by simpa only [h, Ideal.mem_bot] using hpJ)
  let g := Submodule.IsPrincipal.generator J
  have hg : Prime g := Submodule.IsPrincipal.prime_generator_of_isPrime J hJ0
  have hspan : Ideal.span {normalize g} = J :=
    (Ideal.span_singleton_eq_span_singleton.mpr (normalize_associated g)).trans
      (Ideal.span_singleton_generator J)
  have hdiv : normalize g ∣ p := by
    apply Ideal.mem_span_singleton.mp
    rwa [hspan]
  let q : IrreducibleBranch p :=
    ⟨⟨normalize g, Polynomial.monic_normalize hg.ne_zero,
      (normalize_associated g).irreducible_iff.mpr hg.irreducible⟩, hdiv⟩
  refine ⟨q, ?_⟩
  apply MaximalSpectrum.ext
  apply Ideal.comap_injective_of_surjective (mk p) mk_surjective
  exact (branchMaximal_comap p q).trans hspan

/-- All maximal quotients, indexed without repetitions by the original factors. -/
def branchEquivMaximal (p : k[X]) (hp : p ≠ 0) :
    IrreducibleBranch p ≃ MaximalSpectrum (AdjoinRoot p) :=
  Equiv.ofBijective (branchMaximal p)
    ⟨branchMaximal_injective p, branchMaximal_surjective p hp⟩

/-- The quotient field at a branch is the literal polynomial quotient field. -/
def branchQuotientEquiv (p : k[X]) (q : IrreducibleBranch p) :
    (AdjoinRoot p ⧸ (branchMaximal p q).asIdeal) ≃+* AdjoinRoot q.val.val :=
  (divisorMap p q.val.val q.property).quotientKerEquivOfSurjective
    (divisorMap_surjective _ _ _)

@[simp]
theorem branchQuotientEquiv_mk (p : k[X]) (q : IrreducibleBranch p) (a : AdjoinRoot p) :
    branchQuotientEquiv p q (Ideal.Quotient.mk (branchMaximal p q).asIdeal a) =
      divisorMap p q.val.val q.property a :=
  RingHom.quotientKerEquivOfSurjective_apply_mk _ _

/-- The branch quotient equivalence preserves the original scalar map. -/
def branchQuotientAlgEquiv (p : k[X]) (q : IrreducibleBranch p) :
    (AdjoinRoot p ⧸ (branchMaximal p q).asIdeal) ≃ₐ[k] AdjoinRoot q.val.val :=
  { branchQuotientEquiv p q with
    commutes' a := by
      change branchQuotientEquiv p q
        (Ideal.Quotient.mk (branchMaximal p q).asIdeal (mk p (C a))) = mk q.val.val (C a)
      rw [branchQuotientEquiv_mk, divisorMap_mk] }

/-- A squarefree polynomial has a reduced original quotient algebra. -/
theorem isReduced_of_squarefree (p : k[X]) (hp : Squarefree p) :
    IsReduced (AdjoinRoot p) :=
  (Ideal.isRadical_iff_quotient_reduced _).mp
    (isRadical_iff_span_singleton.mp hp.isRadical)

/-- The actual local length of every maximal branch of a squarefree monic
polynomial is one. -/
theorem local_length_eq_one_of_squarefree (p : k[X]) (hp : p.Monic)
    (hs : Squarefree p) (m : MaximalSpectrum (AdjoinRoot p)) :
    Module.length (Localization.AtPrime m.asIdeal) (Localization.AtPrime m.asIdeal) = 1 := by
  let : Module.Finite k (AdjoinRoot p) := hp.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  let : IsReduced (AdjoinRoot p) := isReduced_of_squarefree p hs
  let : Field (Localization.AtPrime m.asIdeal) :=
    (IsArtinianRing.isField_of_isReduced_of_isLocalRing _).toField
  exact Module.length_eq_one _ _

/-- Every branch after arbitrary characteristic-zero scalar extension has
literal local multiplicity one. -/
theorem scalar_local_length_eq_one [CharZero k] (φ : k →+* L) (p : k[X])
    (hp : p.Monic) [Fact (Irreducible p)]
    (m : MaximalSpectrum (AdjoinRoot (p.map φ))) :
    Module.length (Localization.AtPrime m.asIdeal) (Localization.AtPrime m.asIdeal) = 1 :=
  local_length_eq_one_of_squarefree (p.map φ) (hp.map φ)
    (Polynomial.LocalResidue.squarefree_map φ p) m

/-- Coefficient extension to the whole mapped quotient algebra. -/
def scalarMap (φ : k →+* L) (p : k[X]) : AdjoinRoot p →+* AdjoinRoot (p.map φ) :=
  Ideal.Quotient.lift (Ideal.span {p})
    ((mk (p.map φ)).comp (Polynomial.mapRingHom φ)) fun a ha => by
      exact mk_eq_zero.mpr (Polynomial.map_dvd φ (Ideal.mem_span_singleton.mp ha))

@[simp]
theorem scalarMap_mk (φ : k →+* L) (p a : k[X]) :
    scalarMap φ p (mk p a) = mk (p.map φ) (a.map φ) := rfl

@[simp]
theorem scalarMap_of (φ : k →+* L) (p : k[X]) (a : k) :
    scalarMap φ p (of p a) = of (p.map φ) (φ a) := by
  change scalarMap φ p (mk p (C a)) = mk (p.map φ) (C (φ a))
  rw [scalarMap_mk, Polynomial.map_C]

@[simp]
theorem scalarMap_root (φ : k →+* L) (p : k[X]) :
    scalarMap φ p (root p) = root (p.map φ) := by
  rw [← mk_X, scalarMap_mk, Polynomial.map_X, mk_X]

/-- The original residue-field homomorphism is literally the scalar-extension
map followed by the branch quotient map. -/
theorem divisorMap_comp_scalarMap (φ : k →+* L) (p : k[X]) (q : L[X])
    [Fact (Irreducible p)] [Fact (Irreducible q)] (hq : q ∣ p.map φ) :
    (divisorMap (p.map φ) q hq).comp (scalarMap φ p) =
      Polynomial.LocalResidue.adjoinRootMap φ p q hq := by
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := mk_surjective x
  rfl

/-- The scalar map agrees with the standard AdjoinRoot functorial map. -/
theorem scalarMap_eq_map (φ : k →+* L) (p : k[X]) :
    scalarMap φ p = AdjoinRoot.map φ p (p.map φ) dvd_rfl := by
  ext a <;> simp

section Tensor

open scoped TensorProduct

variable [Algebra k L]

/-- The whole scalar tensor product is the whole mapped polynomial quotient,
with no reduction or choice of branch. -/
def scalarExtensionEquiv (p : k[X]) :
    L ⊗[k] AdjoinRoot p ≃ₐ[L] AdjoinRoot (p.map (algebraMap k L)) := by
  let e : L ⊗[k] k ≃ₐ[L] L := Algebra.TensorProduct.rid k L L
  exact (AdjoinRoot.tensorAlgEquiv p _ rfl).trans
    (AdjoinRoot.mapAlgEquiv e _ _ (by
      apply Associated.of_eq
      rw [Polynomial.map_map]
      congr 1
      apply RingHom.ext
      intro a
      change e (1 ⊗ₜ[k] a) = algebraMap k L a
      rw [Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_one]))

@[simp]
theorem scalarExtensionEquiv_root (p : k[X]) :
    scalarExtensionEquiv (L := L) p (1 ⊗ₜ[k] root p) = root (p.map (algebraMap k L)) := by
  dsimp only [scalarExtensionEquiv]
  rw [AlgEquiv.trans_apply, tensorAlgEquiv_root, coe_mapAlgEquiv, map_root]

@[simp]
theorem scalarExtensionEquiv_of (p : k[X]) (a : k) :
    scalarExtensionEquiv (L := L) p (1 ⊗ₜ[k] of p a) =
      of (p.map (algebraMap k L)) (algebraMap k L a) := by
  dsimp only [scalarExtensionEquiv]
  rw [AlgEquiv.trans_apply, tensorAlgEquiv_of, coe_mapAlgEquiv, map_of]
  change of _ ((Algebra.TensorProduct.rid k L L) (1 ⊗ₜ[k] a)) = _
  rw [Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_one]

/-- On the old algebra, the tensor-product equivalence is the literal scalar
map used by the polynomial residue construction. -/
theorem scalarExtensionEquiv_comp_includeRight (p : k[X]) :
    (scalarExtensionEquiv (L := L) p).toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom = scalarMap (algebraMap k L) p := by
  rw [scalarMap_eq_map]
  ext a <;> simp

end Tensor

end AdjoinRoot
