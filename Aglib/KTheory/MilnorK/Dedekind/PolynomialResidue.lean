/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Dedekind.ResidueSupport
public import Aglib.KTheory.MilnorK.Residue.Polynomial.Support

/-! # Polynomial places as actual Dedekind residues -/

@[expose] public noncomputable section

namespace MilnorK.PolynomialDedekindResidue

open Polynomial PolynomialResidue IsDedekindDomain

variable {k : Type*} [Field k]

/-- The actual nonzero prime ideal associated to a monic irreducible. -/
abbrev point (p : MonicIrreducible k) : HeightOneSpectrum k[X] :=
  ⟨Ideal.span {p.val}, inferInstance, Polynomial.LocalResidue.primeIdeal_ne_bot p.val⟩

@[simp] theorem point_asIdeal (p : MonicIrreducible k) :
    (point p).asIdeal = Ideal.span {p.val} := rfl

/-- The unique monic generator of a polynomial height-one prime. -/
def polynomial (q : HeightOneSpectrum k[X]) : MonicIrreducible k := by
  classical
  let g := Submodule.IsPrincipal.generator q.asIdeal
  have hg : Prime g := Submodule.IsPrincipal.prime_generator_of_isPrime q.asIdeal q.ne_bot
  exact ⟨normalize g, Polynomial.monic_normalize hg.ne_zero,
    (normalize_associated g).irreducible_iff.mpr hg.irreducible⟩

@[simp] theorem point_polynomial (q : HeightOneSpectrum k[X]) :
    point (polynomial q) = q := by
  classical
  apply HeightOneSpectrum.ext
  change Ideal.span {normalize (Submodule.IsPrincipal.generator q.asIdeal)} = q.asIdeal
  rw [Ideal.span_singleton_eq_span_singleton.mpr (normalize_associated _),
    Ideal.span_singleton_generator]

@[simp] theorem polynomial_point (p : MonicIrreducible k) :
    polynomial (point p) = p := by
  apply Subtype.ext
  apply Polynomial.eq_of_monic_of_associated (polynomial (point p)).property.1 p.property.1
  apply Ideal.span_singleton_eq_span_singleton.mp
  exact congrArg HeightOneSpectrum.asIdeal (point_polynomial (point p))

/-- Literal reindexing of finite polynomial places by height-one primes. -/
def pointEquiv : MonicIrreducible k ≃ HeightOneSpectrum k[X] where
  toFun := point
  invFun := polynomial
  left_inv := polynomial_point
  right_inv := point_polynomial

/-- Both constructions use the same canonical map into the original rational field. -/
theorem fractionAlgebra_eq (p : MonicIrreducible k) :
    DedekindResidue.fractionAlgebra k[X] (RatFunc k) (point p) =
      Polynomial.LocalResidue.instAlgebraRatFunc p.val := by
  apply Algebra.algebra_ext
  have h :
      @algebraMap (Polynomial.LocalResidue.Ring p.val) (RatFunc k) _ _
          (DedekindResidue.fractionAlgebra k[X] (RatFunc k) (point p)) =
      @algebraMap (Polynomial.LocalResidue.Ring p.val) (RatFunc k) _ _
          (Polynomial.LocalResidue.instAlgebraRatFunc p.val) := by
    apply IsLocalization.ringHom_ext (Ideal.span {p.val}).primeCompl
    apply RingHom.ext
    intro a
    exact (IsLocalization.lift_eq _ a).trans
      (IsScalarTower.algebraMap_apply k[X] (Polynomial.LocalResidue.Ring p.val)
        (RatFunc k) a)
  exact RingHom.congr_fun h

/-- The Dedekind residue at `(p)` is literally the polynomial residue after the
canonical quotient identification, on the unchanged rational-function class. -/
theorem totalResidue_point (p : MonicIrreducible k) (n : ℕ)
    (x : K (RatFunc k) (n + 1)) :
    MilnorK.map n (Polynomial.LocalResidue.residueEquiv p.val).toRingHom
      (DedekindResidue.totalResidue k[X] (RatFunc k) n x (point p)) =
        PolynomialResidue.residueAt p.val n x := by
  rw [PolynomialResidue.residueAt_eq_dvr]
  change _ = MilnorK.map n _ (DVR.residue (Polynomial.LocalResidue.Ring p.val)
    (RatFunc k) n x)
  rw [DedekindResidue.totalResidue_apply]
  congr 2
  congr 1
  · exact fractionAlgebra_eq p
  · apply proof_irrel_heq

end MilnorK.PolynomialDedekindResidue
