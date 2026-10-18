/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Residue.Polynomial.Restriction

/-!
# Reduction of a finite residue to its literal linear place

Extend coefficients to the original residue field and take the linear place
at the original root. Evaluation identifies the resulting residue map with
the identity, not merely an injective map or a map admitting degree descent.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialResidue

open Polynomial Polynomial.LocalResidue

variable {k : Type*} [Field k]

local instance (a : k) : Fact (Irreducible (X - C a)) :=
  ⟨irreducible_X_sub_C a⟩

/-- The residue field at a linear polynomial, with its actual evaluation map. -/
def linearRootEquiv (a : k) : AdjoinRoot (X - C a) ≃ₐ[k] k := by
  let f := AdjoinRoot.liftAlgHom (X - C a) (Algebra.ofId k k) a (by simp)
  exact AlgEquiv.ofBijective f ⟨f.injective, fun b =>
    ⟨algebraMap k (AdjoinRoot (X - C a)) b, f.commutes b⟩⟩

@[simp]
theorem linearRootEquiv_mk (a : k) (g : k[X]) :
    linearRootEquiv a (AdjoinRoot.mk (X - C a) g) = g.eval a := rfl

variable (p : k[X]) [Fact (Irreducible p)]

/-- The original root gives an actual linear factor after residue-field extension. -/
theorem rootLinear_dvd_map :
    X - C (AdjoinRoot.root p) ∣ p.map (algebraMap k (AdjoinRoot p)) := by
  rw [dvd_iff_isRoot, IsRoot, eval_map, ← aeval_def]
  rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

/-- Evaluation after the actual quotient coefficient map is the identity. -/
theorem linearRootEquiv_adjoinRootMap (x : AdjoinRoot p) :
    linearRootEquiv (AdjoinRoot.root p)
      (adjoinRootMap (algebraMap k (AdjoinRoot p)) p
        (X - C (AdjoinRoot.root p)) (rootLinear_dvd_map p) x) = x := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
  rw [adjoinRootMap_mk, linearRootEquiv_mk, eval_map, ← aeval_def]
  exact AdjoinRoot.aeval_eq g

/-- The literal residue-field map in the linear-place reduction is identity. -/
theorem linearRootEquiv_comp_adjoinRootMap :
    (linearRootEquiv (AdjoinRoot.root p)).toRingHom.comp
      (adjoinRootMap (algebraMap k (AdjoinRoot p)) p
        (X - C (AdjoinRoot.root p)) (rootLinear_dvd_map p)) =
      RingHom.id (AdjoinRoot p) := by
  apply RingHom.ext
  intro x
  exact linearRootEquiv_adjoinRootMap p x

/-- Every original finite residue is recovered at the literal linear place after
coefficient extension. No degree factor or norm-independence law occurs. -/
theorem residueAt_eq_linearPlace [CharZero k]
    (n : ℕ) (x : K (RatFunc k) (n + 1)) :
    residueAt p n x =
      MilnorK.map n (linearRootEquiv (AdjoinRoot.root p)).toRingHom
        (residueAt (X - C (AdjoinRoot.root p)) n
          (MilnorK.map (n + 1) (fractionMap (algebraMap k (AdjoinRoot p))) x)) := by
  rw [residueAt_restrict _ p _ (rootLinear_dvd_map p)]
  change _ = ((MilnorK.map n _).comp (MilnorK.map n _)) _
  rw [← MilnorK.map_comp, linearRootEquiv_comp_adjoinRootMap, MilnorK.map_id]
  rfl

end MilnorK.PolynomialResidue
