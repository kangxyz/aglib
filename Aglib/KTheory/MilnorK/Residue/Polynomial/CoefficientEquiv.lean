/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Residue.Polynomial.Restriction
public import Aglib.FieldTheory.RatFuncCoefficientEquiv

/-!
# Exact transport of polynomial residues under coefficient equivalences

Every Milnor class is transported by the literal rational-function coefficient
map and the native equivalence of the original polynomial quotients. The
mapped uniformizer is the target defining polynomial itself, so no
characteristic, separability, or additional unramified hypothesis is needed.
-/

@[expose] public noncomputable section

open Polynomial Polynomial.LocalResidue

namespace Polynomial.LocalResidue

variable {A B : Type*} [Field A] [Field B]

/-- The local-residue quotient map is the native `AdjoinRoot.map`. -/
theorem adjoinRootMap_eq_map (φ : A →+* B) (p : A[X]) (q : B[X])
    [Fact (Irreducible p)] [Fact (Irreducible q)] (hq : q ∣ p.map φ) :
    adjoinRootMap φ p q hq = AdjoinRoot.map φ p q hq := by
  apply AdjoinRoot.ringHom_ext
  · ext a
    change adjoinRootMap φ p q hq (algebraMap A (AdjoinRoot p) a) = _
    rw [adjoinRootMap_algebraMap]
    exact (AdjoinRoot.map_of φ p q hq a).symm
  · rw [adjoinRootMap_root, AdjoinRoot.map_root]

/-- Equivalence of coefficient fields preserves irreducibility of the literal image. -/
theorem irreducible_map_ringEquiv (φ : A ≃+* B) (p : A[X]) (hp : Irreducible p) :
    Irreducible (p.map φ.toRingHom) :=
  hp.map (Polynomial.mapEquiv φ)

end Polynomial.LocalResidue

namespace MilnorK.PolynomialResidue

variable {A B : Type*} [Field A] [Field B]
variable (φ : A ≃+* B) (p : A[X]) [Fact (Irreducible p)]

local instance coefficientEquivMappedIrreducible : Fact (Irreducible (p.map φ.toRingHom)) :=
  ⟨irreducible_map_ringEquiv φ p Fact.out⟩

/-- Coefficient equivalence transports the residue of every class to the original
mapped polynomial quotient, in arbitrary characteristic. -/
theorem residueAt_mapRingEquiv (n : ℕ) (x : K (RatFunc A) (n + 1)) :
    residueAt (p.map φ.toRingHom) n
        (MilnorK.map (n + 1) (fractionMapRingEquiv φ).toRingHom x) =
      MilnorK.map n
        (AdjoinRoot.mapRingEquiv φ p (p.map φ.toRingHom) (Associated.refl _)).toRingHom
        (residueAt p n x) := by
  have hu : Irreducible (localRingMap φ.toRingHom p (p.map φ.toRingHom) dvd_rfl
      (algebraMap A[X] (Ring p) p)) := by
    rw [localRingMap_polynomial]
    exact irreducible_polynomial (p.map φ.toRingHom)
  have he :
      (AdjoinRoot.mapRingEquiv φ p (p.map φ.toRingHom) (Associated.refl _)).toRingHom =
        AdjoinRoot.map φ.toRingHom p (p.map φ.toRingHom) dvd_rfl := by
    apply RingHom.ext
    intro a
    rfl
  rw [he]
  simpa only [fractionMapRingEquiv_toRingHom, adjoinRootMap_eq_map] using
    residueAt_restrict_of_unramified φ.toRingHom p (p.map φ.toRingHom) dvd_rfl hu n x

/-- The exact all-class transport square as equality of the original Milnor maps. -/
theorem residueAt_comp_mapRingEquiv (n : ℕ) :
    (residueAt (p.map φ.toRingHom) n).comp
        (MilnorK.map (n + 1) (fractionMapRingEquiv φ).toRingHom) =
      (MilnorK.map n
        (AdjoinRoot.mapRingEquiv φ p (p.map φ.toRingHom) (Associated.refl _)).toRingHom).comp
        (residueAt p n) := by
  apply LinearMap.ext
  intro x
  exact residueAt_mapRingEquiv φ p n x

section Variable

local instance coefficientEquivSourceX : Fact (Irreducible (X : A[X])) := ⟨irreducible_X⟩
local instance coefficientEquivTargetX : Fact (Irreducible (X : B[X])) := ⟨irreducible_X⟩

/-- The finite `X` residue, identified with the coefficient field, commutes with
all literal coefficient maps. This is the normalization used by rational norms. -/
theorem residueAt_X_restrict_normalized (ψ : A →+* B) (n : ℕ)
    (x : K (RatFunc A) (n + 1)) :
    MilnorK.map n (InfinityResidue.rootXEquiv B).toRingHom
        (residueAt (X : B[X]) n (MilnorK.map (n + 1) (fractionMap ψ) x)) =
      MilnorK.map n ψ
        (MilnorK.map n (InfinityResidue.rootXEquiv A).toRingHom
          (residueAt (X : A[X]) n x)) := by
  have hu : Irreducible (localRingMap ψ X X (by simp)
      (algebraMap A[X] (Ring X) X)) := by
    simpa only [localRingMap_polynomial, Polynomial.map_X] using
      irreducible_polynomial (X : B[X])
  have he : (InfinityResidue.rootXEquiv B).toRingHom.comp
      (adjoinRootMap ψ X X (by simp)) =
        ψ.comp (InfinityResidue.rootXEquiv A).toRingHom := by
    apply RingHom.ext
    intro a
    exact InfinityResidue.rootXEquiv_adjoinRootMap ψ a
  rw [residueAt_restrict_of_unramified ψ X X (by simp) hu]
  change ((MilnorK.map n (InfinityResidue.rootXEquiv B).toRingHom).comp
    (MilnorK.map n (adjoinRootMap ψ X X (by simp)))) _ = _
  rw [← MilnorK.map_comp, he, MilnorK.map_comp]
  rfl

end Variable

end MilnorK.PolynomialResidue
