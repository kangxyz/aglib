/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdjoinRootScalarBranches
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Literal polynomial branches of a finite product presentation

A specified equivalence with a finite product of polynomial algebras matches
every original irreducible branch with one branch of one product factor.
The residue-field equivalence retains the complete original quotient square.
-/

@[expose] public noncomputable section

open Polynomial

namespace AdjoinRoot

/-- A maximal ideal of a product factor pulls back along its actual coordinate. -/
def maximalPiMap {ι : Type*} (R : ι → Type*) [∀ i, CommRing (R i)] :
    (Σ i, MaximalSpectrum (R i)) → MaximalSpectrum (∀ i, R i)
  | ⟨i, m⟩ => ⟨m.asIdeal.comap (Pi.evalRingHom R i), m.isMaximal.comap_piEvalRingHom⟩

/-- Every maximal ideal of a finite product comes from a unique factor. -/
theorem maximalPiMap_bijective {ι : Type*} (R : ι → Type*)
    [∀ i, CommRing (R i)] [Finite ι] : Function.Bijective (maximalPiMap R) := by
  constructor
  · rintro ⟨i, u⟩ ⟨j, v⟩ h
    have he := congrArg MaximalSpectrum.toPrimeSpectrum h
    have hi := PrimeSpectrum.sigmaToPi_injective R
      (show PrimeSpectrum.sigmaToPi R ⟨i, u.toPrimeSpectrum⟩ =
        PrimeSpectrum.sigmaToPi R ⟨j, v.toPrimeSpectrum⟩ from he)
    have hij : i = j := congrArg Sigma.fst hi
    subst j
    have huv : u.toPrimeSpectrum = v.toPrimeSpectrum :=
      @sigma_mk_injective ι (fun j => PrimeSpectrum (R j)) i _ _ hi
    exact congrArg (Sigma.mk i)
      (MaximalSpectrum.toPrimeSpectrum_injective huv)
  · intro m
    obtain ⟨⟨i, t⟩, ht⟩ := (PrimeSpectrum.sigmaToPi_bijective R).2 m.toPrimeSpectrum
    have hideal : t.asIdeal.comap (Pi.evalRingHom R i) = m.asIdeal :=
      congrArg PrimeSpectrum.asIdeal ht
    have hsurj : Function.Surjective (Pi.evalRingHom R i) := Function.surjective_eval _
    have hmap : m.asIdeal.map (Pi.evalRingHom R i) = t.asIdeal := by
      rw [← hideal, Ideal.map_comap_of_surjective _ hsurj]
    have hmax : t.asIdeal.IsMaximal := by
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective
        (Pi.evalRingHom R i) hsurj m.isMaximal with htop | hmax
      · exact (t.isPrime.ne_top (hmap.symm.trans htop)).elim
      · rwa [hmap] at hmax
    exact ⟨⟨i, ⟨t.asIdeal, hmax⟩⟩, MaximalSpectrum.ext hideal⟩

/-- A finite product has exactly the maximal ideals of its individual factors. -/
def maximalPiEquiv {ι : Type*} (R : ι → Type*)
    [∀ i, CommRing (R i)] [Finite ι] :
    (Σ i, MaximalSpectrum (R i)) ≃ MaximalSpectrum (∀ i, R i) :=
  Equiv.ofBijective (maximalPiMap R) (maximalPiMap_bijective R)

/-- Transport maximal ideals by the specified ring equivalence. -/
def maximalRingEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) :
    MaximalSpectrum A ≃ MaximalSpectrum B where
  toFun m := ⟨m.asIdeal.comap e.symm.toRingHom,
    m.isMaximal.comap_bijective _ e.symm.bijective⟩
  invFun m := ⟨m.asIdeal.comap e.toRingHom,
    m.isMaximal.comap_bijective _ e.bijective⟩
  left_inv m := by
    apply MaximalSpectrum.ext
    ext a
    change e.symm (e a) ∈ m.asIdeal ↔ a ∈ m.asIdeal
    rw [RingEquiv.symm_apply_apply]
  right_inv m := by
    apply MaximalSpectrum.ext
    ext a
    change e (e.symm a) ∈ m.asIdeal ↔ a ∈ m.asIdeal
    rw [RingEquiv.apply_symm_apply]

variable {k : Type*} [Field k] {ι : Type*} [Finite ι]
  (L : ι → Type*) [∀ i, Field (L i)] (p : k[X]) (hp : p ≠ 0)
  (q : ∀ i, (L i)[X]) (hq : ∀ i, q i ≠ 0)
  (e : AdjoinRoot p ≃+* ∀ i, AdjoinRoot (q i))

/-- All nested branches, without omission or repetitions, match the original
branches under the specified finite-product algebra equivalence. -/
def piBranchEquiv : (Σ i, IrreducibleBranch (q i)) ≃ IrreducibleBranch p :=
  (Equiv.sigmaCongrRight fun i => branchEquivMaximal (q i) (hq i)).trans
    ((maximalPiEquiv (fun i => AdjoinRoot (q i))).trans
      ((maximalRingEquiv e).symm.trans (branchEquivMaximal p hp).symm))

/-- The map to a nested branch is the literal product coordinate followed
by that branch's original polynomial quotient map. -/
def piBranchMap (u : Σ i, IrreducibleBranch (q i)) :
    AdjoinRoot p →+* AdjoinRoot u.2.val.val :=
  (divisorMap (q u.1) u.2.val.val u.2.property).comp
    ((Pi.evalRingHom (fun i => AdjoinRoot (q i)) u.1).comp e.toRingHom)

omit [Finite ι] in
/-- The actual nested branch map is surjective. -/
theorem piBranchMap_surjective (u : Σ i, IrreducibleBranch (q i)) :
    Function.Surjective (piBranchMap L p q e u) :=
  (divisorMap_surjective (q u.1) u.2.val.val u.2.property).comp
    ((Function.surjective_eval _).comp e.surjective)

/-- Matched branches have exactly the kernel of the original nested quotient. -/
theorem piBranchEquiv_ideal (u : Σ i, IrreducibleBranch (q i)) :
    (branchMaximal p (piBranchEquiv L p hp q hq e u)).asIdeal =
      RingHom.ker (piBranchMap L p q e u) := by
  have h := (branchEquivMaximal p hp).apply_symm_apply
    ((maximalRingEquiv e).symm
      (maximalPiEquiv (fun i => AdjoinRoot (q i))
        ⟨u.1, branchMaximal (q u.1) u.2⟩))
  change branchMaximal p (piBranchEquiv L p hp q hq e u) = _ at h
  rw [h]
  rfl

/-- The matched literal residue fields are equivalent by the original
nested quotient, not an arbitrarily chosen field isomorphism. -/
def piBranchRingEquiv (u : Σ i, IrreducibleBranch (q i)) :
    AdjoinRoot (piBranchEquiv L p hp q hq e u).val.val ≃+* AdjoinRoot u.2.val.val :=
  (branchQuotientEquiv p (piBranchEquiv L p hp q hq e u)).symm.trans
    ((Ideal.quotEquivOfEq (piBranchEquiv_ideal L p hp q hq e u)).trans
      ((piBranchMap L p q e u).quotientKerEquivOfSurjective
        (piBranchMap_surjective L p q e u)))

/-- The entire quotient square commutes on every original algebra element. -/
theorem piBranchRingEquiv_divisorMap (u : Σ i, IrreducibleBranch (q i))
    (x : AdjoinRoot p) :
    piBranchRingEquiv L p hp q hq e u
      (divisorMap p (piBranchEquiv L p hp q hq e u).val.val
        (piBranchEquiv L p hp q hq e u).property x) =
      divisorMap (q u.1) u.2.val.val u.2.property (e x u.1) := by
  rw [← branchQuotientEquiv_mk p (piBranchEquiv L p hp q hq e u) x]
  simp only [piBranchRingEquiv, RingEquiv.trans_apply, RingEquiv.symm_apply_apply]
  rfl

variable [∀ i, Algebra k (L i)]

/-- If the whole product equivalence preserves the base field, the literal
matched branch equivalence preserves it as well. -/
def piBranchAlgEquiv
    (eₐ : AdjoinRoot p ≃ₐ[k] ∀ i, AdjoinRoot (q i))
    (u : Σ i, IrreducibleBranch (q i)) :
    AdjoinRoot (piBranchEquiv L p hp q hq eₐ.toRingEquiv u).val.val ≃ₐ[k]
      AdjoinRoot u.2.val.val :=
  { piBranchRingEquiv L p hp q hq eₐ.toRingEquiv u with
    commutes' a := by
      change piBranchRingEquiv L p hp q hq eₐ.toRingEquiv u
        (divisorMap p (piBranchEquiv L p hp q hq eₐ.toRingEquiv u).val.val
          (piBranchEquiv L p hp q hq eₐ.toRingEquiv u).property
          (algebraMap k (AdjoinRoot p) a)) = _
      rw [piBranchRingEquiv_divisorMap]
      have ha := congrFun (eₐ.commutes a) u.1
      change eₐ.toRingEquiv (algebraMap k (AdjoinRoot p) a) u.1 = _ at ha
      rw [ha]
      rfl }

end AdjoinRoot
