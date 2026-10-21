/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.HenselizationHenselian
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Polynomial coefficients in a common etale neighborhood

A finite family of multivariate polynomials over the constructed henselization
comes from one actual pointed etale neighborhood. The conclusion uses the
original colimit structure map on every coefficient. This is coefficient
descent, not an approximation theorem or a reduction preserving Jacobian rank.
-/

@[expose] public section

noncomputable section

namespace Henselization

variable (R : Type*) [CommRing R] [IsLocalRing R]

/-- A finite family of polynomials is represented in a single actual stage of
 the henselization. The variable type need not be finite. -/
theorem exists_mvPolynomial_family_rep {σ ι : Type*} [Finite ι]
    (F : ι → MvPolynomial σ (Henselization R)) :
    ∃ (S : PointedEtaleNeighborhood R) (G : ι → MvPolynomial σ S.algebra),
      ∀ i, MvPolynomial.map (Henselization.ι R S).toRingHom (G i) = F i := by
  classical
  let := Fintype.ofFinite ι
  let s : Finset (Henselization R) := Finset.univ.biUnion fun i => (F i).coeffs
  let e := Fintype.equivFin s
  obtain ⟨S, a, ha⟩ := exists_fin_rep R (fun i => (e.symm i).val)
  have hs (b : Henselization R) (hb : b ∈ s) :
      b ∈ Set.range (Henselization.ι R S).toRingHom := by
    refine ⟨a (e ⟨b, hb⟩), ?_⟩
    change Henselization.ι R S (a (e ⟨b, hb⟩)) = b
    simpa only [Equiv.symm_apply_apply] using ha (e ⟨b, hb⟩)
  have hF (i : ι) : F i ∈ Set.range
      (MvPolynomial.map (Henselization.ι R S).toRingHom) := by
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro b hb
    apply hs b
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hb⟩
  choose G hG using hF
  exact ⟨S, G, hG⟩

end Henselization
