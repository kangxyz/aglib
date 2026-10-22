/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.ParameterResidue

/-! # Actual residue images of parameter denominators

Every nonzero residue polynomial has a lift outside the parameter prime.
This identifies the denominator set used in the projected source, rather than
assuming its image is the desired parameter localization monoid.
-/

@[expose] public noncomputable section

open IsLocalRing MvPolynomial

namespace ParameterLocalization

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (ι : Type*) (p : R) [Fact (Irreducible p)]

/-- Reduction sends the complement of the parameter prime onto all nonzero
residue polynomials, through actual polynomial lifts. -/
theorem map_primeCompl_residue :
    (parameterIdeal R ι p).primeCompl.map (MvPolynomial.map (residue R)).toMonoidHom =
      nonZeroDivisors (MvPolynomial ι (ResidueField R)) := by
  ext f
  rw [Submonoid.mem_map, mem_nonZeroDivisors_iff_ne_zero]
  constructor
  · rintro ⟨g, hg, hgf⟩ hf
    apply hg
    rw [← ker_map_residue R ι p]
    change MvPolynomial.map (residue R) g = 0
    exact hgf.trans hf
  · intro hf
    obtain ⟨g, hgf⟩ := MvPolynomial.map_surjective (residue R) residue_surjective f
    refine ⟨g, ?_, hgf⟩
    intro hg
    apply hf
    rw [← hgf]
    change g ∈ RingHom.ker (MvPolynomial.map (residue R))
    rwa [ker_map_residue R ι p]

/-- The original coefficient triangle transports the actual source parameter
 denominators to the denominators of the actual residue coordinates. -/
theorem map_parameterDenominators {B D : Type*} [CommRing B] [Algebra R B]
    [CommRing D] [Algebra (ResidueField R) D] (f : B →+* D)
    (hf : f.comp (algebraMap R B) = (algebraMap (ResidueField R) D).comp (residue R))
    (b : ι → B) :
    ((parameterIdeal R ι p).primeCompl.map (aeval b).toRingHom.toMonoidHom).map
        f.toMonoidHom =
      (nonZeroDivisors (MvPolynomial ι (ResidueField R))).map
        (aeval (R := ResidueField R) (fun i => f (b i))).toRingHom.toMonoidHom := by
  let h := (aeval (R := ResidueField R) (fun i => f (b i))).toRingHom
  let red := MvPolynomial.map (residue R) (σ := ι)
  have hpoly : f.comp (aeval (R := R) b).toRingHom = h.comp red := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change f (aeval b (C r)) = aeval (R := ResidueField R) (fun i => f (b i))
        (MvPolynomial.map (residue R) (C r))
      rw [aeval_C, MvPolynomial.map_C, aeval_C]
      exact DFunLike.congr_fun hf r
    · intro i
      change f (aeval b (X i)) = aeval (R := ResidueField R) (fun i => f (b i))
        (MvPolynomial.map (residue R) (X i))
      rw [aeval_X, MvPolynomial.map_X, aeval_X]
  calc
    _ = (parameterIdeal R ι p).primeCompl.map
        (f.comp (aeval b).toRingHom).toMonoidHom := by rw [Submonoid.map_map]; rfl
    _ = (parameterIdeal R ι p).primeCompl.map (h.comp red).toMonoidHom := by rw [hpoly]
    _ = ((parameterIdeal R ι p).primeCompl.map red.toMonoidHom).map h.toMonoidHom := by
      rw [Submonoid.map_map]
      rfl
    _ = _ := by rw [show red = MvPolynomial.map (residue R) from rfl, map_primeCompl_residue]

end ParameterLocalization
