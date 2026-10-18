/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.CompleteDVRResidueEquiv
public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.Equiv

/-! Actual field and ring equivalences transport a proved local norm-residue square. -/

@[expose] public noncomputable section

namespace MilnorK

open IsLocalRing

/-- Transport uses the literal residue equivalence induced by the DVR equivalence. -/
theorem residue_finiteExtensionNorm_of_equiv
    {R S T F E L : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra R S] [Algebra R T]
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap R T)]
    [CharZero (ResidueField R)]
    [FiniteDimensional (ResidueField R) (ResidueField S)]
    [FiniteDimensional (ResidueField R) (ResidueField T)]
    [Field F] [CharZero F] [Field E] [Field L]
    [Algebra F E] [Algebra F L] [FiniteDimensional F E] [FiniteDimensional F L]
    [Algebra R F] [IsFractionRing R F]
    [Algebra S E] [IsFractionRing S E] [Algebra T L] [IsFractionRing T L]
    (j : S ≃ₐ[R] T) (ε : E ≃ₐ[F] L)
    (hε : ∀ s : S, ε (algebraMap S E s) = algebraMap T L (j s))
    (n : ℕ)
    (hsource : ∀ y : K E (n + 1),
      DVR.residue R F n (finiteExtensionNorm F E (n + 1) y) =
        finiteExtensionNorm (ResidueField R) (ResidueField S) n (DVR.residue S E n y))
    (x : K L (n + 1)) :
    DVR.residue R F n (finiteExtensionNorm F L (n + 1) x) =
      finiteExtensionNorm (ResidueField R) (ResidueField T) n (DVR.residue T L n x) := by
  have hex : ∃ y : K E (n + 1), map (n + 1) ε.toRingHom y = x := by
    refine ⟨map (n + 1) ε.symm.toRingHom x, ?_⟩
    rw [← LinearMap.comp_apply, ← map_comp]
    have hi : ε.toRingHom.comp ε.symm.toRingHom = RingHom.id L := by
      ext a
      exact ε.apply_symm_apply a
    rw [hi, map_id, LinearMap.id_apply]
  obtain ⟨y, rfl⟩ := hex
  rw [finiteExtensionNorm_map_algEquiv ε, hsource,
    ← DVR.residue_equiv_apply j.toRingEquiv ε.toRingEquiv hε]
  exact (finiteExtensionNorm_map_algEquiv (ResidueField.mapAlgEquiv' j) n _).symm

end MilnorK
