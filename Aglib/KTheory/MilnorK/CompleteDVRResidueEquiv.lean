/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.CompleteDVRExtension
public import Aglib.KTheory.MilnorK.Residue.Restriction

/-!
# Transport of the actual complete-DVR residue through field equivalences

The ring equivalence is the restriction of the specified field equivalence to
its two actual integral closures. Its residue equivalence is induced by this
same restriction. No norm, residue compatibility, or uniformizer-preservation
hypothesis is added: the latter follows from the ring equivalence itself.
-/

@[expose] public noncomputable section

namespace MilnorK

namespace DVR

variable {S T E L : Type*}
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Field L] [Algebra T L] [IsFractionRing T L]

/-- Every actual DVR equivalence preserves the canonical residue in all degrees. -/
theorem residue_equiv (j : S ≃+* T) (ε : E ≃+* L)
    (hε : ∀ s : S, ε (algebraMap S E s) = algebraMap T L (j s)) (n : ℕ) :
    (map n (IsLocalRing.ResidueField.mapEquiv j).toRingHom).comp (residue S E n) =
      (residue T L n).comp (map (n + 1) ε.toRingHom) := by
  let : IsLocalHom j.toRingHom := ⟨fun _ h => (MulEquiv.isUnit_map j).mp h⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible S
  exact residue_restrict j.toRingHom ε.toRingHom hε hπ (hπ.map j) n

/-- The same actual equivalence square evaluated on any Milnor class. -/
theorem residue_equiv_apply (j : S ≃+* T) (ε : E ≃+* L)
    (hε : ∀ s : S, ε (algebraMap S E s) = algebraMap T L (j s))
    (n : ℕ) (x : K E (n + 1)) :
    map n (IsLocalRing.ResidueField.mapEquiv j).toRingHom (residue S E n x) =
      residue T L n (map (n + 1) ε.toRingHom x) :=
  LinearMap.congr_fun (residue_equiv j ε hε n) x

end DVR

namespace CompleteDVRResidueEquiv

open IsLocalRing

section Maps

variable (R F : Type*) {E L : Type*} [CommRing R] [CommRing F]
  [CommRing E] [CommRing L] [Algebra R F]
  [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra F L] [Algebra R L] [IsScalarTower R F L]

/-- Restriction of the specified field equivalence, with no chosen closure model. -/
def closureEquiv (ε : E ≃ₐ[F] L) : integralClosure R E ≃ₐ[R] integralClosure R L :=
  (ε.restrictScalars R).mapIntegralClosure

/-- On actual integral elements, the restriction has literally the specified values. -/
theorem closureEquiv_apply (ε : E ≃ₐ[F] L) (s : integralClosure R E) :
    algebraMap (integralClosure R L) L (closureEquiv R F ε s) =
      ε (algebraMap (integralClosure R E) E s) := rfl

variable [IsLocalRing (integralClosure R E)] [IsLocalRing (integralClosure R L)]

/-- The residue-field equivalence induced by the literal integral-closure map. -/
def residueEquiv (ε : E ≃ₐ[F] L) :
    ResidueField (integralClosure R E) ≃+* ResidueField (integralClosure R L) :=
  ResidueField.mapEquiv (closureEquiv R F ε).toRingEquiv

/-- Reduction of an integral element commutes with the specified equivalence. -/
@[simp] theorem residueEquiv_residue (ε : E ≃ₐ[F] L) (s : integralClosure R E) :
    residueEquiv R F ε (IsLocalRing.residue (integralClosure R E) s) =
      IsLocalRing.residue (integralClosure R L) (closureEquiv R F ε s) := rfl

variable [IsLocalRing R]
  [IsLocalHom (algebraMap R (integralClosure R E))]
  [IsLocalHom (algebraMap R (integralClosure R L))]

/-- The same induced equivalence also respects the actual base residue field. -/
def residueAlgEquiv (ε : E ≃ₐ[F] L) :
    ResidueField (integralClosure R E) ≃ₐ[ResidueField R]
      ResidueField (integralClosure R L) :=
  ResidueField.mapAlgEquiv' (closureEquiv R F ε)

/-- Forgetting the base residue algebra does not change the actual map. -/
@[simp] theorem residueAlgEquiv_toRingEquiv (ε : E ≃ₐ[F] L) :
    (residueAlgEquiv R F ε).toRingEquiv = residueEquiv R F ε := rfl

end Maps

section ActualDVRs

variable (R F : Type*) {E L : Type*} [CommRing R] [CommRing F]
  [Field E] [Field L] [Algebra R F]
  [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra F L] [Algebra R L] [IsScalarTower R F L]
  [IsDiscreteValuationRing (integralClosure R E)]
  [IsDiscreteValuationRing (integralClosure R L)]
  [IsFractionRing (integralClosure R E) E] [IsFractionRing (integralClosure R L) L]

/-- The canonical tame-residue square uses the literal restricted field equivalence. -/
theorem residue_naturality (ε : E ≃ₐ[F] L) (n : ℕ) :
    (map n (residueEquiv R F ε).toRingHom).comp
        (DVR.residue (integralClosure R E) E n) =
      (DVR.residue (integralClosure R L) L n).comp (map (n + 1) ε.toRingHom) :=
  DVR.residue_equiv (closureEquiv R F ε).toRingEquiv ε.toRingEquiv (fun _ => rfl) n

/-- Naturality on every quotient class, without bounds on any symbol's valuations. -/
theorem residue_naturality_apply (ε : E ≃ₐ[F] L) (n : ℕ) (x : K E (n + 1)) :
    map n (residueEquiv R F ε).toRingHom (DVR.residue (integralClosure R E) E n x) =
      DVR.residue (integralClosure R L) L n (map (n + 1) ε.toRingHom x) :=
  LinearMap.congr_fun (residue_naturality R F ε n) x

end ActualDVRs

section Complete

variable (R F : Type*) {E L : Type*}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Field L] [Algebra F L] [Algebra R L] [IsScalarTower R F L]
  [FiniteDimensional F E] [FiniteDimensional F L]
  [Algebra.IsSeparable F E] [Algebra.IsSeparable F L]

/-- For finite separable extensions of a complete DVR, all actual closure
structures in the residue square are derived, not supplied as hypotheses. -/
theorem residue_naturality_complete (ε : E ≃ₐ[F] L) (n : ℕ) :
    let _ := IsDiscreteValuationRing.CompleteExtension.integralClosure_isDiscreteValuationRing R F E
    let _ := IsDiscreteValuationRing.CompleteExtension.integralClosure_isDiscreteValuationRing R F L
    let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F E (integralClosure R E)
    let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F L (integralClosure R L)
    (map n (residueEquiv R F ε).toRingHom).comp
        (DVR.residue (integralClosure R E) E n) =
      (DVR.residue (integralClosure R L) L n).comp (map (n + 1) ε.toRingHom) := by
  dsimp only
  let _ := IsDiscreteValuationRing.CompleteExtension.integralClosure_isDiscreteValuationRing R F E
  let _ := IsDiscreteValuationRing.CompleteExtension.integralClosure_isDiscreteValuationRing R F L
  let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F E (integralClosure R E)
  let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F L (integralClosure R L)
  exact residue_naturality R F ε n

end Complete

end CompleteDVRResidueEquiv

end MilnorK
