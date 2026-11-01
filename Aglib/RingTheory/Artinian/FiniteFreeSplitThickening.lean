/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Artinian.FiniteIntegralSplitQuotient

/-! # Split thickenings for finite free algebras on a principal open

The original generic algebra is split over the algebraic closure and descended
to an actual finite intermediate field. Tensor reassociation uses the original
cancel-base-change equivalence, after which finite integral coefficient capture
constructs the actual localized quotient. No split quotient is an input.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra.FiniteAlgebra

universe u v w x y

variable (R : Type u) [CommRing R] [IsDomain R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
  (Ω : Type w) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
  {A : Type x} [CommRing A] [Algebra R A] {I : Type y} [Finite I]

/-- A finite free algebra has an actual split nilpotent quotient after a
principal shrinking and a finite coefficient extension. The unchanged index
is the maximal spectrum of the original geometric generic algebra. -/
theorem exists_finiteFree_splitThickening (b : Module.Basis I R A) :
    ∃ n : ℕ, 0 < n ∧ ∃ L : IntermediateField K Ω,
      letI : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
      ∃ r : R, r ≠ 0 ∧ ∃ _hr : algebraMap R L r ≠ 0,
        ∃ B : Subalgebra R L, Module.Finite R B ∧
          ∃ qC : (Localization.Away (algebraMap R B r)) ⊗[R] A →ₐ[Localization.Away
            (algebraMap R B r)]
              (MaximalSpectrum (Ω ⊗[K] (K ⊗[R] A)) → Localization.Away (algebraMap R B r)),
            Function.Surjective qC ∧ (RingHom.ker qC.toRingHom) ^ n = ⊥ := by
  classical
  have : Module.Finite R A := Module.Finite.of_basis b
  have : IsArtinianRing (Ω ⊗[K] (K ⊗[R] A)) := IsArtinianRing.of_finite Ω _
  obtain ⟨n, hn, L, hL, qL, hqL, hnL, _⟩ :=
    exists_finiteField_splitReduction (k := K) (Ω := Ω) (A := K ⊗[R] A)
  refine ⟨n, hn, L, ?_⟩
  let : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  have : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite K L := hL
  let e := Algebra.TensorProduct.cancelBaseChange R K L L A
  let q := qL.comp e.symm.toAlgHom
  have hq : Function.Surjective q := hqL.comp e.symm.surjective
  have hnil : (RingHom.ker q.toRingHom) ^ n = ⊥ :=
    RingHom.ker_pow_eq_bot_of_injective_square e.symm.toAlgHom q.toRingHom qL.toRingHom
      (RingHom.id _) e.symm.injective (fun _ => rfl) n hnL
  obtain ⟨r, hr, hrL, B, hB, qC, hqC, hnC, _⟩ :=
    exists_finiteIntegral_away_splitQuotient R K b q hq n hnil
  exact ⟨r, hr, hrL, B, hB, qC, hqC, hnC⟩

end Algebra.FiniteAlgebra
