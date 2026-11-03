/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kaehler.Exterior.Map
public import Aglib.RingTheory.Kaehler.FractionRing
public import Aglib.RingTheory.Reflexive.DoubleDual


/-!
# Rank-one biduals over the unchanged differential base

The original ordinary differential basis over A fixes the generic top degree.
A different regular local chart C with the same fraction field and the SAME
coefficient ring has a rank-one raw-form bidual. Neither completeness nor
finiteness of C over A is used. The original differential localization is the
map used in the bidual rank calculation.
-/

@[expose] public noncomputable section

universe u

namespace KaehlerDifferential

variable {Λ A C K : Type u} [CommRing Λ] [CommRing A]
  [CommRing C] [Field K]
  [Algebra Λ A] [Algebra A K] [Algebra Λ K] [IsScalarTower Λ A K]
  [IsFractionRing A K]
  [Algebra Λ C] [Algebra C K] [IsScalarTower Λ C K] [IsFractionRing C K]
  {r : ℕ}

/-- The actual ordinary basis determines generic top-form dimension one over the same base. -/
theorem finrank_topForms_fraction_of_basis
    (b : Module.Basis (Fin r) A (KaehlerDifferential Λ A)) :
    Module.finrank K (⋀[K]^r (KaehlerDifferential Λ K)) = 1 := by
  let bK := fractionBasis (K := K) b
  let : Module.Free K (KaehlerDifferential Λ K) := Module.Free.of_basis bK
  let : Module.Finite K (KaehlerDifferential Λ K) := Module.Finite.of_basis bK
  rw [exteriorPower.finrank_eq, finrank_fraction_of_basis (K := K) b,
    Fintype.card_fin, Nat.choose_self]

include K in
/-- An actual regular local surface chart has a rank-one bidual of top raw forms,
with top degree fixed by the original A-basis and unchanged coefficient ring. -/
theorem nonempty_topFormsBidual_equiv_of_original_basis
    [IsRegularLocalRing C] (hd : ringKrullDim C ≤ 2)
    [Module.Finite C (⋀[C]^r (KaehlerDifferential Λ C))]
    (b : Module.Basis (Fin r) A (KaehlerDifferential Λ A)) :
    Nonempty (C ≃ₗ[C] Module.Dual C (Module.Dual C
      (⋀[C]^r (KaehlerDifferential Λ C)))) := by
  let : IsLocalizedModule (nonZeroDivisors C) (mapExterior Λ C K r) :=
    mapExterior_isLocalizedModule Λ C K (nonZeroDivisors C) r
  exact Module.nonempty_doubleDual_equiv_self_of_generic_rank_one hd
    (mapExterior Λ C K r) (finrank_topForms_fraction_of_basis (K := K) b)

end KaehlerDifferential
