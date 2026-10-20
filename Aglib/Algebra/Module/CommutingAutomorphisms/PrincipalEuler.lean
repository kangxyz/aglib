/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Module.CommutingAutomorphisms.PrincipalSpecialization
public import Aglib.RingTheory.Length.ExactSequence
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Basic
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Additivity
public import Aglib.RingTheory.ScalarHomology.Basic

/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/Algebra/Module/CommutingAutomorphisms/PrincipalEuler.lean`
at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`8c328aebf784be46c6b87249cd9c52df2da13e11de5ec47fbee6ca7799bd6c76`.
-/

@[expose] public section

open _root_.Module (FinitePrincipal finitePrincipal_of_regular)

noncomputable section
set_option autoImplicit false
open scoped _root_.TensorProduct AlgebraMonoidAlgebra
namespace Module.CommutingAutomorphisms
open LaurentSupport
open _root_.Module
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The actual original Laurent module stays finitely generated after localization. -/
theorem localOriginal_moduleFinite (X : Object R) (Q : Ideal (Laurent R)) [Q.IsPrime] :
    Module.Finite (Localization.AtPrime Q) (LocalRealization X Q) := by
  infer_instance

/-- Every target prime pulls back to a source prime containing the actual
principal scalar. Its localized image is therefore in the local maximal ideal. -/
theorem localOriginalScalar_mem_maximalIdeal (t : R) (ht : algebraMap R S t = 0)
    (q : Ideal (Laurent S)) [q.IsPrime] :
    algebraMap R (Localization.AtPrime (q.under (Laurent R))) t ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime (q.under (Laurent R))) := by
  let Q := q.under (Laurent R)
  have hQ : algebraMap R (Laurent R) t ∈ Q := by
    change coefficientMap (algebraMap R S) (algebraMap R (Laurent R) t) ∈ q
    have hz : coefficientMap (algebraMap R S) (algebraMap R (Laurent R) t) = 0 := by
      have hh := RingHom.congr_fun
        (MonoidAlgebra.mapRingHom_comp_algebraMap (M := Character) (algebraMap R S)) t
      simpa only [coefficientMap, RingHom.comp_apply, ht, map_zero] using hh
    rw [hz]
    exact q.zero_mem
  rw [IsScalarTower.algebraMap_apply R (Laurent R) (Localization.AtPrime Q)]
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q _).mpr hQ

/-- The genuine localized original source object satisfies finite principal
Euler homology at every actual minimal target component. No filtration or
coefficient-sum identity is used in this prerequisite. -/
theorem localOriginal_finitePrincipal [IsNoetherianRing S]
    (X : Object R) (t : R) (h : Function.Surjective (algebraMap R S))
    (ht : RingHom.ker (algebraMap R S) = Ideal.span ({t} : Set R)) (hr : IsRegular t)
    (q : Ideal (Laurent S)) [q.IsPrime]
    (hq : q ∈ (supportIdeal (X.baseChange S)).minimalPrimes) :
    FinitePrincipal (LocalRealization X (q.under (Laurent R)))
      (algebraMap R (Localization.AtPrime (q.under (Laurent R))) t) := by
  let Q := q.under (Laurent R)
  apply finitePrincipal_of_regular _ _ (localOriginalScalar_regular X t hr Q)
  have he := Module.endCokernel_length_congr
    (A := Localization.AtPrime Q) (N := LocalRealization X Q)
    (localizedOriginalScalarEnd X t Q)
    (LinearMap.lsmul (Localization.AtPrime Q) (LocalRealization X Q)
      (algebraMap R (Localization.AtPrime Q) t))
    (localizedOriginalScalarEnd_eq_lsmul X t Q)
  rw [← he]
  exact localPrincipalCokernel_length_ne_top X t h ht q hq

end Module.CommutingAutomorphisms
