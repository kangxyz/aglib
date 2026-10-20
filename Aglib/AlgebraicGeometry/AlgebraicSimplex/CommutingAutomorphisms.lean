/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AlgebraicSimplex.FieldBaseChange
public import Aglib.Algebra.Module.CommutingAutomorphisms.FlatSupport
public import Aglib.Algebra.Module.CommutingAutomorphisms.LocalMultiplicity
public import Aglib.Algebra.Module.CommutingAutomorphisms.SupportNaturality
public import Aglib.Algebra.Module.CommutingAutomorphisms.PrincipalSpecialization
public import Aglib.RingTheory.MonoidAlgebra.FiniteDominantPrimes

/-!
# Commuting automorphisms over algebraic simplex coordinate rings

The finite support algebra, field base change, local multiplicities and actual
face scalar cokernels specialize the native module constructions. Lengths remain
in `ENat`; the final integer identity uses `toNat` and asserts no additional
finiteness at arbitrary target primes.

These are the general simplex-dependent suffixes of the seven R5 operator
sources at revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. The lower module
files have no dependency on this geometric specialization. No cycle or K-group
construction is imported.
-/

@[expose] public noncomputable section

open AlgebraicGeometry
open _root_.Module.CommutingAutomorphisms
open _root_.Module.CommutingAutomorphisms.LaurentSupport
open _root_.MonoidAlgebra (FiniteDominantPrime)
open scoped TensorProduct AlgebraMonoidAlgebra

namespace AlgebraicGeometry.AlgebraicSimplex.CommutingAutomorphisms

universe u

/-- The actual simplex generators therefore have finite affine support. -/
theorem support_finite (K : Type u) [Field K] (j : ℕ)
    (X : Object (AlgebraicSimplex.CoordinateRing K j)) :
    Module.Finite (AlgebraicSimplex.CoordinateRing K j) (Support X) := inferInstance

/-- Specialization to the literal field-coefficient map between actual simplices. -/
theorem field_action (K L : Type u) [Field K] [Field L] (f : K →+* L)
    (j : ℕ) (X : Object (AlgebraicSimplex.CoordinateRing K j))
    (p : Laurent (AlgebraicSimplex.CoordinateRing K j)) :
    letI := (AlgebraicSimplex.coefficientMap f j).toAlgebra
    representation (X.baseChange (AlgebraicSimplex.CoordinateRing L j))
      (Module.CommutingAutomorphisms.LaurentSupport.coefficientMap
        (AlgebraicSimplex.coefficientMap f j) p) =
      (representation X p).baseChange (AlgebraicSimplex.CoordinateRing L j) := by
  let := (AlgebraicSimplex.coefficientMap f j).toAlgebra
  exact representation_baseChange X p

/-- Literal simplex generators have dominant finite support components. -/
theorem minimal_component (K : Type u) [Field K] (j : ℕ)
    (X : Object (AlgebraicSimplex.CoordinateRing K j))
    (p : Ideal (Laurent (AlgebraicSimplex.CoordinateRing K j)))
    (hp : p ∈ (supportIdeal X).minimalPrimes) :
    Module.Finite (AlgebraicSimplex.CoordinateRing K j)
        (Laurent (AlgebraicSimplex.CoordinateRing K j) ⧸ p) ∧
    Function.Injective (algebraMap (AlgebraicSimplex.CoordinateRing K j)
      (Laurent (AlgebraicSimplex.CoordinateRing K j) ⧸ p)) :=
  ⟨minimal_component_finite X p hp, minimal_component_dominant X p hp⟩

/-- The intrinsic multiplicity is finite for every original simplex generator. -/
theorem multiplicity_coe (K : Type u) [Field K] (j : ℕ)
    (X : Object (AlgebraicSimplex.CoordinateRing K j))
    (p : Ideal (Support X)) [p.IsPrime] (hp : p ∈ minimalPrimes (Support X)) :
    (multiplicity X p : ℕ∞) = localLength X p :=
  Module.CommutingAutomorphisms.LaurentSupport.multiplicity_coe X p hp

/-- The actual field coefficient extension satisfies the support-ideal equation;
its flatness is derived from the actual simplex chart and tensor pushout. -/
theorem field_supportIdeal (K L : Type u) [Field K] [Field L]
    (f : K →+* L) (j : ℕ) (X : Object (AlgebraicSimplex.CoordinateRing K j)) :
    letI := (AlgebraicSimplex.coefficientMap f j).toAlgebra
    supportIdeal (X.baseChange (AlgebraicSimplex.CoordinateRing L j)) =
      (supportIdeal X).map (Module.CommutingAutomorphisms.LaurentSupport.coefficientMap
        (AlgebraicSimplex.coefficientMap f j)) := by
  let := (AlgebraicSimplex.coefficientMap f j).toAlgebra
  let : Module.Flat (AlgebraicSimplex.CoordinateRing K j) (AlgebraicSimplex.CoordinateRing L j) :=
    AlgebraicSimplex.coefficientMap_flat f j
  exact supportIdeal_baseChange X

/-- Literal field scalar extension of each actual simplex support algebra. -/
def field_supportEquiv (K L : Type u) [Field K] [Field L]
    (f : K →+* L) (j : ℕ) (X : Object (AlgebraicSimplex.CoordinateRing K j)) :
    letI := (AlgebraicSimplex.coefficientMap f j).toAlgebra
    AlgebraicSimplex.CoordinateRing L j ⊗[AlgebraicSimplex.CoordinateRing K j] Support X ≃ₐ[
      AlgebraicSimplex.CoordinateRing L j]
      Support (X.baseChange (AlgebraicSimplex.CoordinateRing L j)) := by
  letI := (AlgebraicSimplex.coefficientMap f j).toAlgebra
  letI : Module.Flat (AlgebraicSimplex.CoordinateRing K j) (AlgebraicSimplex.CoordinateRing L j) :=
    AlgebraicSimplex.coefficientMap_flat f j
  exact supportBaseChangeEquiv X

/-- Proper contraction for every minimal component of every actual coordinate face of every
finite dominant simplex point quotient.

Source mapping: supporting generalized local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded actual-face prerequisite subset: every Field K, n : Nat, i : Fin(n + 2) and
source FiniteDominantPrime p, with Q minimal over the actual extended face ideal,
give contraction to that face ideal; no arbitrary-prime or flatness conclusion is asserted. -/
theorem minimal_face_contract (K : Type u) [Field K] (n : ℕ)
    (i : Fin (n + 2)) (p : FiniteDominantPrime (AlgebraicSimplex.CoordinateRing K (n + 1)))
    (Q : Ideal (Laurent (AlgebraicSimplex.CoordinateRing K (n + 1)) ⧸ p.val))
    (hQ : Q ∈ ((AlgebraicSimplex.faceIdeal K i).map
      (algebraMap (AlgebraicSimplex.CoordinateRing K (n + 1))
        (Laurent (AlgebraicSimplex.CoordinateRing K (n + 1)) ⧸ p.val))).minimalPrimes) :
    Q.under (AlgebraicSimplex.CoordinateRing K (n + 1)) = AlgebraicSimplex.faceIdeal K i := by
  let : IsIntegrallyClosed (AlgebraicSimplex.CoordinateRing K (n + 1)) :=
    IsIntegrallyClosed.of_equiv (AlgebraicSimplex.polynomialEquiv K (n + 1)).symm.toRingEquiv
  exact MonoidAlgebra.FiniteDominantPrime.minimalPrime_under_eq p
    (AlgebraicSimplex.faceIdeal K i) Q hQ

/-- Original Grayson modules satisfy the face regularity hypothesis at every ambient prime,
with the actual coordinate t_i and the actual Laurent action.

Source mapping: supporting generalized local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded actual-face prerequisite subset: every Field K, n : Nat, i : Fin(n + 2),
original Object X and ambient Laurent prime q give scalar regularity for the actual
coordinate on the localized original realization. -/
theorem face_local_regular (K : Type u) [Field K] (n : ℕ) (i : Fin (n + 2))
    (X : Object (AlgebraicSimplex.CoordinateRing K (n + 1)))
    (q : Ideal (Laurent (AlgebraicSimplex.CoordinateRing K (n + 1)))) [q.IsPrime] :
    IsSMulRegular (LocalRealization X q)
      (algebraMap (AlgebraicSimplex.CoordinateRing K (n + 1)) (Localization.AtPrime q)
        (AlgebraicSimplex.coordinate K (n + 1) i)) :=
  localOriginalScalar_regular X _ (AlgebraicSimplex.coordinate_isRegular K (n + 1) i) q

/-- Literal local coefficient identity for every coordinate face in every simplex degree.
The object is scalar-extended along the actual face map.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded actual-face subset: every Field K, n : Nat and i : Fin(n + 2), with the actual
face algebra instance and coordinate equation, give the ENat identity at every target
prime q. -/
theorem face_ambientLength_eq_localPrincipalCokernel_length (K : Type u) [Field K]
    (n : ℕ) (i : Fin (n + 2))
    (X : Object (AlgebraicSimplex.CoordinateRing K (n + 1)))
    (q : Ideal (Laurent (AlgebraicSimplex.CoordinateRing K n))) [q.IsPrime] :
    letI := (AlgebraicSimplex.face K i).toAlgebra
    ambientLength (X.baseChange (AlgebraicSimplex.CoordinateRing K n)) q =
      Module.length (Localization.AtPrime
        (q.under (Laurent (AlgebraicSimplex.CoordinateRing K (n + 1)))))
        (LocalPrincipalCokernel X (AlgebraicSimplex.coordinate K (n + 1) i)
          (q.under (Laurent (AlgebraicSimplex.CoordinateRing K (n + 1))))) := by
  let := (AlgebraicSimplex.face K i).toAlgebra
  exact ambientLength_principal_baseChange X _
    (AlgebraicSimplex.face_surjective K i) (AlgebraicSimplex.ker_face K i) q

/-- The actual regular face coordinate gives the target coefficient's toNat integer-cast
identity at every target prime. A finite-length interpretation additionally uses the
Noetherian-target/minimal-support conditions.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded actual-face Euler subset: every Field K, n : Nat and i : Fin(n + 2), with the
actual regular coordinate and face algebra instance, give only the toNat integer-cast
identity at arbitrary q. Finite interpretation uses the
Noetherian-target/minimal-support conditions of localPrincipalCokernel_length_ne_top. -/
theorem face_principalEuler_eq_toNat_ambientLength (K : Type u) [Field K]
    (n : ℕ) (i : Fin (n + 2))
    (X : Object (AlgebraicSimplex.CoordinateRing K (n + 1)))
    (q : Ideal (Laurent (AlgebraicSimplex.CoordinateRing K n))) [q.IsPrime] :
    letI := (AlgebraicSimplex.face K i).toAlgebra
    let Q := q.under (Laurent (AlgebraicSimplex.CoordinateRing K (n + 1)))
    _root_.Module.principalEuler
      (A := Localization.AtPrime Q) (N := LocalRealization X Q)
      (algebraMap (AlgebraicSimplex.CoordinateRing K (n + 1))
        (Localization.AtPrime Q) (AlgebraicSimplex.coordinate K (n + 1) i)) =
      ((ambientLength (X.baseChange (AlgebraicSimplex.CoordinateRing K n)) q).toNat : ℤ) := by
  let := (AlgebraicSimplex.face K i).toAlgebra
  exact principalEuler_local_original_baseChange X _
    (AlgebraicSimplex.face_surjective K i) (AlgebraicSimplex.ker_face K i)
    (AlgebraicSimplex.coordinate_isRegular K (n + 1) i) q

end AlgebraicGeometry.AlgebraicSimplex.CommutingAutomorphisms
