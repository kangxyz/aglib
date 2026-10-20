/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Module.CommutingAutomorphisms.LocalLength
public import Aglib.RingTheory.Length.ExactSequence
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Basic

/-!
# Scalar regularity on the actual Laurent module

A regular base scalar acts injectively on the original finite projective module
and on its localization at every Laurent prime. Flatness of the original module
is derived from projectivity. No regularity or flatness of a support quotient
is assumed. Normal-domain contraction for the independent finite-dominant prime
carrier belongs to `MonoidAlgebra.FiniteDominantPrime.minimalPrime_under_eq`.
-/
/-!
## Migration source

Native extraction from
`lean/R5Lab/Aglib/Algebra/Module/CommutingAutomorphisms/PrincipalRegularity.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`8988bdbfdd8f35a20f7598b58a9d4de4e725c3f461240ac33233f0895ba1ec78`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped _root_.TensorProduct AlgebraMonoidAlgebra
namespace Module.CommutingAutomorphisms
open LaurentSupport
universe u
variable {R : Type u} [CommRing R]

/-- Scalar multiplication inside the actual original Laurent module.

Source mapping: supporting generalized local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded prerequisite subset: the actual scalar endomorphism of the original realization,
linear for the full Laurent R action; no regularity or Noetherian condition is needed
for this definition. -/
def originalScalarEnd (X : Object R) (r : R) :
    Realization X →ₗ[Laurent R] Realization X :=
  LinearMap.lsmul (Laurent R) (Realization X) (algebraMap R (Laurent R) r)

theorem originalScalarEnd_injective (X : Object R) (r : R) (hr : IsRegular r) :
    Function.Injective (originalScalarEnd X r) := by
  let : Module.Flat R (Realization X) := Module.Flat.of_linearEquiv (realizationBaseEquiv X)
  have h := Module.Flat.isSMulRegular_of_isRegular (M := Realization X) hr
  intro x y hxy
  apply h
  change algebraMap R (Laurent R) r • x = algebraMap R (Laurent R) r • y at hxy
  simpa only [IsScalarTower.algebraMap_smul] using hxy

def localizedOriginalScalarEnd (X : Object R) (r : R)
    (q : Ideal (Laurent R)) [q.IsPrime] :
    LocalRealization X q →ₗ[Localization.AtPrime q] LocalRealization X q :=
  (originalScalarEnd X r).baseChange (Localization.AtPrime q)

theorem localizedOriginalScalarEnd_injective (X : Object R) (r : R) (hr : IsRegular r)
    (q : Ideal (Laurent R)) [q.IsPrime] :
    Function.Injective (localizedOriginalScalarEnd X r q) :=
  Module.Flat.lTensor_preserves_injective_linearMap (originalScalarEnd X r)
    (originalScalarEnd_injective X r hr)

theorem localizedOriginalScalarEnd_apply (X : Object R) (r : R)
    (q : Ideal (Laurent R)) [q.IsPrime] (x : LocalRealization X q) :
    localizedOriginalScalarEnd X r q x =
      algebraMap R (Localization.AtPrime q) r • x := by
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    change s ⊗ₜ[Laurent R] ((algebraMap R (Laurent R) r) • m) = _
    rw [TensorProduct.tmul_smul]
    simp only [IsScalarTower.algebraMap_smul, TensorProduct.smul_tmul']
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

/-- The actual localized original module is scalar-regular for every regular base scalar at
every Laurent prime. This is a scalar-kernel prerequisite; no Tor-functor comparison is
encoded here.

Source mapping: supporting generalized local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded prerequisite subset: IsRegular r in R gives IsSMulRegular on the localized
original realization at every Laurent prime q; no point-quotient regularity or flatness
premise is assumed. -/
theorem localOriginalScalar_regular (X : Object R) (r : R) (hr : IsRegular r)
    (q : Ideal (Laurent R)) [q.IsPrime] :
    IsSMulRegular (LocalRealization X q) (algebraMap R (Localization.AtPrime q) r) := by
  intro x y hxy
  apply localizedOriginalScalarEnd_injective X r hr q
  simpa only [localizedOriginalScalarEnd_apply] using hxy

end Module.CommutingAutomorphisms
