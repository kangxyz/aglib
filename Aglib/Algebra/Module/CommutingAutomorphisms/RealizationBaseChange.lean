/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Module.CommutingAutomorphisms.LocalLength
public import Aglib.Algebra.Module.CommutingAutomorphisms.FlatSupport
public import Aglib.RingTheory.Localization.LengthFlatBaseChange

/-!
# Scalar extension of the actual Grayson module and its local multiplicity

Supporting construction for K2-018#prop:k2018-arithmetic-characters,
mathematical source revision e73d98b1b5c1e5abcdebf7d058e436d792b87982.
The encoded slice identifies the original scalar-extended Laurent module
and derives its local lengths under the added flatness hypothesis. It does
not construct the finite motivic comparison or assert cycle naturality.

The canonical coefficient pushout identifies the original scalar-extended
module with the extension of its entire Laurent action. Localizing this exact
module identification and the flat coefficient map proves the extended-natural
local-length formula. Finite-cycle pullback and simplicial compatibility remain
separate obligations.
-/
/-!
## Migration source

Native extraction from
`lean/R5Lab/Aglib/Algebra/Module/CommutingAutomorphisms/RealizationBaseChange.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`e62ad3c3c68efc69742158543f1b7c93b647ed8e1cd762dc22c63a77a685c4f3`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped _root_.TensorProduct AlgebraMonoidAlgebra
open _root_.TensorProduct
namespace Module.CommutingAutomorphisms
open LaurentSupport
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The torus coefficient pushout cancels to the ORIGINAL scalar-extended
module, before any length or multiplicity equation is asserted. -/
def scalarModuleEquiv (X : Object R) :
    Laurent S ⊗[Laurent R] Realization X ≃ₗ[S] Realization (X.baseChange S) := by
  change Laurent S ⊗[Laurent R] Realization X ≃ₗ[S] S ⊗[R] Realization X
  exact Algebra.IsPushout.cancelBaseChange R S (Laurent R) (Laurent S) (Realization X)

@[simp] theorem scalarModuleEquiv_symm_tmul (X : Object R) (s : S) (x : Realization X) :
    (scalarModuleEquiv (S := S) X).symm (s ⊗ₜ[R] x) =
      algebraMap S (Laurent S) s ⊗ₜ[Laurent R] x :=
  Algebra.IsPushout.cancelBaseChange_symm_tmul R S (Laurent R) (Laurent S) (Realization X) s x

theorem scalarModuleEquiv_symm_coefficient_smul (X : Object R)
    (a : Laurent R) (z : Realization (X.baseChange S)) :
    (scalarModuleEquiv (S := S) X).symm
        (coefficientMap (algebraMap R S) a • z) =
      a • (scalarModuleEquiv (S := S) X).symm z := by
  induction z using TensorProduct.inductionOn with
  | tmul s x =>
    let := laurentModule X
    change (scalarModuleEquiv (S := S) X).symm
      (representation (X.baseChange S) (coefficientMap (algebraMap R S) a)
        (s ⊗ₜ[R] x)) = _
    have ha : representation (X.baseChange S) (coefficientMap (algebraMap R S) a)
        (s ⊗ₜ[R] x) = s ⊗ₜ[R] representation X a x :=
      LinearMap.congr_fun (representation_baseChange X a) (s ⊗ₜ[R] x)
    rw [ha, scalarModuleEquiv_symm_tmul, scalarModuleEquiv_symm_tmul]
    change algebraMap S (Laurent S) s ⊗ₜ[Laurent R] (a • (x : Realization X)) =
      a • (algebraMap S (Laurent S) s ⊗ₜ[Laurent R] (x : Realization X))
    exact TensorProduct.tmul_smul a _ (x : Realization X)
  | add z w hz hw => simp only [smul_add, map_add, hz, hw]

theorem scalarModuleEquiv_symm_smul (X : Object R)
    (b : Laurent S) (z : Realization (X.baseChange S)) :
    (scalarModuleEquiv (S := S) X).symm (b • z) =
      b • (scalarModuleEquiv (S := S) X).symm z := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b c hb hc => simp only [add_smul, map_add, hb, hc]
  | single m s =>
    let a : Laurent R := MonoidAlgebra.single m 1
    have h : MonoidAlgebra.single m s =
        s • coefficientMap (algebraMap R S) a := by
      simp [a]
    rw [h, smul_assoc, map_smul, scalarModuleEquiv_symm_coefficient_smul,
      smul_assoc]
    change s • (a • (scalarModuleEquiv X).symm z) =
      s • (algebraMap (Laurent R) (Laurent S) a • (scalarModuleEquiv X).symm z)
    rw [IsScalarTower.algebraMap_smul]

/-- The cancellation map is linear for the complete ORIGINAL extended
Laurent action, not only for the coefficient ring. -/
def scalarLaurentModuleEquivSymm (X : Object R) :
    Realization (X.baseChange S) ≃ₗ[Laurent S]
      Laurent S ⊗[Laurent R] Realization X where
  toEquiv := (scalarModuleEquiv X).symm.toEquiv
  map_add' := (scalarModuleEquiv X).symm.map_add
  map_smul' := scalarModuleEquiv_symm_smul X

/-- The scalar-extension equivalence for the complete Laurent action on the original module. -/
def scalarLaurentModuleEquiv (X : Object R) :
    Laurent S ⊗[Laurent R] Realization X ≃ₗ[Laurent S]
      Realization (X.baseChange S) := (scalarLaurentModuleEquivSymm X).symm

/-- Flatness of the original scalar extension passes to the literal torus
coefficient algebra through its constructed pushout. -/
theorem laurent_flat_baseChange [Module.Flat R S] :
    Module.Flat (Laurent R) (Laurent S) :=
  Module.Flat.of_linearEquiv
    (Algebra.IsPushout.equiv R (Laurent R) S (Laurent S)).symm.toLinearEquiv

/-- The local module of the literal extended object is the scalar extension
of its original Laurent module. -/
def localScalarRealizationEquiv (X : Object R) (q : Ideal (Laurent S)) [q.IsPrime] :
    LocalRealization (X.baseChange S) q ≃ₗ[Localization.AtPrime q]
      Localization.AtPrime q ⊗[Laurent R] Realization X :=
  ((scalarLaurentModuleEquiv (S := S) X).symm.baseChange
    (Laurent S) (Localization.AtPrime q) _ _).trans
      (AlgebraTensorModule.cancelBaseChange (Laurent R) (Laurent S)
        (Localization.AtPrime q) (Localization.AtPrime q) (Realization X))

/-- The actual extended-object multiplicity is the original local length
times the length of the literal contracted-prime residue fibre. -/
theorem ambientLength_flat_baseChange [Module.Flat R S]
    (X : Object R) (q : Ideal (Laurent S)) [q.IsPrime] :
    letI := Localization.AtPrime.algebraOfLiesOver (q.under (Laurent R)) q
    ambientLength (X.baseChange S) q =
      ambientLength X (q.under (Laurent R)) *
      Module.length (Localization.AtPrime q)
        (Localization.AtPrime q ⧸
          (IsLocalRing.maximalIdeal (Localization.AtPrime (q.under (Laurent R)))).map
            (algebraMap (Localization.AtPrime (q.under (Laurent R)))
              (Localization.AtPrime q))) := by
  let := Localization.AtPrime.algebraOfLiesOver (q.under (Laurent R)) q
  let : Module.Flat (Laurent R) (Laurent S) := laurent_flat_baseChange
  exact (localScalarRealizationEquiv X q).length_eq.trans
    (_root_.Module.localized_length_flat_baseChange (Realization X) q)

end Module.CommutingAutomorphisms
