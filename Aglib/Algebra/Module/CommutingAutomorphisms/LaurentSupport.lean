/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Module.Automorphism.BaseChange
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.Group.Commute.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Flat.Basic

/-!
# Actual Laurent action and finite support of a split Grayson generator

The ring is the coordinate algebra of the two-dimensional split torus.
Its two coordinates act by the two original commuting automorphisms. The
support algebra is the quotient by the actual action kernel, not a supplied
finite algebra. Finiteness over a Noetherian base and flatness of the represented
module are derived. This is a foundation for the support-length cycle map;
it does not yet define that cycle or a finite motivic comparison.
-/
/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/Algebra/Module/CommutingAutomorphisms/LaurentSupport.lean`
at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`08f75ddd0c03829a234b82b584a22c841d185df9b784b3bad01fd80ac5b6e938`.
-/

@[expose] public section

noncomputable section
open scoped _root_.TensorProduct
namespace Module.CommutingAutomorphisms.LaurentSupport
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

abbrev Character := Multiplicative (ℤ × ℤ)
abbrev Laurent (R : Type u) [CommRing R] := MonoidAlgebra R Character

def monomial (R : Type u) [CommRing R] (m : ℤ × ℤ) : Laurent R :=
  MonoidAlgebra.single (Multiplicative.ofAdd m) 1

def firstCoordinate (R : Type u) [CommRing R] : Laurent R := monomial R (1, 0)
def secondCoordinate (R : Type u) [CommRing R] : Laurent R := monomial R (0, 1)

theorem automorphisms_commute (X : Object R) : Commute X.a X.b := by
  apply LinearEquiv.ext
  exact X.commute

/-- The two commuting automorphisms give the actual character-lattice action. -/
def exponentAction (X : Object R) : Character →* (X.carrier ≃ₗ[R] X.carrier) where
  toFun m := X.a ^ m.toAdd.1 * X.b ^ m.toAdd.2
  map_one' := by simp
  map_mul' m n := by
    change X.a ^ (m.toAdd.1 + n.toAdd.1) * X.b ^ (m.toAdd.2 + n.toAdd.2) = _
    rw [zpow_add, zpow_add]
    simp only [mul_assoc]
    rw [← mul_assoc (X.a ^ n.toAdd.1) (X.b ^ m.toAdd.2) (X.b ^ n.toAdd.2),
      (automorphisms_commute X).zpow_zpow n.toAdd.1 m.toAdd.2 |>.eq]
    simp only [mul_assoc]

/-- The Laurent polynomial action, built from the original automorphisms. -/
def representation (X : Object R) : Laurent R →ₐ[R] Module.End R X.carrier :=
  MonoidAlgebra.lift R _ Character
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (exponentAction X))

@[simp] theorem representation_single (X : Object R) (m : Character) (r : R) :
    representation X (MonoidAlgebra.single m r) =
      r • (X.a ^ m.toAdd.1 * X.b ^ m.toAdd.2).toLinearMap := by
  simp [representation, exponentAction, MonoidAlgebra.lift_single]

@[simp] theorem representation_first (X : Object R) :
    representation X (firstCoordinate R) = X.a.toLinearMap := by
  simp [firstCoordinate, monomial]

@[simp] theorem representation_second (X : Object R) :
    representation X (secondCoordinate R) = X.b.toLinearMap := by
  simp [secondCoordinate, monomial]

/-- The support is the quotient by the actual annihilator action ideal. -/
def supportIdeal (X : Object R) : Ideal (Laurent R) := RingHom.ker (representation X)
abbrev Support (X : Object R) := Laurent R ⧸ supportIdeal X

def supportRepresentation (X : Object R) : Support X →ₐ[R] Module.End R X.carrier :=
  Ideal.kerLiftAlg (representation X)

theorem supportRepresentation_injective (X : Object R) :
    Function.Injective (supportRepresentation X) :=
  Ideal.kerLiftAlg_injective (representation X)

/-- The support is finite over the base, by its embedding into the finite-module
endomorphism ring. No flatness of the support algebra is asserted. -/
instance support_finite [IsNoetherianRing R] (X : Object R) : Module.Finite R (Support X) :=
  Module.Finite.of_injective (supportRepresentation X).toLinearMap
    (supportRepresentation_injective X)

/-- The actual represented module is finite and flat over the base. -/
theorem generator_finite_flat (X : Object R) :
    Module.Finite R X.carrier ∧ Module.Flat R X.carrier := ⟨inferInstance, inferInstance⟩

/-- The module action over its actual support algebra. -/
@[instance_reducible]
def supportModule (X : Object R) : Module (Support X) X.carrier :=
  Module.compHom X.carrier (supportRepresentation X).toRingHom

theorem supportModule_tower (X : Object R) :
    letI := supportModule X
    IsScalarTower R (Support X) X.carrier := by
  let := supportModule X
  refine ⟨fun r s x => ?_⟩
  change supportRepresentation X (r • s) x = r • supportRepresentation X s x
  rw [map_smul]
  rfl

theorem supportModule_faithful (X : Object R) :
    letI := supportModule X
    FaithfulSMul (Support X) X.carrier := by
  let := supportModule X
  refine ⟨fun {a b} h => (supportRepresentation_injective X) ?_⟩
  exact LinearMap.ext h

theorem supportModule_finite (X : Object R) :
    letI := supportModule X
    Module.Finite (Support X) X.carrier := by
  let := supportModule X
  let := supportModule_tower X
  exact Module.Finite.of_restrictScalars_finite R (Support X) X.carrier

end Module.CommutingAutomorphisms.LaurentSupport
