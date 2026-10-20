/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Module.CommutingAutomorphisms.LaurentSupport

/-!
# Actual scalar transport and coordinate support equations

The action square is proved for every algebra map. It supplies a map on the
actual support quotients. An equality of the support with arbitrary base change
is deliberately not claimed: the flat kernel/base-change theorem remains a
separate construction. Identity-coordinate and ordered right-unit relations
are actual annihilator equations needed for the reduced support-cycle map.
-/
/-!
## Migration source

Native extraction from
`lean/R5Lab/Aglib/Algebra/Module/CommutingAutomorphisms/SupportNaturality.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`041082a5bfc603a9bb2b855d11fc0b1a2667d27b5df1c3e03ef81323042604ac`.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped _root_.TensorProduct
namespace Module.CommutingAutomorphisms.LaurentSupport
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

/-- Literal coefficient extension on the torus coordinate algebra. -/
def coefficientMap (f : R →+* S) : Laurent R →+* Laurent S :=
  MonoidAlgebra.mapRingHom Character f

@[simp] theorem coefficientMap_single (f : R →+* S) (m : Character) (r : R) :
    coefficientMap f (MonoidAlgebra.single m r) = MonoidAlgebra.single m (f r) :=
  MonoidAlgebra.mapRingHom_single _ _ _

section Scalar
variable [Algebra R S]

theorem monomial_baseChange (X : Object R) (m : Character) :
    (X.a ^ m.toAdd.1 * X.b ^ m.toAdd.2).baseChange R S =
      (X.baseChange S).a ^ m.toAdd.1 * (X.baseChange S).b ^ m.toAdd.2 := by
  rw [LinearEquiv.baseChange_mul, LinearEquiv.baseChange_zpow, LinearEquiv.baseChange_zpow]
  rfl

/-- Scalar extension commutes with the entire actual Laurent action. -/
theorem representation_baseChange (X : Object R) (p : Laurent R) :
    representation (X.baseChange S) (coefficientMap (algebraMap R S) p) =
      (representation X p).baseChange S := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, LinearMap.baseChange_add, hp, hq]
  | single m r =>
    rw [coefficientMap_single, representation_single, representation_single,
      LinearMap.baseChange_smul]
    rw [← monomial_baseChange X m]
    change (algebraMap R S r) •
        (X.a ^ m.toAdd.1 * X.b ^ m.toAdd.2).toLinearMap.baseChange S =
      r • (X.a ^ m.toAdd.1 * X.b ^ m.toAdd.2).toLinearMap.baseChange S
    exact (IsScalarTower.algebraMap_smul S r _)

/-- Every original annihilator relation vanishes after actual tensor extension. -/
theorem supportIdeal_map_le (X : Object R) :
    supportIdeal X ≤ (supportIdeal (X.baseChange S)).comap (coefficientMap (algebraMap R S)) := by
  intro p hp
  change representation (X.baseChange S) (coefficientMap (algebraMap R S) p) = 0
  rw [representation_baseChange]
  change representation X p = 0 at hp
  rw [hp, LinearMap.baseChange_zero]

/-- The actual ring map on support quotients; no kernel equality is assumed. -/
def supportMap (X : Object R) : Support X →+* Support (X.baseChange S) :=
  Ideal.quotientMap _ (coefficientMap (algebraMap R S)) (supportIdeal_map_le X)

@[simp] theorem supportMap_mk (X : Object R) (p : Laurent R) :
    supportMap (S := S) X (Ideal.Quotient.mk (supportIdeal X) p) =
      Ideal.Quotient.mk (supportIdeal (X.baseChange S)) (coefficientMap (algebraMap R S) p) := rfl

end Scalar

/-- The actual Laurent-module structure whose annihilator defines the support. -/
@[instance_reducible]
def laurentModule (X : Object R) : Module (Laurent R) X.carrier :=
  Module.compHom X.carrier (representation X).toRingHom

theorem supportIdeal_eq_annihilator (X : Object R) :
    letI := laurentModule X
    supportIdeal X = Module.annihilator (Laurent R) X.carrier := by
  let := laurentModule X
  ext p
  rw [Module.mem_annihilator]
  change representation X p = 0 ↔ ∀ x : X.carrier, representation X p x = 0
  exact LinearMap.ext_iff

/-- A generator with identity first coordinate is supported on the first identity axis. -/
theorem first_identity_relation (X : Object R) (ha : X.a = LinearEquiv.refl R X.carrier) :
    firstCoordinate R - 1 ∈ supportIdeal X := by
  change representation X (firstCoordinate R - 1) = 0
  rw [map_sub, representation_first, map_one, ha]
  exact sub_self _

/-- A generator with identity second coordinate is supported on the second identity axis. -/
theorem second_identity_relation (X : Object R) (hb : X.b = LinearEquiv.refl R X.carrier) :
    secondCoordinate R - 1 ∈ supportIdeal X := by
  change representation X (secondCoordinate R - 1) = 0
  rw [map_sub, representation_second, map_one, hb]
  exact sub_self _

/-- For the actual ordered mixed product (X, unit a), the SECOND torus
coordinate is the constant a. The two coordinates are not exchanged. -/
theorem rightUnit_relation (X : Module.Automorphism.Object R) (a : Rˣ) :
    secondCoordinate R - algebraMap R (Laurent R) (a : R) ∈
      supportIdeal (X.tensor (Module.Automorphism.Object.unit a)) := by
  change representation _ (secondCoordinate R - algebraMap R (Laurent R) (a : R)) = 0
  rw [map_sub, representation_second, AlgHom.commutes]
  apply LinearMap.ext
  intro z
  change (X.tensor (Module.Automorphism.Object.unit a)).b z - (a : R) • z = 0
  apply sub_eq_zero.mpr
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul x y =>
    change x ⊗ₜ[R] ((a : R) * y) = (a : R) • (x ⊗ₜ[R] y)
    simpa only [smul_eq_mul] using (TensorProduct.tmul_smul (R := R) (a : R) x y)

end Module.CommutingAutomorphisms.LaurentSupport
