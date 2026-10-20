/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Module.CommutingAutomorphisms.SupportNaturality

/-!
# The original Grayson modules over one common Laurent ring

The type tag below keeps different Laurent actions distinct when two objects
have the same underlying carrier. Its carrier and additive/base-module structures
are literally those of the original object, and its Laurent action is the
already constructed representation. Isomorphisms and direct sums are proved on
these actual actions, before any cycle or length compatibility is asserted.
-/
/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/Algebra/Module/CommutingAutomorphisms/Realization.lean` at
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`0b3787dd5cf2a5e7432f6163d8262e57959076e2577152d878b17bf1f59d105a`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped _root_.TensorProduct
namespace Module.CommutingAutomorphisms
open LaurentSupport
universe u
variable {R : Type u} [CommRing R]

/-- Conjugation by the ORIGINAL intertwining module isomorphism. -/
def conjugation {P Q : Type u} [AddCommGroup P] [AddCommGroup Q]
    [Module R P] [Module R Q] (e : P ≃ₗ[R] Q) :
    (P ≃ₗ[R] P) →* (Q ≃ₗ[R] Q) where
  toFun a := e.symm.trans (a.trans e)
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp

theorem conjugation_first {X Y : Object R} (e : Object.Iso X Y) :
    conjugation e.linearEquiv X.a = Y.a := by
  ext y
  change e.linearEquiv (X.a (e.linearEquiv.symm y)) = Y.a y
  rw [e.commute_a, e.linearEquiv.apply_symm_apply]

theorem conjugation_second {X Y : Object R} (e : Object.Iso X Y) :
    conjugation e.linearEquiv X.b = Y.b := by
  ext y
  change e.linearEquiv (X.b (e.linearEquiv.symm y)) = Y.b y
  rw [e.commute_b, e.linearEquiv.apply_symm_apply]

theorem conjugation_exponent {X Y : Object R} (e : Object.Iso X Y) (m : Character) :
    conjugation e.linearEquiv (exponentAction X m) = exponentAction Y m := by
  change conjugation e.linearEquiv (X.a ^ m.toAdd.1 * X.b ^ m.toAdd.2) = _
  rw [map_mul, map_zpow, map_zpow, conjugation_first, conjugation_second]
  rfl

/-- Every Laurent polynomial intertwines under the ORIGINAL object isomorphism. -/
theorem representation_iso {X Y : Object R} (e : Object.Iso X Y)
    (p : Laurent R) (x : X.carrier) :
    e.linearEquiv (representation X p x) = representation Y p (e.linearEquiv x) := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | single m r =>
    rw [representation_single, representation_single]
    change e.linearEquiv (r • (exponentAction X m) x) =
      r • (exponentAction Y m) (e.linearEquiv x)
    rw [e.linearEquiv.map_smul]
    apply congrArg (fun y => r • y)
    have h := congrArg (fun a : Y.carrier ≃ₗ[R] Y.carrier => a (e.linearEquiv x))
      (conjugation_exponent e m)
    simpa [conjugation] using h

/-- The direct-product automorphism map on the actual direct-sum module. -/
def productAut (X Y : Object R) :
    (X.carrier ≃ₗ[R] X.carrier) × (Y.carrier ≃ₗ[R] Y.carrier) →*
      ((X.sum Y).carrier ≃ₗ[R] (X.sum Y).carrier) where
  toFun a := a.1.prodCongr a.2
  map_one' := by ext x <;> rfl
  map_mul' a b := by ext x <;> rfl

theorem exponent_sum (X Y : Object R) (m : Character) :
    exponentAction (X.sum Y) m =
      (exponentAction X m).prodCongr (exponentAction Y m) := by
  have h := map_mul (productAut X Y) ((X.a, Y.a) ^ m.toAdd.1) ((X.b, Y.b) ^ m.toAdd.2)
  rw [map_zpow, map_zpow] at h
  simpa [productAut, exponentAction] using h.symm

/-- The Laurent action of the original sum is the componentwise action. -/
theorem representation_sum (X Y : Object R) (p : Laurent R) (x : X.carrier) (y : Y.carrier) :
    representation (X.sum Y) p (x, y) = (representation X p x, representation Y p y) := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp; rfl
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]; rfl
  | single m r =>
    rw [representation_single, representation_single, representation_single]
    change r • exponentAction (X.sum Y) m (x, y) =
      (r • exponentAction X m x, r • exponentAction Y m y)
    rw [exponent_sum]
    rfl

/-- Original carrier, tagged only to distinguish its actual Laurent module structure. -/
def Realization (X : Object R) : Type u := X.carrier

instance realizationAddCommGroup (X : Object R) : AddCommGroup (Realization X) := X.instAddCommGroup
instance realizationBaseModule (X : Object R) : Module R (Realization X) := X.instModule
instance realizationLaurentModule (X : Object R) : Module (Laurent R) (Realization X) :=
  laurentModule X
instance realizationFiniteBase (X : Object R) : Module.Finite R (Realization X) := X.instFinite

instance realizationTower (X : Object R) : IsScalarTower R (Laurent R) (Realization X) where
  smul_assoc r p x := by
    change representation X (r • p) x = r • representation X p x
    rw [map_smul]
    rfl

instance realizationFinite (X : Object R) : Module.Finite (Laurent R) (Realization X) :=
  Module.Finite.of_restrictScalars_finite R (Laurent R) (Realization X)

/-- The tag has the identity map to the original base module. -/
def realizationBaseEquiv (X : Object R) : Realization X ≃ₗ[R] X.carrier := LinearEquiv.refl R _

/-- The actual object isomorphism is Laurent-linear for the constructed actions. -/
def realizationIso {X Y : Object R} (e : Object.Iso X Y) :
    Realization X ≃ₗ[Laurent R] Realization Y where
  toEquiv := e.linearEquiv.toEquiv
  map_add' := e.linearEquiv.map_add
  map_smul' p x := representation_iso e p x

/-- The ORIGINAL sum module is isomorphic to the product of the original
Laurent modules by the literal pair map. -/
def realizationSum (X Y : Object R) :
    Realization (X.sum Y) ≃ₗ[Laurent R] Realization X × Realization Y where
  toEquiv := Equiv.refl _
  map_add' _ _ := rfl
  map_smul' p x := representation_sum X Y p x.1 x.2

/-- Its annihilator is the already constructed actual action kernel. -/
theorem realization_annihilator (X : Object R) :
    Module.annihilator (Laurent R) (Realization X) = supportIdeal X := by
  ext p
  rw [Module.mem_annihilator]
  change (∀ x : X.carrier, representation X p x = 0) ↔ representation X p = 0
  exact (LinearMap.ext_iff (f := representation X p) (g := 0)).symm

/-- Isomorphic ORIGINAL generators have identical actual support ideals. -/
theorem supportIdeal_iso {X Y : Object R} (e : Object.Iso X Y) :
    supportIdeal X = supportIdeal Y := by
  ext p
  change representation X p = 0 ↔ representation Y p = 0
  constructor
  · intro h
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := e.linearEquiv.surjective y
    rw [← representation_iso, h]
    exact e.linearEquiv.map_zero
  · intro h
    apply LinearMap.ext
    intro x
    apply e.linearEquiv.injective
    rw [representation_iso, h]
    simp only [LinearMap.zero_apply, map_zero]

/-- The actual sum support is governed by intersection of the two kernels.
No multiplicity additivity is inferred merely from this support equation. -/
theorem supportIdeal_sum (X Y : Object R) :
    supportIdeal (X.sum Y) = supportIdeal X ⊓ supportIdeal Y := by
  ext p
  change representation (X.sum Y) p = 0 ↔ representation X p = 0 ∧ representation Y p = 0
  constructor
  · intro h
    constructor
    · apply LinearMap.ext
      intro x
      have hx := congrArg (fun f : Module.End R (X.sum Y).carrier => (f (x, 0)).1) h
      exact (congrArg Prod.fst (representation_sum X Y p x 0)).symm.trans hx
    · apply LinearMap.ext
      intro y
      have hy := congrArg (fun f : Module.End R (X.sum Y).carrier => (f (0, y)).2) h
      exact (congrArg Prod.snd (representation_sum X Y p 0 y)).symm.trans hy
  · rintro ⟨hx, hy⟩
    apply LinearMap.ext
    rintro ⟨x, y⟩
    rw [representation_sum, hx, hy]
    rfl

end Module.CommutingAutomorphisms
