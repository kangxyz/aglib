/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Grassmannian.BaseChangeFormula
public import Aglib.AlgebraicGeometry.Grassmannian.Plucker

/-!
# The Plücker map of the Grassmannian

The declarations below restate the base change of exterior powers of projective modules, the
Plücker point of a point of Mathlib's Grassmannian functor with its naturality and injectivity,
and the Plücker morphism of the glued Grassmannian over `Spec R` with its monomorphism property,
and guard their axioms. The instance in `Aglib.RingTheory.Grassmannian.BaseChangeFormula`
supplies the premise `Module.Grassmannian.BaseChangeMkQFormula`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TensorProduct
open scoped Module.Grassmannian

universe u

namespace AglibTest.GrassmannianPlucker

/-- Exterior powers of a projective module commute with base change. -/
theorem isBaseChange_toBaseChange (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (k : ℕ)
    (P : Type u) [AddCommGroup P] [Module A P] [Module.Projective A P] :
    IsBaseChange B (exteriorPower.toBaseChange A B k P) :=
  exteriorPower.isBaseChange_toBaseChange A B k P

/-- The `k`-th exterior power of a finite projective module of constant rank `r` has constant rank
`r.choose k`. -/
theorem rankAtStalk_exteriorPower (A : Type u) [CommRing A] (k : ℕ) (Q : Type u) [AddCommGroup Q]
    [Module A Q] [Module.Finite A Q] [Module.Projective A Q] {r : ℕ}
    (hr : ∀ p, Module.rankAtStalk (R := A) Q p = r) (p : PrimeSpectrum A) :
    Module.rankAtStalk (R := A) (⋀[A]^k Q) p = r.choose k :=
  exteriorPower.rankAtStalk_exteriorPower k hr p

/-- The Plücker point of a point of the Grassmannian functor. -/
def plucker (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (k : ℕ)
    (A : Type u) [CommRing A] [Algebra R A] (N : G(k, A ⊗[R] M; A)) :
    G(1, A ⊗[R] ⋀[R]^k M; A) :=
  Module.Grassmannian.plucker N

/-- Its submodule is the kernel of `A ⊗ ⋀^k M → ⋀^k ((A ⊗ M) ⧸ N)`. -/
example (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (k : ℕ)
    (A : Type u) [CommRing A] [Algebra R A] (N : G(k, A ⊗[R] M; A)) :
    (plucker R M k A N).toSubmodule =
      LinearMap.ker (exteriorPower.map k N.toSubmodule.mkQ ∘ₗ
        (exteriorPower.toBaseChange R A k M).liftBaseChange A) :=
  rfl

/-- The Plücker point commutes with Mathlib's base change of points. -/
theorem map_plucker (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (k : ℕ)
    {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (f : A →ₐ[R] B)
    (N : G(k, A ⊗[R] M; A)) :
    Module.Grassmannian.map f (plucker R M k A N) =
      plucker R M k B (Module.Grassmannian.map f N) :=
  Module.Grassmannian.map_plucker f N

/-- A point of the Grassmannian is determined by its Plücker point. -/
theorem plucker_injective (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
    (k : ℕ) (A : Type u) [CommRing A] [Algebra R A] :
    Function.Injective (plucker R M k A) :=
  Module.Grassmannian.plucker_injective

/-- The Plücker transformation of Mathlib's Grassmannian functors. -/
def pluckerNatTrans (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
    (k : ℕ) :
    Module.Grassmannian.functor.{u, u, u} (R := R) (M := M) k ⟶
      Module.Grassmannian.functor.{u, u, u} (R := R) (M := ⋀[R]^k M) 1 :=
  Module.Grassmannian.pluckerNatTrans R M k

/-- The Plücker morphism `Gr(R^n, k) ⟶ Gr(R^{n.choose k}, 1)` over `Spec R`. -/
def pluckerHom (R : CommRingCat.{u}) (k n : ℕ) :
    Grassmannian.schemeOver R k n ⟶ Grassmannian.schemeOver R 1 (n.choose k) :=
  Grassmannian.plucker R k n

/-- On affine points it is the Plücker transformation. -/
theorem representableEquiv_comp_pluckerHom (R : CommRingCat.{u}) (k n : ℕ) (A : CommAlgCat.{u} R)
    (g : Grassmannian.affineOver A ⟶ Grassmannian.schemeOver R k n) :
    Grassmannian.representableEquiv R 1 (n.choose k) A (g ≫ pluckerHom R k n) =
      (Grassmannian.pluckerFinNatTrans R k n).app A (Grassmannian.representableEquiv R k n A g) :=
  Grassmannian.representableEquiv_comp_plucker R k n A g

/-- The Plücker morphism into the projective space `P(⋀^k R^n)` with Plücker coordinates. -/
def pluckerProjective (R : CommRingCat.{u}) (k n : ℕ) :
    Grassmannian.schemeOver R k n ⟶
      ProjectiveSpace.schemeOver R (ULift.{u} (Set.powersetCard (Fin n) k)) :=
  Grassmannian.pluckerProjective R k n

/-- On affine points, the Plücker morphism into projective space is the Plücker transformation. -/
theorem representableEquiv_comp_pluckerProjective (R : CommRingCat.{u}) (k n : ℕ)
    (A : CommAlgCat.{u} R) (g : Grassmannian.affineOver A ⟶ Grassmannian.schemeOver R k n) :
    ProjectiveSpace.representableEquiv R (Equiv.ulift.trans (Grassmannian.pluckerIndexEquiv k n))
        A (g ≫ pluckerProjective R k n) =
      (Grassmannian.pluckerFinNatTrans R k n).app A (Grassmannian.representableEquiv R k n A g) :=
  Grassmannian.representableEquiv_comp_pluckerProjective R k n A g

/-- The Plücker morphism is a monomorphism of schemes over `Spec R`. -/
theorem mono_pluckerHom (R : CommRingCat.{u}) (k n : ℕ) : Mono (pluckerHom R k n) :=
  inferInstanceAs (Mono (Grassmannian.plucker R k n))

/-- So is the Plücker morphism into projective space, and its underlying morphism of schemes. -/
theorem mono_pluckerProjective_left (R : CommRingCat.{u}) (k n : ℕ) :
    Mono (pluckerProjective R k n).left :=
  inferInstanceAs (Mono (Grassmannian.pluckerProjective R k n).left)

end AglibTest.GrassmannianPlucker

/-- info: 'AglibTest.GrassmannianPlucker.isBaseChange_toBaseChange' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianPlucker.isBaseChange_toBaseChange

/-- info: 'AglibTest.GrassmannianPlucker.rankAtStalk_exteriorPower' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianPlucker.rankAtStalk_exteriorPower

/-- info: 'AglibTest.GrassmannianPlucker.plucker' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianPlucker.plucker

/-- info: 'AglibTest.GrassmannianPlucker.map_plucker' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianPlucker.map_plucker

/-- info: 'AglibTest.GrassmannianPlucker.pluckerNatTrans' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianPlucker.pluckerNatTrans

/-- info: 'AglibTest.GrassmannianPlucker.pluckerHom' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianPlucker.pluckerHom

/-- info: 'AglibTest.GrassmannianPlucker.representableEquiv_comp_pluckerHom' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianPlucker.representableEquiv_comp_pluckerHom

/-- info: 'AglibTest.GrassmannianPlucker.pluckerProjective' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianPlucker.pluckerProjective

/-- info: 'AglibTest.GrassmannianPlucker.representableEquiv_comp_pluckerProjective' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianPlucker.representableEquiv_comp_pluckerProjective

/-- info: 'AglibTest.GrassmannianPlucker.plucker_injective' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianPlucker.plucker_injective

/-- info: 'AglibTest.GrassmannianPlucker.mono_pluckerHom' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianPlucker.mono_pluckerHom

/-- info: 'AglibTest.GrassmannianPlucker.mono_pluckerProjective_left' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianPlucker.mono_pluckerProjective_left

/-- info: 'exteriorPower.mem_iff_forall_wedgeLeft_mem_ker' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exteriorPower.mem_iff_forall_wedgeLeft_mem_ker
