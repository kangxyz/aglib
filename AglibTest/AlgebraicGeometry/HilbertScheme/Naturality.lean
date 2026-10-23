/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.HilbertScheme.GrassmannianTransport

/-! Focused consumer of the naturality of the Grassmannian point of a Hilbert family (Nitsure,
arXiv:math/0504590v1, §5, p. 26), its transport to the Grassmannian of quotients of `A^N` through
the monomial basis, the base change of homogeneous polynomial sections of `𝒪(n)` and the
right-unit compatibility of the pullback tensor comparison, with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open scoped Polynomial TensorProduct

universe u

/-- The pullback tensor comparison is compatible with the right unitors. -/
example {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    (Scheme.Modules.pullback f).map (ρ_ M).inv ≫ Scheme.Modules.pullbackTensorMap f M (𝟙_ _) ≫
        ((Scheme.Modules.pullback f).obj M ◁ (Scheme.Modules.pullbackUnitIso f).hom) =
      (ρ_ ((Scheme.Modules.pullback f).obj M)).inv :=
  Scheme.Modules.pullbackTensorMap_rightUnit f M

/-- The pullback of the section of a homogeneous polynomial is the section of the polynomial with
mapped coefficients. -/
example {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (ι : Type u) (n : ℕ)
    (p : MvPolynomial.homogeneousSubmodule ι R n) :
    (twistingPullbackIso φ ι n).hom.val.app (op ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction (map φ ι)).unit.app
          (twistingSheaf R ι n)).val.app (op ⊤) (homogeneousSection R ι n p)) =
      homogeneousSection S ι n ((MvPolynomial.gradedMap (ι := ι) φ).gradedAddHom n p) :=
  twistingPullbackIso_hom_unit_homogeneousSection φ ι n p

/-- **Naturality of the Grassmannian point**: base change along `f : B → B'` of the point of `Z`
is the point of the pullback of `Z`. -/
example {A : Type u} [CommRing A] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) {Φ : ℚ[X]}
    {B B' : Type u} [CommRing B] [Algebra A B] [IsNoetherianRing B] [CommRing B'] [Algebra A B']
    [IsNoetherianRing B'] (f : B →ₐ[A] B')
    {Z : (pullback (toSpec A ι) (Spec.map (CommRingCat.ofHom (algebraMap A B)))).IdealSheafData}
    (hZ : IsHilbertFamily ι Φ (Spec.map (CommRingCat.ofHom (algebraMap A B))) Z)
    (h : Spec.map (CommRingCat.ofHom (f : B →+* B')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      Spec.map (CommRingCat.ofHom (algebraMap A B')))
    (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) :
    Module.Grassmannian.map f (hZ.grassmannianFunctorPoint ι n e r hr) =
      (hZ.comap ι _ h).grassmannianFunctorPoint ι n e r hr :=
  hZ.map_grassmannianFunctorPoint ι n e f _ rfl h r hr

/-- **The Grassmannian embedding on Noetherian affine test schemes**: a natural transformation
from `B ↦ Hilb^Φ(Spec B)` to Mathlib's Grassmannian functor, injective at every `B`. -/
example {A : Type u} [CommRing A] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) (Φ : ℚ[X]) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r)
    (B : ObjectProperty.FullSubcategory fun B : CommAlgCat.{u} A => IsNoetherianRing B) :
    Function.Injective ((noetherianAffineGrassmannianNatTrans ι n e A Φ r hr).app B) :=
  noetherianAffineGrassmannianNatTrans_app_injective ι n e A Φ r hr B

/-- **Through the monomial basis**: the embedding with values in the Grassmannian of rank
`⌊Φ(r)⌋₊` quotients of `A^N`, `N = (n + r).choose r`, the functor that
`Grassmannian.localFunctor` uses. -/
example {A : Type u} [CommRing A] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) (Φ : ℚ[X]) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r) :
    noetherianAffineHilbertFunctor ι A Φ ⟶ ObjectProperty.ι _ ⋙
      Module.Grassmannian.functor.{u, u, u} (R := A)
        (M := Fin ((n + r).choose r) → A) ⌊Φ.eval (r : ℚ)⌋₊ :=
  noetherianAffineGrassmannianNatTransFin ι n e A Φ r hr

/--
info: 'AlgebraicGeometry.Scheme.Modules.pullbackTensorMap_rightUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackTensorMap_rightUnit

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingPullbackIso_hom_unit_homogeneousSection' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingPullbackIso_hom_unit_homogeneousSection

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingTensorPullbackIso_rightUnitor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingTensorPullbackIso_rightUnitor

/--
info: 'MvPolynomial.homogeneousSubmoduleBaseChangeEquiv_rTensor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.homogeneousSubmoduleBaseChangeEquiv_rTensor

/--
info: 'AlgebraicGeometry.ProjectiveSpace.unitTwistPullbackHom_comp_g' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.unitTwistPullbackHom_comp_g

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.equiv₀_twistingH0PolynomialLinearEquiv_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.equiv₀_twistingH0PolynomialLinearEquiv_symm

/--
info: 'AlgebraicGeometry.ProjectiveSpace.restrictionH0_unitTwistH0Equiv_rTensor_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.restrictionH0_unitTwistH0Equiv_rTensor_eq_zero

/--
info: 'AlgebraicGeometry.ProjectiveSpace.map_ofLinearEquiv_grassmannianPoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.map_ofLinearEquiv_grassmannianPoint

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.map_grassmannianFunctorPoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.map_grassmannianFunctorPoint

/--
info: 'AlgebraicGeometry.ProjectiveSpace.noetherianAffineGrassmannianNatTrans' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.noetherianAffineGrassmannianNatTrans

/--
info: 'AlgebraicGeometry.ProjectiveSpace.noetherianAffineGrassmannianNatTrans_app_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.noetherianAffineGrassmannianNatTrans_app_injective

/--
info: 'Module.Grassmannian.functorIsoOfLinearEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Module.Grassmannian.functorIsoOfLinearEquiv

/--
info: 'Finsupp.natCard_degree_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Finsupp.natCard_degree_eq

/--
info: 'Module.Grassmannian.map_ofLinearEquiv_baseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Module.Grassmannian.map_ofLinearEquiv_baseChange

/--
info: 'AlgebraicGeometry.ProjectiveSpace.noetherianAffineGrassmannianNatTransFin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.noetherianAffineGrassmannianNatTransFin
