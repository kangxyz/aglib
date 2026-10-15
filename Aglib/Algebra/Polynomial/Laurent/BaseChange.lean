/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
Actual polynomial and Laurent coefficient pushouts for arbitrary commutative-ring maps. The
universal constructions use polynomial evaluation and the genuine Laurent coordinate unit; original
chart and coefficient-map naturality are retained.
-/

/-!
Source: `Quillen/Algebra/Polynomial/LaurentBaseChange.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Selection: whole_general_prerequisite; source ranges [[1, 215]].
Actual objects, maps, universes and hypotheses are preserved.
-/

@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u
namespace CommRingCat.PolynomialLaurent

/-- The coefficient inclusion into the polynomial ring. -/
def coefficient (R : CommRingCat.{u}) : R ⟶ CommRingCat.of (Polynomial R) :=
  CommRingCat.ofHom Polynomial.C

/-- The polynomial ring map induced by a map of coefficient rings. -/
def polynomialMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (Polynomial S) :=
  CommRingCat.ofHom (Polynomial.mapRingHom f.hom)

lemma polynomial_square {R S : CommRingCat.{u}} (f : R ⟶ S) :
    f ≫ coefficient S = coefficient R ≫ polynomialMap f := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (Polynomial.map_C f.hom).symm

/-- Polynomial coefficient extension is the actual original ring pushout. -/
lemma polynomial_isPushout {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsPushout f (coefficient R) (coefficient S) (polynomialMap f) := by
  apply IsPushout.of_isColimit (c := PushoutCocone.mk _ _ (polynomial_square f))
  apply PushoutCocone.isColimitAux'
  intro s
  let d : CommRingCat.of (Polynomial S) ⟶ s.pt :=
    CommRingCat.ofHom (Polynomial.eval₂RingHom s.inl.hom (s.inr Polynomial.X))
  refine ⟨d,?_,?_,?_⟩
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact Polynomial.eval₂_C _ _
  · apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro r
      change Polynomial.eval₂ s.inl.hom (s.inr Polynomial.X) ((Polynomial.C r).map f.hom) = s.inr
        (Polynomial.C r)
      rw [Polynomial.map_C,Polynomial.eval₂_C]
      exact congrArg (fun h ↦ h r) s.condition
    · change Polynomial.eval₂ s.inl.hom (s.inr Polynomial.X) (Polynomial.X.map f.hom) =
        s.inr Polynomial.X
      rw [Polynomial.map_X,Polynomial.eval₂_X]
  · intro h hl hr
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro a
      change h (Polynomial.C a) = Polynomial.eval₂ s.inl.hom (s.inr Polynomial.X) (Polynomial.C a)
      rw [Polynomial.eval₂_C]
      exact congrArg (fun k ↦ k a) hl
    · change h Polynomial.X = Polynomial.eval₂ s.inl.hom (s.inr Polynomial.X) Polynomial.X
      rw [Polynomial.eval₂_X]
      have hx := congrArg (fun k ↦ k Polynomial.X) hr
      simpa [polynomialMap] using hx

/-- The coefficient inclusion into the Laurent polynomial ring. -/
def laurentCoefficient (R : CommRingCat.{u}) : R ⟶ CommRingCat.of (LaurentPolynomial R) :=
  CommRingCat.ofHom LaurentPolynomial.C

/-- The Laurent polynomial ring map induced by a map of coefficient rings. -/
def laurentMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    CommRingCat.of (LaurentPolynomial R) ⟶ CommRingCat.of (LaurentPolynomial S) :=
  CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ f.hom)

@[simp] lemma laurentMap_C {R S : CommRingCat.{u}} (f : R ⟶ S) (r : R) :
    laurentMap f (LaurentPolynomial.C r) = LaurentPolynomial.C (f r) :=
  AddMonoidAlgebra.mapRingHom_single f.hom 0 r

@[simp] lemma laurentMap_T {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℤ) :
    laurentMap f (LaurentPolynomial.T n) = LaurentPolynomial.T n := by
  change AddMonoidAlgebra.mapRingHom ℤ f.hom (AddMonoidAlgebra.single n 1) = AddMonoidAlgebra.single
    n 1
  rw [AddMonoidAlgebra.mapRingHom_single,map_one]

/-- Laurent ring maps are determined by the original coefficients and T itself. -/
lemma laurent_hom_ext {R A : Type u} [CommRing R] [CommRing A]
    (f g : LaurentPolynomial R →+* A)
    (hC : ∀ r, f (LaurentPolynomial.C r) = g (LaurentPolynomial.C r))
    (hT : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) : f = g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial R))
  apply Polynomial.ringHom_ext
  · intro r
    change f (Polynomial.toLaurent (Polynomial.C r)) = g (Polynomial.toLaurent (Polynomial.C r))
    rw [Polynomial.toLaurent_C]
    exact hC r
  · change f (Polynomial.toLaurent Polynomial.X) = g (Polynomial.toLaurent Polynomial.X)
    rw [Polynomial.toLaurent_X]
    exact hT

/-- The actual coordinate unit with its literal inverse coordinate. -/
def coordinateUnit (R : CommRingCat.{u}) : (LaurentPolynomial R)ˣ :=
  ⟨LaurentPolynomial.T 1,LaurentPolynomial.T (-1),by
    rw [← LaurentPolynomial.T_add]; norm_num,by
    rw [← LaurentPolynomial.T_add]; norm_num⟩

lemma laurent_square {R S : CommRingCat.{u}} (f : R ⟶ S) :
    f ≫ laurentCoefficient S = laurentCoefficient R ≫ laurentMap f := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (laurentMap_C f r).symm

/-- Laurent coefficient extension is the actual original ring pushout. -/
lemma laurent_isPushout {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsPushout f (laurentCoefficient R) (laurentCoefficient S) (laurentMap f) := by
  apply IsPushout.of_isColimit (c := PushoutCocone.mk _ _ (laurent_square f))
  apply PushoutCocone.isColimitAux'
  intro s
  let t : s.ptˣ := Units.map s.inr.hom.toMonoidHom (coordinateUnit R)
  let d : CommRingCat.of (LaurentPolynomial S) ⟶ s.pt :=
    CommRingCat.ofHom (LaurentPolynomial.eval₂ s.inl.hom t)
  have ht : (t : s.pt) = s.inr (LaurentPolynomial.T 1) := rfl
  refine ⟨d,?_,?_,?_⟩
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact LaurentPolynomial.eval₂_C _ _ _
  · apply CommRingCat.hom_ext
    apply laurent_hom_ext
    · intro r
      change LaurentPolynomial.eval₂ s.inl.hom t (laurentMap f (LaurentPolynomial.C r)) = s.inr
        (LaurentPolynomial.C r)
      rw [laurentMap_C,LaurentPolynomial.eval₂_C]
      exact congrArg (fun h ↦ h r) s.condition
    · change LaurentPolynomial.eval₂ s.inl.hom t (laurentMap f (LaurentPolynomial.T 1)) =
        s.inr (LaurentPolynomial.T 1)
      rw [laurentMap_T,LaurentPolynomial.eval₂_T,zpow_one,ht]
  · intro h hl hr
    apply CommRingCat.hom_ext
    apply laurent_hom_ext
    · intro a
      change h (LaurentPolynomial.C a) = LaurentPolynomial.eval₂ s.inl.hom t (LaurentPolynomial.C a)
      rw [LaurentPolynomial.eval₂_C]
      exact congrArg (fun k ↦ k a) hl
    · change h (LaurentPolynomial.T 1) = LaurentPolynomial.eval₂ s.inl.hom t (LaurentPolynomial.T 1)
      rw [LaurentPolynomial.eval₂_T,zpow_one,ht]
      have hx := congrArg (fun k ↦ k (LaurentPolynomial.T 1)) hr
      change h (laurentMap f (LaurentPolynomial.T 1)) = _ at hx
      rwa [laurentMap_T] at hx

@[simp] lemma polynomialMap_comp {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    polynomialMap (f ≫ g) = polynomialMap f ≫ polynomialMap g := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  exact (Polynomial.map_map f.hom g.hom p).symm

@[simp] lemma laurentMap_comp {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    laurentMap (f ≫ g) = laurentMap f ≫ laurentMap g := by
  apply CommRingCat.hom_ext
  exact AddMonoidAlgebra.mapRingHom_comp g.hom f.hom

lemma toLaurent_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    polynomialMap f ≫ CommRingCat.ofHom Polynomial.toLaurent =
      CommRingCat.ofHom Polynomial.toLaurent ≫ laurentMap f := by
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    change Polynomial.toLaurent ((Polynomial.C r).map f.hom) = laurentMap f (Polynomial.toLaurent
      (Polynomial.C r))
    rw [Polynomial.map_C,Polynomial.toLaurent_C,Polynomial.toLaurent_C,laurentMap_C]
  · change Polynomial.toLaurent (Polynomial.X.map f.hom) = laurentMap f (Polynomial.toLaurent
    Polynomial.X)
    rw [Polynomial.map_X,Polynomial.toLaurent_X,Polynomial.toLaurent_X,laurentMap_T]

lemma invert_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    laurentMap f ≫ CommRingCat.ofHom LaurentPolynomial.invert.toRingHom =
      CommRingCat.ofHom LaurentPolynomial.invert.toRingHom ≫ laurentMap f := by
  apply CommRingCat.hom_ext
  apply laurent_hom_ext
  · intro r
    change LaurentPolynomial.invert (laurentMap f (LaurentPolynomial.C r)) =
      laurentMap f (LaurentPolynomial.invert (LaurentPolynomial.C r))
    rw [laurentMap_C,LaurentPolynomial.invert_C,LaurentPolynomial.invert_C,laurentMap_C]
  · change LaurentPolynomial.invert (laurentMap f (LaurentPolynomial.T 1)) =
      laurentMap f (LaurentPolynomial.invert (LaurentPolynomial.T 1))
    rw [laurentMap_T,LaurentPolynomial.invert_T,LaurentPolynomial.invert_T,laurentMap_T]

lemma minus_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    polynomialMap f ≫ CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp
      Polynomial.toLaurent) =
      CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent) ≫ laurentMap
        f := by
  change polynomialMap f ≫ (CommRingCat.ofHom Polynomial.toLaurent ≫
      CommRingCat.ofHom LaurentPolynomial.invert.toRingHom) =
    (CommRingCat.ofHom Polynomial.toLaurent ≫ CommRingCat.ofHom LaurentPolynomial.invert.toRingHom)
      ≫ laurentMap f
  rw [← Category.assoc,toLaurent_naturality,Category.assoc,invert_naturality,Category.assoc]

end CommRingCat.PolynomialLaurent

end
