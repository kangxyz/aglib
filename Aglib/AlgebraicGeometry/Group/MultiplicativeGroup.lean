/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
/-!
# Actual multiplicative group and roots-of-unity schemes

Mathematical source revision: `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Engineering source revision: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
Manuscript locator: `K2-018#lem:k2018-geometric-exact-order`.

C4 construction prerequisite for `K2-018#lem:k2018-geometric-exact-order`,
frozen source basis `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

The absolute coordinate ring is the actual Laurent polynomial ring over the
universe-lifted integers. Its spectrum represents invertible global sections
on every scheme, using the actual Gamma/Spec adjunction and localization.
Relative products represent the same functor on schemes over any base X.
Representability supplies the genuine commutative group-object structure.
The nth-power morphism is characterized by the literal nth power of each
unit; its actual equalizer with the identity-valued map represents the
existing `rootsOfUnity n` group of global units.

All constructions and representation identities are proved without a retained
standard-theorem premise. They are valid for every base and every natural n.
This file does not assert finite etaleness at noninvertible level, nor a
Kummer H1 comparison. The coefficient here has multiplicative weight one;
it is not the arithmetic weight-two coefficient used by the final consumer.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj
namespace AlgebraicGeometry.Scheme.Group.MultiplicativeGroup
universe u

/-- The actual universal Laurent coordinate ring, in the scheme universe. -/
abbrev CoordinateRing := LaurentPolynomial (ULift.{u} ℤ)

/-- The universal Laurent coordinate `T`, regarded as a unit with inverse `T⁻¹`. -/
def coordinateUnit : CoordinateRing.{u}ˣ where
  val := LaurentPolynomial.T 1
  inv := LaurentPolynomial.T (-1)
  val_inv := by rw [← LaurentPolynomial.T_add]; norm_num
  inv_val := by rw [← LaurentPolynomial.T_add]; norm_num

/-- The canonical ring homomorphism from universe-lifted integers to a commutative ring. -/
def integerMap (R : Type u) [CommRing R] : ULift.{u} ℤ →+* R :=
  (Int.castRingHom R).comp ULift.ringEquiv.toRingHom

theorem integerMap_unique {R : Type u} [CommRing R] (f : ULift.{u} ℤ →+* R) :
    f = integerMap R := by
  ext z
  obtain ⟨z⟩ := z
  change f (z : ULift.{u} ℤ) = _
  rw [map_intCast]
  rfl

/-- Actual Laurent-ring homomorphisms are exactly units, by localization. -/
def ringHomUnitsEquiv (R : Type u) [CommRing R] : (CoordinateRing.{u} →+* R) ≃ Rˣ where
  toFun f := Units.map f.toMonoidHom coordinateUnit
  invFun a := LaurentPolynomial.eval₂ (integerMap R) a
  left_inv f := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial (ULift.{u} ℤ)))
    apply Polynomial.ringHom_ext'
    · ext z
      change LaurentPolynomial.eval₂ (integerMap R) (Units.map f.toMonoidHom coordinateUnit)
        (Polynomial.toLaurent (Polynomial.C z)) = f (Polynomial.toLaurent (Polynomial.C z))
      rw [LaurentPolynomial.eval₂_toLaurent, Polynomial.eval₂_C, Polynomial.toLaurent_C]
      exact (congrArg (fun g : ULift.{u} ℤ →+* R => g z)
        (integerMap_unique (f.comp LaurentPolynomial.C))).symm
    · change LaurentPolynomial.eval₂ (integerMap R) (Units.map f.toMonoidHom coordinateUnit)
        (Polynomial.toLaurent Polynomial.X) = f (Polynomial.toLaurent Polynomial.X)
      rw [Polynomial.toLaurent_X, LaurentPolynomial.eval₂_T]
      simp only [zpow_one]
      rfl
  right_inv a := by
    apply Units.ext
    change LaurentPolynomial.eval₂ (integerMap R) a (LaurentPolynomial.T 1) = (a : R)
    rw [LaurentPolynomial.eval₂_T, zpow_one]

theorem ringHomUnitsEquiv_comp {R S : Type u} [CommRing R] [CommRing S]
    (f : CoordinateRing.{u} →+* R) (g : R →+* S) :
    ringHomUnitsEquiv S (g.comp f) = Units.map g.toMonoidHom (ringHomUnitsEquiv R f) := by
  apply Units.ext
  rfl

/-- Units as an actual functor on commutative rings. -/
def unitsFunctor : CommRingCat.{u} ⥤ CommGrpCat.{u} where
  obj R := .of Rˣ
  map f := CommGrpCat.ofHom (Units.map f.hom.toMonoidHom)
  map_id R := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro a
    apply Units.ext
    rfl
  map_comp f g := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro a
    apply Units.ext
    rfl

/-- Actual global invertible functions, contravariant in the test scheme. -/
def globalUnitsFunctor : Scheme.{u}ᵒᵖ ⥤ CommGrpCat.{u} := Scheme.Γ ⋙ unitsFunctor

/-- The equivalence between morphisms in the opposite ring category and ring homomorphisms in
the reversed direction. -/
def opRingHomEquiv (R S : CommRingCat.{u}) : (op S ⟶ op R) ≃ (R →+* S) where
  toFun f := f.unop.hom
  invFun f := (CommRingCat.ofHom f).op
  left_inv _ := rfl
  right_inv _ := rfl

/-- The absolute Laurent affine scheme used in the multiplicative group. -/
def affineScheme : Scheme.{u} := Spec (.of CoordinateRing.{u})

/-- The actual Γ/Spec adjunction and Laurent localization represent global units. -/
def affineHomUnits (U : Scheme.{u}) : (U ⟶ affineScheme.{u}) ≃ Γ(U, ⊤)ˣ :=
  ((ΓSpec.adjunction.homEquiv U (op (.of CoordinateRing.{u}))).symm.trans
    (opRingHomEquiv (.of CoordinateRing.{u}) Γ(U, ⊤))).trans
      (ringHomUnitsEquiv Γ(U, ⊤))

theorem affineHomUnits_apply (U : Scheme.{u}) (f : U ⟶ affineScheme.{u}) :
    affineHomUnits U f = Units.map (((Scheme.ΓSpecIso (.of CoordinateRing.{u})).inv ≫
      f.appTop).hom.toMonoidHom)
      coordinateUnit := rfl

theorem affineHomUnits_comp {U V : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ affineScheme.{u}) :
    affineHomUnits U (f ≫ g) = Units.map f.appTop.hom.toMonoidHom (affineHomUnits V g) := by
  apply Units.ext
  simp only [affineHomUnits_apply, Units.coe_map,
    Scheme.Hom.comp_appTop]
  rfl

/-- The actual relative multiplicative-group scheme is the product projection. -/
def scheme (X : Scheme.{u}) : Over X := Over.mk (Limits.prod.fst : X ⨯ affineScheme.{u} ⟶ X)

/-- The equivalence identifying a morphism to the relative multiplicative scheme with its
component in the absolute Laurent affine scheme. -/
def overHomAffineEquiv (X : Scheme.{u}) (U : Over X) : (U ⟶ scheme X) ≃ (U.left ⟶ affineScheme.{u})
  where
  toFun f := f.left ≫ Limits.prod.snd
  invFun g := Over.homMk (Limits.prod.lift U.hom g) (by simp [scheme])
  left_inv f := by
    apply Over.OverMorphism.ext
    apply Limits.prod.hom_ext
    · simpa [scheme] using f.w.symm
    · simp
  right_inv g := by simp

/-- The equivalence identifying relative multiplicative-scheme sections with invertible global
functions on the test scheme. -/
def sectionsUnitsEquiv (X : Scheme.{u}) (U : Over X) : (U ⟶ scheme X) ≃ Γ(U.left, ⊤)ˣ :=
  (overHomAffineEquiv X U).trans (affineHomUnits U.left)

/-- The contravariant functor of invertible global functions on schemes over `X`. -/
def overUnitsFunctor (X : Scheme.{u}) : (Over X)ᵒᵖ ⥤ CommGrpCat.{u} :=
  (Over.forget X).op ⋙ globalUnitsFunctor

/-- Genuine unit representability on every test scheme over X. -/
def unitsRepresentable (X : Scheme.{u}) :
    (overUnitsFunctor X ⋙ CategoryTheory.forget _).RepresentableBy (scheme X) where
  homEquiv := sectionsUnitsEquiv X _
  homEquiv_comp f g := by
    change affineHomUnits _ ((f.left ≫ g.left) ≫ Limits.prod.snd) =
      Units.map f.left.appTop.hom.toMonoidHom (affineHomUnits _ (g.left ≫ Limits.prod.snd))
    rw [Category.assoc, affineHomUnits_comp]

/-- The commutative group-object structure obtained from representability of global units. -/
@[instance_reducible] def commGroup (X : Scheme.{u}) : CommGrpObj (scheme X) :=
  CommGrpObj.ofRepresentableBy _ (overUnitsFunctor X) (unitsRepresentable X)

/-- The actual commutative multiplicative group object over X. -/
def groupScheme (X : Scheme.{u}) : Grp (Over X) :=
  letI := commGroup X
  Grp.mk (scheme X)

instance groupScheme_isComm (X : Scheme.{u}) : IsCommMonObj (groupScheme X).X := by
  let := commGroup X
  infer_instance

/-- The unit representation preserves the actual group-object multiplication. -/
theorem sectionsUnitsEquiv_mul (X : Scheme.{u}) (U : Over X) (a b : U ⟶ scheme X) :
    letI := commGroup X
    sectionsUnitsEquiv X U (a * b) = sectionsUnitsEquiv X U a * sectionsUnitsEquiv X U b := by
  let := commGroup X
  exact ((yonedaMonObjIsoOfRepresentableBy (scheme X)
    (overUnitsFunctor X ⋙ forget₂ CommGrpCat GrpCat ⋙ forget₂ GrpCat MonCat) (unitsRepresentable
      X)).hom.app (op U)).hom.map_mul a b

/-- The actual nth-power morphism, obtained from the universal Laurent unit. -/
def powerMap (X : Scheme.{u}) (n : ℕ) : scheme X ⟶ scheme X :=
  (unitsRepresentable X).homEquiv.symm ((sectionsUnitsEquiv X (scheme X) (𝟙 _)) ^ n)

/-- On every actual test scheme, the scheme morphism is the literal power map. -/
theorem powerMap_comp (X : Scheme.{u}) (n : ℕ) (U : Over X) (a : U ⟶ scheme X) :
    sectionsUnitsEquiv X U (a ≫ powerMap X n) = (sectionsUnitsEquiv X U a) ^ n := by
  let e := unitsRepresentable X
  change e.homEquiv (a ≫ e.homEquiv.symm ((e.homEquiv (𝟙 _)) ^ n)) = (e.homEquiv a) ^ n
  rw [e.homEquiv_comp, Equiv.apply_symm_apply]
  change (overUnitsFunctor X).map a.op ((e.homEquiv (𝟙 _)) ^ n) = (e.homEquiv a) ^ n
  rw [map_pow]
  congr 1

/-- The constant identity morphism, characterized on actual units. -/
def oneMap (X : Scheme.{u}) : scheme X ⟶ scheme X :=
  (unitsRepresentable X).homEquiv.symm 1

theorem oneMap_comp (X : Scheme.{u}) (U : Over X) (a : U ⟶ scheme X) :
    sectionsUnitsEquiv X U (a ≫ oneMap X) = 1 := by
  let e := unitsRepresentable X
  change e.homEquiv (a ≫ e.homEquiv.symm 1) = 1
  rw [e.homEquiv_comp, Equiv.apply_symm_apply]
  exact map_one (((overUnitsFunctor X).map a.op).hom)

/-- The actual nth-power kernel scheme, before any finiteness/etaleness theorem. -/
def rootsScheme (X : Scheme.{u}) (n : ℕ) : Over X := equalizer (powerMap X n) (oneMap X)

/-- The equalizer inclusion of the roots-of-unity scheme into the multiplicative scheme. -/
def rootsInclusion (X : Scheme.{u}) (n : ℕ) : rootsScheme X n ⟶ scheme X :=
  equalizer.ι _ _

/-- Every root-scheme section is the corresponding actual global unit of nth power one. -/
def rootsHomEquiv (X : Scheme.{u}) (n : ℕ) (U : Over X) :
    (U ⟶ rootsScheme X n) ≃ rootsOfUnity n Γ(U.left, ⊤) where
  toFun f := ⟨sectionsUnitsEquiv X U (f ≫ rootsInclusion X n), by
    have h := congrArg (sectionsUnitsEquiv X U)
      (show (f ≫ rootsInclusion X n) ≫ powerMap X n =
        (f ≫ rootsInclusion X n) ≫ oneMap X from by
          change (f ≫ equalizer.ι (powerMap X n) (oneMap X)) ≫ powerMap X n =
            (f ≫ equalizer.ι (powerMap X n) (oneMap X)) ≫ oneMap X
          rw [Category.assoc, Category.assoc, equalizer.condition])
    rw [powerMap_comp, oneMap_comp] at h
    exact h⟩
  invFun a := equalizer.lift (f := powerMap X n) (g := oneMap X) ((sectionsUnitsEquiv X U).symm
    a.val)
    (by
      apply (sectionsUnitsEquiv X U).injective
      rw [powerMap_comp, oneMap_comp, Equiv.apply_symm_apply]
      exact a.property)
  left_inv f := by
    apply equalizer.hom_ext
    change equalizer.lift _ _ ≫ equalizer.ι _ _ = f ≫ rootsInclusion X n
    rw [equalizer.lift_ι, Equiv.symm_apply_apply]
  right_inv a := by
    apply Subtype.ext
    change sectionsUnitsEquiv X U (equalizer.lift _ _ ≫ equalizer.ι _ _) = a.val
    rw [equalizer.lift_ι, Equiv.apply_symm_apply]

/-- The actual roots-of-unity groups on all test schemes over X. -/
def rootsFunctor (X : Scheme.{u}) (n : ℕ) : (Over X)ᵒᵖ ⥤ CommGrpCat.{u} where
  obj U := .of (rootsOfUnity n Γ(U.unop.left, ⊤))
  map f := CommGrpCat.ofHom {
    toFun a := ⟨(overUnitsFunctor X).map f a.val, by
      change ((overUnitsFunctor X).map f a.val) ^ n = 1
      rw [← map_pow, a.property, map_one]⟩
    map_one' := Subtype.ext (map_one (((overUnitsFunctor X).map f).hom))
    map_mul' a b := Subtype.ext (map_mul (((overUnitsFunctor X).map f).hom) a.val b.val) }
  map_id U := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro a
    apply Subtype.ext
    exact congrArg (fun g => g a.val) ((overUnitsFunctor X).map_id U)
  map_comp f g := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro a
    apply Subtype.ext
    exact congrArg (fun h => h a.val) ((overUnitsFunctor X).map_comp f g)

/-- Actual representability of nth roots, including the literal restriction maps. -/
def rootsRepresentable (X : Scheme.{u}) (n : ℕ) :
    (rootsFunctor X n ⋙ CategoryTheory.forget _).RepresentableBy (rootsScheme X n) where
  homEquiv := rootsHomEquiv X n _
  homEquiv_comp f g := by
    apply Subtype.ext
    change sectionsUnitsEquiv X _ ((f ≫ g) ≫ rootsInclusion X n) =
      (overUnitsFunctor X).map f.op (sectionsUnitsEquiv X _ (g ≫ rootsInclusion X n))
    rw [Category.assoc]
    exact (unitsRepresentable X).homEquiv_comp f (g ≫ rootsInclusion X n)

/-- The commutative group-object structure obtained from representability of `n`th roots of
unity. -/
@[instance_reducible] def rootsCommGroup (X : Scheme.{u}) (n : ℕ) : CommGrpObj (rootsScheme X n) :=
  CommGrpObj.ofRepresentableBy _ (rootsFunctor X n) (rootsRepresentable X n)

/-- The group object of `n`th roots of unity over `X`. -/
def rootsGroupScheme (X : Scheme.{u}) (n : ℕ) : Grp (Over X) :=
  letI := rootsCommGroup X n
  Grp.mk (rootsScheme X n)

instance rootsGroupScheme_isComm (X : Scheme.{u}) (n : ℕ) : IsCommMonObj (rootsGroupScheme X n).X :=
  by
  let := rootsCommGroup X n
  infer_instance

end AlgebraicGeometry.Scheme.Group.MultiplicativeGroup
