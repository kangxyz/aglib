/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.StalkMap
public import Aglib.AlgebraicGeometry.Stalk.CodimensionOne
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Actual local and constant maps over a Dedekind base

For an actual dominant morphism `f : X ⟶ Spec A`, the constant-field map is
the actual generic stalk map, preceded by the canonical isomorphism from the
given fraction field of `A`. At each actual point, the localization-to-stalk
map is the canonical affine stalk isomorphism followed by `f.stalkMap`.
Their compatibility is proved from naturality of stalk specialization and
the localization universal property.

When the actual image prime is zero, the constant field itself maps to the
stalk, so all its multiplicative units are stalk units. When that prime is
nonzero, it defines an actual `HeightOneSpectrum A` index. No assumption that
the morphism preserves codimension one is needed.

## Source correspondence

Auxiliary local geometry for the arithmetic constant-map slice of
`research/exposes/K2/018/expose.tex`, `K2-018#sec:k2018-introduction`, lines
63–82, and `K2-018#sec:k2018-splitting`, lines 221–253, at baseline commit
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, source SHA-256
`e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299`.
This correspondence covers all declarations below as auxiliary geometry;
no Quillen comparison or arithmetic-model image equality is asserted.

Implementation basis: `6987216b7dfb16036f94cc41b3c33a2da4e5e535`;
Lean `4.34.1`, mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
-/

@[expose] public section





noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
universe u v
namespace AlgebraicGeometry.Scheme.DedekindBase

variable {A : Type u} [CommRing A] [IsDedekindDomain A]
  {X : Scheme.{u}} [IsIntegral X]

/-- The actual prime of the base underneath the actual scheme point. -/
def imagePrime (f : X ⟶ Spec (CommRingCat.of A)) (x : X) : PrimeSpectrum A := f x

omit [IsIntegral X] in
/-- The zero image prime is precisely the actual generic point of the affine base. -/
theorem image_eq_genericPoint_iff (f : X ⟶ Spec (CommRingCat.of A)) (x : X) :
    f x = genericPoint (Spec (CommRingCat.of A)) ↔ (imagePrime f x).asIdeal = ⊥ := by
  rw [genericPoint_eq_bot_of_affine]
  exact ⟨fun h => congrArg PrimeSpectrum.asIdeal h, fun h => PrimeSpectrum.ext h⟩

/-- The base-to-stalk map obtained from the affine germ and the structure morphism. -/
def baseToStalk (f : X ⟶ Spec (CommRingCat.of A)) (x : X) :
    A →+* X.presheaf.stalk x :=
  (f.stalkMap x).hom.comp (StructureSheaf.toStalk A (f x)).hom

/-- The actual affine localization followed by the actual structure-sheaf stalk map. -/
def localizationToStalk (f : X ⟶ Spec (CommRingCat.of A)) (x : X) :
    Localization.AtPrime (imagePrime f x).asIdeal →+* X.presheaf.stalk x :=
  (f.stalkMap x).hom.comp (StructureSheaf.stalkIso A (f x)).toRingHom

/-- The constructed localization map is local. -/
instance localizationToStalk_isLocalHom (f : X ⟶ Spec (CommRingCat.of A)) (x : X) :
    IsLocalHom (localizationToStalk f x) := by
  let e := StructureSheaf.stalkIso A (f x)
  have : IsLocalHom e.toRingHom :=
    isLocalHom_of_leftInverse e.symm.toRingHom e.symm_apply_apply
  exact RingHom.isLocalHom_comp (f.stalkMap x).hom e.toRingHom

omit [IsDedekindDomain A] [IsIntegral X] in
/-- The constructed localization map agrees with the base germ on every base element. -/
@[simp] theorem localizationToStalk_algebraMap
    (f : X ⟶ Spec (CommRingCat.of A)) (x : X) (a : A) :
    localizationToStalk f x (algebraMap A _ a) = baseToStalk f x a := by
  exact congrArg (f.stalkMap x).hom ((StructureSheaf.stalkIso A (f x)).commutes a)

omit [IsDedekindDomain A] [IsIntegral X] in
/-- Base elements outside the actual image prime are units in the actual stalk. -/
theorem baseToStalk_isUnit (f : X ⟶ Spec (CommRingCat.of A)) (x : X)
    (a : A) (ha : a ∉ (imagePrime f x).asIdeal) : IsUnit (baseToStalk f x a) := by
  rw [← localizationToStalk_algebraMap]
  exact (IsLocalization.map_units (Localization.AtPrime (imagePrime f x).asIdeal)
    (⟨a, ha⟩ : (imagePrime f x).asIdeal.primeCompl)).map (localizationToStalk f x)

/-- A nonzero actual image prime is an actual height-one prime of the Dedekind base. -/
def verticalPrime (f : X ⟶ Spec (CommRingCat.of A)) (x : X)
    (hx : (imagePrime f x).asIdeal ≠ ⊥) : IsDedekindDomain.HeightOneSpectrum A :=
  ⟨(imagePrime f x).asIdeal, (imagePrime f x).isPrime, hx⟩

/-- The actual localization map, indexed by the constructed nonzero base prime. -/
def verticalToStalk (f : X ⟶ Spec (CommRingCat.of A)) (x : X)
    (hx : (imagePrime f x).asIdeal ≠ ⊥) :
    Localization.AtPrime (verticalPrime f x hx).asIdeal →+* X.presheaf.stalk x :=
  localizationToStalk f x

/-- Localness of the actual map from the vertical base localization. -/
instance verticalToStalk_isLocalHom (f : X ⟶ Spec (CommRingCat.of A)) (x : X)
    (hx : (imagePrime f x).asIdeal ≠ ⊥) : IsLocalHom (verticalToStalk f x hx) :=
  localizationToStalk_isLocalHom f x

omit [IsDedekindDomain A] [IsIntegral X] in
/-- The vertical localization map extends the genuine base germ. -/
@[simp] theorem verticalToStalk_algebraMap (f : X ⟶ Spec (CommRingCat.of A)) (x : X)
    (hx : (imagePrime f x).asIdeal ≠ ⊥) (a : A) :
    verticalToStalk f x hx (algebraMap A _ a) = baseToStalk f x a :=
  localizationToStalk_algebraMap f x a

variable (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]

-- Expose the affine generic-germ algebra to typeclass search through `Spec`.
local instance : Algebra A (Spec (CommRingCat.of A)).functionField :=
  (StructureSheaf.toStalk A (genericPoint (Spec (CommRingCat.of A)))).hom.toAlgebra

local instance : IsFractionRing A (Spec (CommRingCat.of A)).functionField :=
  functionField_isFractionRing_of_affine (CommRingCat.of A)

/-- The supplied fraction field is canonically the actual generic stalk of `Spec A`. -/
def fractionFieldEquiv : K ≃ₐ[A] (Spec (CommRingCat.of A)).functionField :=
  IsLocalization.algEquiv (nonZeroDivisors A) K _

/-- The actual pullback on generic stalks, expressed on the given fraction field. -/
def constantToFunctionField (f : X ⟶ Spec (CommRingCat.of A)) [IsDominant f] :
    K →+* X.functionField :=
  (functionFieldMap f).comp (fractionFieldEquiv (A := A) K).toRingHom

/-- In the affine base, specialization of any base germ is its generic germ. -/
theorem affine_generic_germ (y : Spec (CommRingCat.of A)) (a : A) :
    algebraMap ((Spec (CommRingCat.of A)).presheaf.stalk y)
      (Spec (CommRingCat.of A)).functionField (StructureSheaf.toStalk A y a) =
        algebraMap A (Spec (CommRingCat.of A)).functionField a := by
  exact ConcreteCategory.congr_hom
    (StructureSheaf.toStalk_stalkSpecializes (genericPoint_specializes y)) a

/-- The constant-field embedding and every actual base-to-stalk map agree in the function field. -/
@[simp] theorem constantToFunctionField_algebraMap
    (f : X ⟶ Spec (CommRingCat.of A)) [IsDominant f] (x : X) (a : A) :
    constantToFunctionField K f (algebraMap A K a) =
      algebraMap (X.presheaf.stalk x) X.functionField (baseToStalk f x a) := by
  change functionFieldMap f (fractionFieldEquiv K (algebraMap A K a)) = _
  rw [(fractionFieldEquiv K).commutes, ← affine_generic_germ (f x) a, functionFieldMap_stalk]
  rfl

omit [IsIntegral X] in
/-- At a point over the zero prime, every nonzero base element is a stalk unit. -/
theorem horizontal_denominator_isUnit (f : X ⟶ Spec (CommRingCat.of A)) (x : X)
    (hx : (imagePrime f x).asIdeal = ⊥) (a : nonZeroDivisors A) :
    IsUnit (baseToStalk f x (a : A)) := by
  apply baseToStalk_isUnit
  rw [hx, Ideal.mem_bot]
  exact nonZeroDivisors.ne_zero a.property

/-- The whole constant field maps to each actual stalk over the zero prime. -/
def horizontalToStalk (f : X ⟶ Spec (CommRingCat.of A)) (x : X)
    (hx : (imagePrime f x).asIdeal = ⊥) : K →+* X.presheaf.stalk x :=
  IsLocalization.lift (horizontal_denominator_isUnit f x hx)

omit [IsIntegral X] in
/-- The horizontal field-to-stalk map extends the genuine base germ. -/
@[simp] theorem horizontalToStalk_algebraMap
    (f : X ⟶ Spec (CommRingCat.of A)) (x : X)
    (hx : (imagePrime f x).asIdeal = ⊥) (a : A) :
    horizontalToStalk K f x hx (algebraMap A K a) = baseToStalk f x a :=
  IsLocalization.lift_eq (horizontal_denominator_isUnit f x hx) a

/-- Horizontal stalk factorization of the canonical constant-field map. -/
theorem horizontalToStalk_compat (f : X ⟶ Spec (CommRingCat.of A)) [IsDominant f]
    (x : X) (hx : (imagePrime f x).asIdeal = ⊥) (a : K) :
    constantToFunctionField K f a =
      algebraMap (X.presheaf.stalk x) X.functionField (horizontalToStalk K f x hx a) := by
  have h : constantToFunctionField K f =
      (algebraMap (X.presheaf.stalk x) X.functionField).comp (horizontalToStalk K f x hx) := by
    apply IsFractionRing.ringHom_ext (A := A)
    intro b
    simp only [RingHom.comp_apply, horizontalToStalk_algebraMap,
      constantToFunctionField_algebraMap K f x]
  exact RingHom.congr_fun h a

/-- Every multiplicative constant unit is the image of an actual horizontal stalk unit. -/
theorem horizontal_fieldUnits (f : X ⟶ Spec (CommRingCat.of A)) [IsDominant f]
    (x : CodimensionOnePoint X) (hx : (imagePrime f x.1).asIdeal = ⊥) (a : Kˣ) :
    Units.map (constantToFunctionField K f).toMonoidHom a =
      x.fieldUnits (Units.map (horizontalToStalk K f x.1 hx).toMonoidHom a) := by
  apply Units.ext
  exact horizontalToStalk_compat K f x.1 hx (a : K)

end AlgebraicGeometry.Scheme.DedekindBase

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/Stalk/DedekindBase.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 e56078d33a4f191c0fd6a04c7615fc5e43c1d0622539d3db75b42e7df6c81632.
Native names and imports replace source wrappers; stated conditions and maps are retained. -/
