/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.FiniteCartierDegree
public import Aglib.AlgebraicGeometry.Curves.Picard.EffectiveClass.Uniqueness

/-!
# Reduced finite Cartier divisors from a simple rank-one positive class

Use the divisor of the original Cartier ideal inclusion, with its generic
chart chosen only inside the proof. The actual map-divisor coefficient is
the dimension of the original source stalk, with its structural field
action and residue-field weight. A simple effective representative and
h0=1 identify this divisor uniquely. Over an algebraically closed field
every nonempty source stalk then has dimension one and is reduced.

No point count is substituted for scheme length. The original finite
scheme and original stalks are retained, including the empty divisor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Scheme Scheme.Hom Scheme.Modules Scheme.Modules.Hom Scheme.Modules.Invertible
open Scheme.Cohomology

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.FiniteCartierDegree.MapDivisors

open Divisors Picard.DivisorInverse Picard.DivisorClass Picard.RationalTrivialization

variable (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
  [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
  (L : LineBundle X)
  (φ : (show X.Modules from L.val) ⟶
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf)) [Mono φ]
  (U₀ : X.Opens) [Nonempty U₀]
  (e₀ : L.val.over U₀ ≅ SheafOfModules.unit (X.ringCatSheaf.over U₀))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The divisor of the actual line-bundle inclusion is effective because
its original local generator images are regular sections. -/
theorem mapDivisor_nonneg (x : ClosedPoint X) : 0 ≤ mapDivisor X L φ U₀ e₀ x := by
  let c := localChart X L.val L.property x.val
  let : Nonempty c.1 := ⟨⟨x.val, c.2.property⟩⟩
  rw [mapDivisor_coefficient X L φ U₀ e₀ c.1 c.2.val x c.2.property]
  exact (order_nonneg_iff_mem_stalk X x.val _).mpr
    ⟨X.presheaf.germ c.1 x.val c.2.property
        (φ.val.app (op c.1) (chartGenerator X L.val c.1 c.2.val)),
      Scheme.algebraMap_germ_eq_germToFunctionField X c.2.property _⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The effective map divisor represents the positive bundle, the dual
of the original included line bundle. -/
theorem divisorToPicard_mapDivisor (hdim : topologicalKrullDim X ≤ 1) :
    divisorToPicard X hdim (mapDivisor X L φ U₀ e₀) = classOf X (dualLineBundle X L) := by
  rw [mapDivisor, map_sub, divisorToPicard_principal, zero_sub, classOf_dual]
  exact congrArg Neg.neg (Quotient.sound
    ⟨(toDivisorIso X L.val L.property U₀ e₀ hdim).symm⟩)

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.FiniteCartierDegree.MapDivisors

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel

open Divisors Picard.DivisorClass Picard.DivisorInverse Picard.Degree
open Picard.RationalTrivialization Picard.Degree.FiniteSupportLengths FiniteCartierDegree
open Scheme.Hom.FiniteFlat

private theorem isReduced_of_field_finrank_one
    (K B : Type*) [Field K] [CommRing B] [Nontrivial B] [Algebra K B]
    (h : Module.finrank K B = 1) : _root_.IsReduced B := by
  constructor
  intro z hz
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one h (one_ne_zero : (1 : B) ≠ 0) z
  have hza : algebraMap K B a = z := by simpa only [Algebra.smul_def, mul_one] using ha
  obtain ⟨m, hm⟩ := hz
  have ha0 : a ^ m = 0 := (algebraMap K B).injective (by
    rw [map_pow, hza, hm, map_zero])
  rw [← hza, eq_zero_of_pow_eq_zero ha0, map_zero]

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k)
  [IsIntegral X.left] [IsNoetherian X.left]
  [∀ x : ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)]
  [LocallyOfFiniteType X.hom]
  {D : Scheme.{u}} (i : D ⟶ X.left) [IsClosedImmersion i] [IsFinite (i ≫ X.hom)]
  (hI : IsLocallyRankOne X.left (idealModule i))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A finite Cartier divisor is reduced when its actual positive bundle
has h0=1 and the same class as a simple effective divisor. All generic
charts and Artinian component choices remain internal to the proof. -/
theorem isReduced_of_positive_class_simple_of_h0_one
    (hdim : topologicalKrullDim X.left ≤ 1) (E : Divisor X.left)
    (heff : ∀ x, 0 ≤ E x) (hsimple : ∀ x, E x = 0 ∨ E x = 1)
    (hclass : divisorToPicard X.left hdim E =
      classOf X.left (dualLineBundle X.left ⟨idealModule i, hI⟩))
    (h0 : Module.finrank k (moduleCohomology k X
      (dualLineBundle X.left ⟨idealModule i, hI⟩).val 0) = 1) : IsReduced D := by
  let I : LineBundle X.left := ⟨idealModule i, hI⟩
  let c₀ := localChart X.left I.val I.property (genericPoint X.left)
  let : Nonempty c₀.1 := ⟨⟨genericPoint X.left, c₀.2.property⟩⟩
  let Z := MapDivisors.mapDivisor X.left I (idealInclusion i) c₀.1 c₀.2.val
  have hZeff : ∀ x, 0 ≤ Z x :=
    MapDivisors.mapDivisor_nonneg X.left I (idealInclusion i) c₀.1 c₀.2.val
  have hZclass : divisorToPicard X.left hdim Z = classOf X.left (dualLineBundle X.left I) :=
    MapDivisors.divisorToPicard_mapDivisor X.left I (idealInclusion i) c₀.1 c₀.2.val hdim
  obtain ⟨e⟩ := (class_eq_iff X.left (divisorLineBundle X.left hdim Z)
    (dualLineBundle X.left I)).mp hZclass
  have hZ0 : Module.finrank k (moduleCohomology k X (divisorSheaf X.left Z) 0) = 1 :=
    (moduleCohomologyIso X e 0).finrank_eq.trans h0
  have hZE : Z = E := Picard.effective_divisor_eq_of_class_eq_of_h0_one
    X hdim Z E hZeff heff (hZclass.trans hclass.symm) hZ0
  let q := i ≫ X.hom
  let : Algebra k Γ(D, ⊤) := coordinateAlgebra k (Over.mk q)
  let : Module.Finite k Γ(D, ⊤) := finite_coordinate_algebra k D q
  let : IsArtinianRing Γ(D, ⊤) := IsArtinianRing.of_finite k Γ(D, ⊤)
  obtain ⟨r, hr⟩ := IsArtinianRing.isNilpotent_nilradical (R := Γ(D, ⊤))
  have hr' : _root_.nilradical Γ(D, ⊤) ^ (r + 1) = ⊥ := by
    rw [pow_succ, hr, zero_mul, Ideal.zero_eq_bot]
  have hstalk (y : D) : _root_.IsReduced (D.presheaf.stalk y) := by
    obtain ⟨m, rfl⟩ := CartierSum.point_surjective k D q y
    let y := FiniteStalks.point k D q m
    let : Algebra k (D.presheaf.stalk y) := stalkConstantsAlgebra D q y
    have eStalk : Algebra.ArtinComponent Γ(D, ⊤) r m ≃ₐ[k] D.presheaf.stalk y :=
      FiniteStalks.factorStalkEquiv k D q r hr' m
    have : Module.Finite k (D.presheaf.stalk y) :=
      Module.Finite.of_surjective eStalk.toLinearEquiv.toLinearMap eStalk.surjective
    have hx : IsClosed ({i y} : Set X.left) := (CartierSum.closedPoint k D q i m).property
    let c := localChart X.left (idealModule i) hI (i y)
    have hc := CartierLocal.ideal_mapDivisor_weighted_coefficient X.left i hI X.hom
      c₀.1 c₀.2.val c.1 c.2.val y c.2.property hx
    change Z ⟨i y, hx⟩ * weight X.left X.hom ⟨i y, hx⟩ =
      (Module.finrank k (D.presheaf.stalk y) : ℤ) at hc
    rw [hZE, weight_eq_one, mul_one] at hc
    have hp : 0 < Module.finrank k (D.presheaf.stalk y) := Module.finrank_pos
    have hdimone : Module.finrank k (D.presheaf.stalk y) = 1 := by
      rcases hsimple ⟨i y, hx⟩ with hz | h1
      · rw [hz] at hc
        omega
      · exact_mod_cast hc.symm.trans h1
    exact isReduced_of_field_finrank_one k (D.presheaf.stalk y) hdimone
  let (y : D) : _root_.IsReduced (D.presheaf.stalk y) := hstalk y
  exact isReduced_of_isReduced_stalk D

end AlgebraicGeometry.Scheme.OverField.Curve.Abel
