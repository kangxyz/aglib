/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.MonogenicResidueExtension
public import Aglib.RingTheory.DiscreteValuationRing.ParameterResidue
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# A prescribed residue element in a same-uniformizer DVR extension

Every actual point from a DVR to a field, with kernel the maximal ideal,
extends to a DVR point realizing any prescribed element of that field.
The algebraic case uses the literal monogenic residue lift, including
inseparable extensions. The transcendental case evaluates the actual
residue fraction field of the one-variable parameter localization.
Both cases preserve the original point and the same natural uniformizer.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace ParameterLocalization

variable (B K : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Field K] [Algebra (ResidueField B) K]

/-- The actual one-variable evaluation is injective at a transcendental
element of the specified residue extension. -/
theorem aeval_singleton_injective_of_transcendental
    (a : K) (ha : Transcendental (ResidueField B) a) :
    Function.Injective ((MvPolynomial.aeval (fun _ : Unit ↦ a) :
      MvPolynomial Unit (ResidueField B) →ₐ[ResidueField B] K).toRingHom) := by
  change Function.Injective (MvPolynomial.aeval (fun _ : Unit ↦ a) :
    MvPolynomial Unit (ResidueField B) →ₐ[ResidueField B] K)
  exact algebraicIndependent_iff_injective_aeval.mp
    ((algebraicIndependent_unique_type_iff
      (R := ResidueField B) (x := fun _ : Unit ↦ a)).mpr ha)

/-- Evaluation at the specified transcendental element extends to the
literal polynomial fraction field. -/
def transcendentalFractionPoint (a : K) (ha : Transcendental (ResidueField B) a) :
    FractionRing (MvPolynomial Unit (ResidueField B)) →+* K :=
  IsFractionRing.lift
    (K := FractionRing (MvPolynomial Unit (ResidueField B)))
    (g := (MvPolynomial.aeval (fun _ : Unit ↦ a) :
      MvPolynomial Unit (ResidueField B) →ₐ[ResidueField B] K).toRingHom)
    (aeval_singleton_injective_of_transcendental B K a ha)

@[simp]
theorem transcendentalFractionPoint_algebraMap
    (a : K) (ha : Transcendental (ResidueField B) a)
    (q : MvPolynomial Unit (ResidueField B)) :
    transcendentalFractionPoint B K a ha
      (algebraMap (MvPolynomial Unit (ResidueField B))
        (FractionRing (MvPolynomial Unit (ResidueField B))) q) =
      MvPolynomial.aeval (fun _ : Unit ↦ a) q :=
  IsFractionRing.lift_algebraMap
    (K := FractionRing (MvPolynomial Unit (ResidueField B)))
    (g := (MvPolynomial.aeval (fun _ : Unit ↦ a) :
      MvPolynomial Unit (ResidueField B) →ₐ[ResidueField B] K).toRingHom)
    (aeval_singleton_injective_of_transcendental B K a ha) q

variable (p : B) [Fact (Irreducible p)]

/-- The actual residue point of the native one-variable parameter DVR. -/
def transcendentalResiduePoint (a : K) (ha : Transcendental (ResidueField B) a) :
    Ring B Unit p →+* K :=
  (transcendentalFractionPoint B K a ha).comp
    ((residueFieldRingEquiv B Unit p).toRingHom.comp (residue (Ring B Unit p)))

/-- The point has the actual maximal ideal as kernel. -/
theorem ker_transcendentalResiduePoint
    (a : K) (ha : Transcendental (ResidueField B) a) :
    RingHom.ker (transcendentalResiduePoint B K p a ha) =
      maximalIdeal (Ring B Unit p) := by
  calc
    RingHom.ker (transcendentalResiduePoint B K p a ha) =
        RingHom.ker ((residueFieldRingEquiv B Unit p).toRingHom.comp
          (residue (Ring B Unit p))) :=
      RingHom.ker_comp_of_injective _
        (f := transcendentalFractionPoint B K a ha)
        (transcendentalFractionPoint B K a ha).injective
    _ = RingHom.ker (residue (Ring B Unit p)) :=
      RingHom.ker_comp_of_injective _ (f := (residueFieldRingEquiv B Unit p).toRingHom)
        (residueFieldRingEquiv B Unit p).injective
    _ = maximalIdeal (Ring B Unit p) := ker_residue

/-- The original coefficient map retains the specified residue-field
embedding. -/
@[simp]
theorem transcendentalResiduePoint_algebraMap
    (a : K) (ha : Transcendental (ResidueField B) a) (b : B) :
    transcendentalResiduePoint B K p a ha (algebraMap B (Ring B Unit p) b) =
      algebraMap (ResidueField B) K (residue B b) := by
  change transcendentalFractionPoint B K a ha
    (residueFieldRingEquiv B Unit p
      (residue (Ring B Unit p)
        (algebraMap (MvPolynomial Unit B) (Ring B Unit p) (MvPolynomial.C b)))) = _
  rw [residueFieldRingEquiv_polynomial, transcendentalFractionPoint_algebraMap,
    MvPolynomial.map_C, MvPolynomial.aeval_C]

/-- The original polynomial variable maps to the prescribed field element. -/
@[simp]
theorem transcendentalResiduePoint_X
    (a : K) (ha : Transcendental (ResidueField B) a) :
    transcendentalResiduePoint B K p a ha
      (algebraMap (MvPolynomial Unit B) (Ring B Unit p) (MvPolynomial.X ())) = a := by
  change transcendentalFractionPoint B K a ha
    (residueFieldRingEquiv B Unit p
      (residue (Ring B Unit p)
        (algebraMap (MvPolynomial Unit B) (Ring B Unit p) (MvPolynomial.X ())))) = a
  rw [residueFieldRingEquiv_polynomial, transcendentalFractionPoint_algebraMap,
    MvPolynomial.map_X, MvPolynomial.aeval_X]

/-- The prescribed transcendental residue is realized in the actual
same-uniformizer parameter localization. -/
theorem mem_range_transcendentalResiduePoint
    (a : K) (ha : Transcendental (ResidueField B) a) :
    a ∈ Set.range (transcendentalResiduePoint B K p a ha) :=
  ⟨algebraMap (MvPolynomial Unit B) (Ring B Unit p) (MvPolynomial.X ()),
    transcendentalResiduePoint_X B K p a ha⟩

end ParameterLocalization

namespace IsDiscreteValuationRing

universe u v

/-- An actual one-element enlargement of a marked DVR. The carrier and
both maps are constructed, and the point square retains the original
map into the specified field. -/
structure ResidueExtension {B : Type u} {K : Type v} [CommRing B] [Field K]
    (p : ℕ) (g : B →+* K) (a : K) where
  /-- The constructed coefficient ring. -/
  ring : CommRingCat.{u}
  /-- The constructed ring is a domain. -/
  isDomain : IsDomain ring
  /-- The constructed ring is a DVR. -/
  isDiscreteValuationRing : @IsDiscreteValuationRing ring _ isDomain
  /-- The actual extension map from the original DVR. -/
  map : B →+* ring
  /-- The actual residue point in the specified field. -/
  point : ring →+* K
  /-- The point restricts to the original point. -/
  point_comp : point.comp map = g
  /-- The original natural coefficient remains a uniformizer. -/
  irreducible : Irreducible (p : ring)
  /-- The point has the actual maximal ideal as its kernel. -/
  ker_point :
    letI : IsDomain ring := isDomain
    letI : IsDiscreteValuationRing ring := isDiscreteValuationRing
    RingHom.ker point = maximalIdeal ring
  /-- The prescribed element is an actual residue of the new ring. -/
  mem_range : a ∈ Set.range point

attribute [instance] ResidueExtension.isDomain ResidueExtension.isDiscreteValuationRing

variable {B : Type u} {K : Type v} [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Field K]

/-- Adjoin any prescribed element of the residue target to a marked DVR,
using its actual simple algebraic extension or its actual one-variable
parameter localization. Inseparable elements are allowed. -/
def residueExtension (p : ℕ) (hp : Irreducible (p : B))
    (g : B →+* K) (hg : RingHom.ker g = maximalIdeal B) (a : K) :
    ResidueExtension p g a := by
  let gbar : ResidueField B →+* K :=
    Ideal.Quotient.lift (maximalIdeal B) g (fun _ hx ↦ hg.symm.le hx)
  let : Algebra (ResidueField B) K := gbar.toAlgebra
  have hcoeff (b : B) : algebraMap (ResidueField B) K (residue B b) = g b := rfl
  by_cases ha : IsAlgebraic (ResidueField B) a
  · let L := IntermediateField.adjoin (ResidueField B) ({a} : Set K)
    let b : PowerBasis (ResidueField B) L := IntermediateField.adjoin.powerBasis ha.isIntegral
    let : Algebra B L := ((algebraMap (ResidueField B) L).comp (residue B)).toAlgebra
    let : IsScalarTower B (ResidueField B) L := IsScalarTower.of_algebraMap_eq' rfl
    let D := PowerBasis.ResidueLiftRing B L b
    let : IsDomain D := PowerBasis.residueLift_isDomain B L b
    let : IsDiscreteValuationRing D := PowerBasis.residueLift_isDiscreteValuationRing B L b
    let ψ : D →+* K := L.val.toRingHom.comp (PowerBasis.residueLiftPoint B L b).toRingHom
    refine {
      ring := CommRingCat.of D
      isDomain := inferInstance
      isDiscreteValuationRing := inferInstance
      map := algebraMap B D
      point := ψ
      point_comp := ?_
      irreducible := ?_
      ker_point := ?_
      mem_range := ?_ }
    · ext x
      change L.val (PowerBasis.residueLiftPoint B L b (algebraMap B D x)) = g x
      rw [PowerBasis.residueLiftPoint_algebraMap]
      exact (L.val.commutes (residue B x)).trans (hcoeff x)
    · simpa only [map_natCast] using
        PowerBasis.residueLift_irreducible_algebraMap B L b (p : B) hp
    · change RingHom.ker ψ = maximalIdeal D
      rw [show ψ = L.val.toRingHom.comp (PowerBasis.residueLiftPoint B L b).toRingHom from rfl,
        RingHom.ker_comp_of_injective _ (f := L.val.toRingHom) L.val.injective,
        PowerBasis.ker_residueLiftPoint]
      exact (PowerBasis.residueLift_maximalIdeal B L b).symm
    · refine ⟨AdjoinRoot.root (PowerBasis.residueLiftPolynomial B L b), ?_⟩
      change L.val (PowerBasis.residueLiftPoint B L b
        (AdjoinRoot.root (PowerBasis.residueLiftPolynomial B L b))) = a
      rw [PowerBasis.residueLiftPoint_root]
      rfl
  · have ht : Transcendental (ResidueField B) a := ha
    let : Fact (Irreducible (p : B)) := ⟨hp⟩
    let D := ParameterLocalization.Ring B Unit (p : B)
    let : IsDiscreteValuationRing D := ParameterLocalization.isDiscreteValuationRing B Unit (p : B)
    refine {
      ring := CommRingCat.of D
      isDomain := inferInstance
      isDiscreteValuationRing := inferInstance
      map := algebraMap B D
      point := ParameterLocalization.transcendentalResiduePoint B K (p : B) a ht
      point_comp := ?_
      irreducible := ?_
      ker_point := ParameterLocalization.ker_transcendentalResiduePoint B K (p : B) a ht
      mem_range := ParameterLocalization.mem_range_transcendentalResiduePoint B K (p : B) a ht }
    · ext x
      exact (ParameterLocalization.transcendentalResiduePoint_algebraMap B K (p : B) a ht x).trans
        (hcoeff x)
    · simpa only [map_natCast] using
        ParameterLocalization.uniformizer_irreducible B Unit (p : B)

end IsDiscreteValuationRing
