/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.FiniteCartierReduced
public import Aglib.AlgebraicGeometry.Curves.Abel.PointClasses
public import Aglib.AlgebraicGeometry.Curves.Picard.EffectiveClass
public import Aglib.AlgebraicGeometry.Curves.PointDivisor.Sections
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Dimension

/-!
# Support of an actual rank-one effective Cartier divisor

The original ideal-inclusion divisor has positive coefficient precisely
at the image points of the actual finite Cartier immersion. Its native
weighted coefficient/stalk-dimension formula retains nilpotent lengths.
When h0 of the positive line bundle is one, uniqueness of its effective
representative identifies this divisor without any chart choice in the
statement.

Consequently a rational point belongs to the original Cartier divisor
exactly when the positive bundle twisted by the ORIGINAL point ideal has
a nonzero global section. This is the curve linear-system support input
for theta incidence; it assumes no theta, Jacobian or polarization data.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Scheme Scheme.Hom Scheme.Modules Scheme.Modules.Hom Scheme.Modules.Invertible
open Scheme.Cohomology Scheme.Hom.FiniteFlat

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel

open Divisors Picard Picard.DivisorClass Picard.DivisorInverse Picard.Degree
open Picard.RationalTrivialization Picard.Degree.FiniteSupportLengths FiniteCartierDegree

section Coefficients

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k)
  [IsIntegral X.left] [IsNoetherian X.left]
  [∀ x : ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)]
  [LocallyOfFiniteType X.hom]
  {Z : Scheme.{u}} (i : Z ⟶ X.left) [IsClosedImmersion i] [IsFinite (i ≫ X.hom)]
  (hI : IsLocallyRankOne X.left (idealModule i))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Original finite Cartier support is positivity of the unique effective
representative, using actual source stalks rather than a point count. -/
theorem finiteCartier_mem_range_iff_coefficient_pos
    (hdim : topologicalKrullDim X.left ≤ 1) (D : Divisor X.left) (heff : ∀ x, 0 ≤ D x)
    (hclass : divisorToPicard X.left hdim D =
      classOf X.left (dualLineBundle X.left ⟨idealModule i, hI⟩))
    (h0 : Module.finrank k (moduleCohomology k X
      (dualLineBundle X.left ⟨idealModule i, hI⟩).val 0) = 1) (x : ClosedPoint X.left) :
    x.val ∈ Set.range i ↔ 0 < D x := by
  let I : LineBundle X.left := ⟨idealModule i, hI⟩
  let c₀ := localChart X.left I.val I.property (genericPoint X.left)
  let : Nonempty c₀.1 := ⟨⟨genericPoint X.left, c₀.2.property⟩⟩
  let E := MapDivisors.mapDivisor X.left I (idealInclusion i) c₀.1 c₀.2.val
  have hEeff : ∀ x, 0 ≤ E x :=
    MapDivisors.mapDivisor_nonneg X.left I (idealInclusion i) c₀.1 c₀.2.val
  have hEclass : divisorToPicard X.left hdim E = classOf X.left (dualLineBundle X.left I) :=
    MapDivisors.divisorToPicard_mapDivisor X.left I (idealInclusion i) c₀.1 c₀.2.val hdim
  obtain ⟨e⟩ := (class_eq_iff X.left (divisorLineBundle X.left hdim E)
    (dualLineBundle X.left I)).mp hEclass
  have hE0 : Module.finrank k (moduleCohomology k X (divisorSheaf X.left E) 0) = 1 :=
    (moduleCohomologyIso X e 0).finrank_eq.trans h0
  have hED : E = D := effective_divisor_eq_of_class_eq_of_h0_one
    X hdim E D hEeff heff (hEclass.trans hclass.symm) hE0
  constructor
  · rintro ⟨y, hy⟩
    let q := i ≫ X.hom
    let : Algebra k Γ(Z, ⊤) := coordinateAlgebra k (Over.mk q)
    let : Module.Finite k Γ(Z, ⊤) := finite_coordinate_algebra k Z q
    let : IsArtinianRing Γ(Z, ⊤) := IsArtinianRing.of_finite k Γ(Z, ⊤)
    obtain ⟨r, hr⟩ := IsArtinianRing.isNilpotent_nilradical (R := Γ(Z, ⊤))
    have hr' : _root_.nilradical Γ(Z, ⊤) ^ (r + 1) = ⊥ := by
      rw [pow_succ, hr, zero_mul, Ideal.zero_eq_bot]
    obtain ⟨m, rfl⟩ := CartierSum.point_surjective k Z q y
    let y := FiniteStalks.point k Z q m
    let : Algebra k (Z.presheaf.stalk y) := stalkConstantsAlgebra Z q y
    have eStalk : Algebra.ArtinComponent Γ(Z, ⊤) r m ≃ₐ[k] Z.presheaf.stalk y :=
      FiniteStalks.factorStalkEquiv k Z q r hr' m
    have : Module.Finite k (Z.presheaf.stalk y) :=
      Module.Finite.of_surjective eStalk.toLinearEquiv.toLinearMap eStalk.surjective
    have hx : IsClosed ({i y} : Set X.left) := (CartierSum.closedPoint k Z q i m).property
    have hxx : (⟨i y, hx⟩ : ClosedPoint X.left) = x := Subtype.ext hy
    let c := localChart X.left (idealModule i) hI (i y)
    have hc := CartierLocal.ideal_mapDivisor_weighted_coefficient X.left i hI X.hom
      c₀.1 c₀.2.val c.1 c.2.val y c.2.property hx
    change E ⟨i y, hx⟩ * weight X.left X.hom ⟨i y, hx⟩ =
      (Module.finrank k (Z.presheaf.stalk y) : ℤ) at hc
    rw [hED, weight_eq_one, mul_one, hxx] at hc
    have hp : 0 < Module.finrank k (Z.presheaf.stalk y) := Module.finrank_pos
    omega
  · intro hpos
    by_contra hnot
    have hz := CartierLocal.ideal_mapDivisor_eq_zero_of_not_mem_range
      X.left i hI c₀.1 c₀.2.val x hnot
    change E x = 0 at hz
    rw [hED] at hz
    omega

end Coefficients

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Properties X)
  {Z : Scheme.{u}} (i : Z ⟶ X.left) [IsClosedImmersion i] [IsFinite (i ≫ X.hom)]
  (hI : IsLocallyRankOne X.left (idealModule i))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A rational point is in the original rank-one effective Cartier divisor
exactly when its positive bundle twisted by the original point ideal has
a nonzero actual global section. -/
theorem finiteCartier_mem_range_iff_nonzero_point_twist
    (h0 : Module.finrank k (moduleCohomology k X
      (dualLineBundle X.left ⟨idealModule i, hI⟩).val 0) = 1)
    (q : Spec (.of k) ⟶ X.left) (hq : q ≫ X.hom = 𝟙 _) :
    q (IsLocalRing.closedPoint k) ∈ Set.range i ↔
      ∃ s : (tensorLineBundle X.left (dualLineBundle X.left ⟨idealModule i, hI⟩)
        (PointDivisor.idealLineBundle X hX q hq)).val.val.obj (op ⊤), s ≠ 0 := by
  classical
  let := hX.proper
  let := PointDivisor.isIntegral_of_properties X hX
  let := curveProperties_isNoetherian hX
  let (x : ClosedPoint X.left) := PointDivisor.isDiscreteValuationRing_stalk X hX x
  let hd := (curveProperties_dimension smoothFieldDimension hX).le
  let L := dualLineBundle X.left ⟨idealModule i, hI⟩
  let M := tensorLineBundle X.left L (PointDivisor.idealLineBundle X hX q hq)
  let x := PointDivisor.closedPoint X q hq
  let A : Divisor X.left := Finsupp.single x 1
  have : Nontrivial (moduleCohomology k X L.val 0) := Module.nontrivial_of_finrank_eq_succ h0
  obtain ⟨s, hs⟩ := exists_ne (0 : moduleCohomology k X L.val 0)
  have hs' : moduleH0Equiv X L.val s ≠ 0 := fun hz =>
    hs ((moduleH0Equiv X L.val).injective (hz.trans (moduleH0Equiv X L.val).map_zero.symm))
  obtain ⟨D, heff, hclass⟩ := exists_effective_divisor_class_of_nonzero_section
    X.left hd L (moduleH0Equiv X L.val s) hs'
  have hpoint := PointDivisor.positiveLineBundle_class_eq_pointDivisor X hX q hq hd
  change -classOf X.left (PointDivisor.idealLineBundle X hX q hq) =
    divisorToPicard X.left hd A at hpoint
  have hpointIdeal : classOf X.left (PointDivisor.idealLineBundle X hX q hq) =
      -divisorToPicard X.left hd A := neg_eq_iff_eq_neg.mp hpoint
  have hM : divisorToPicard X.left hd (D - A) = classOf X.left M := by
    rw [map_sub, hclass]
    change classOf X.left L - divisorToPicard X.left hd A =
      classOf X.left (tensorLineBundle X.left L (PointDivisor.idealLineBundle X hX q hq))
    rw [classOf_tensor, hpointIdeal, sub_eq_add_neg]
  have hmem := finiteCartier_mem_range_iff_coefficient_pos X i hI hd D heff hclass h0 x
  change x.val ∈ Set.range i ↔ ∃ s : M.val.val.obj (op ⊤), s ≠ 0
  rw [hmem]
  constructor
  · intro hx
    have hDminus : ∀ y, 0 ≤ (D - A : Divisor X.left) y := by
      intro y
      by_cases hy : y = x
      · subst y
        simp only [A, Finsupp.sub_apply, Finsupp.single_eq_same]
        omega
      · simpa only [A, Finsupp.sub_apply, Finsupp.single_eq_of_ne hy, sub_zero] using heff y
    exact (exists_nonzero_section_iff_effective_class X.left hd M).mpr ⟨D - A, hDminus, hM⟩
  · intro hsM
    obtain ⟨E, hEeff, hEclass⟩ :=
      (exists_nonzero_section_iff_effective_class X.left hd M).mp hsM
    have hAeff : ∀ y, 0 ≤ A y := by
      intro y
      by_cases hy : y = x
      · simp only [A, hy, Finsupp.single_eq_same]; omega
      · simp only [A, Finsupp.single_eq_of_ne hy, le_refl]
    have hsumEff : ∀ y, 0 ≤ (E + A : Divisor X.left) y := fun y => by
      change 0 ≤ E y + A y
      exact add_nonneg (hEeff y) (hAeff y)
    have hsumClass : divisorToPicard X.left hd (E + A) = divisorToPicard X.left hd D := by
      rw [map_add, hEclass, ← hM, map_sub, sub_add_cancel]
    obtain ⟨e⟩ := (class_eq_iff X.left (divisorLineBundle X.left hd D) L).mp hclass
    have hD0 : Module.finrank k (moduleCohomology k X (divisorSheaf X.left D) 0) = 1 :=
      (moduleCohomologyIso X e 0).finrank_eq.trans h0
    have hDE : D = E + A := effective_divisor_eq_of_class_eq_of_h0_one
      X hd D (E + A) heff hsumEff hsumClass.symm hD0
    have hx := congrArg (fun B : Divisor X.left => B x) hDE
    change D x = E x + A x at hx
    simp only [A, Finsupp.single_eq_same] at hx
    have := hEeff x
    omega

end AlgebraicGeometry.Scheme.OverField.Curve.Abel
