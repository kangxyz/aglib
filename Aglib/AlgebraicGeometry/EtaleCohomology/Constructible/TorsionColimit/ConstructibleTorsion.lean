/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Basic
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.CoefficientRepresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteSetRepresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Torsion.Basic
public import Aglib.AlgebraicGeometry.Morphisms.Finite.PointLifts
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Actual constructible coefficients have finite geometric stalks

An original field-valued point in the image of a locally closed immersion lifts
through that immersion. Its pullback is a nonempty immersion into a field
spectrum; its image is the whole spectrum, so it is a surjective closed immersion
into a reduced scheme and hence an isomorphism. This retains the original
factorization, including when the ambient or stratum scheme is nonreduced.

The published inverse-image stalk comparison then transfers finite local
constancy on the actual strata to finiteness of every original geometric stalk.
Thus affine-local constructibility implies internal torsion on every scheme.
No Noetherian, quasi-compactness, coefficient-order or cohomology premise is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u

attribute [local instance] hasSheafifyLarge

/-- A field-valued point in the image of an actual immersion factors through
that immersion, with its original structure morphism unchanged. -/
theorem exists_fieldPoint_lift_of_mem_range {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsImmersion j] {K : Type u} [Field K] (η : Spec (.of K) ⟶ X)
    (hη : η default ∈ Set.range j) : ∃ ζ : Spec (.of K) ⟶ Y, ζ ≫ j = η := by
  obtain ⟨y, hy⟩ := hη
  obtain ⟨z, _, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := j) (g := η)
    y (default : Spec (.of K)) hy
  let p : pullback j η ⟶ Spec (.of K) := pullback.snd j η
  have hp : Surjective p := ⟨fun t => ⟨z, hz.trans (Subsingleton.elim _ t)⟩⟩
  have : IsClosedImmersion p := IsClosedImmersion.of_isPreimmersion p (by
    rw [Set.range_eq_univ.mpr hp.surj]
    exact isClosed_univ)
  have : IsIso p := isIso_of_isClosedImmersion_of_surjective p
  refine ⟨inv p ≫ pullback.fst j η, ?_⟩
  calc
    (inv p ≫ pullback.fst j η) ≫ j = inv p ≫ (p ≫ η) := by
      rw [Category.assoc, pullback.condition]
    _ = η := by simp

/-- Actual finite locally constant abelian sheaves have finite original
geometric stalks, by their produced finite-etale group representation. -/
theorem finite_geometricStalk_of_finiteLocallyConstant {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsFiniteLocallyConstant F)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ X) :
    Finite ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1}) |>.obj F) := by
  let r := CoefficientRepresentation.ofFiniteLocallyConstant F (stacks03RV X) hF
  have : IsFinite r.group.X.hom := r.finite
  have : Etale r.group.X.hom := r.etale
  have : IsCommMonObj r.group.X := r.commutative
  have : Finite (Over.mk η ⟶ r.group.X) :=
    Scheme.Finite.finite_hom_over_point r.group.X.hom η
  have : Finite (RepresentedSections r.group (Over.mk η)) := inferInstance
  let e := ((pointSmallEtale η).sheafFiber.mapIso r.iso).symm ≪≫
    representedFiberIso η r.group
  exact Finite.of_injective e.hom (ConcreteCategory.bijective_of_isIso e.hom).injective

/-- Finiteness transfers through the published original inverse-image stalk
isomorphism, with the literal composite field-valued point. -/
theorem finite_geometricStalk_of_inverseImage {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (η : Spec (.of Ω) ⟶ Y)
    (h : Finite ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1}) |>.obj
      ((inverseImage f).obj F))) :
    Finite ((pointSmallEtale (η ≫ f)).sheafFiber
      (A := AddCommGrpCat.{u + 1}) |>.obj F) := by
  have : Finite ((inverseImage f ⋙ (pointSmallEtale η).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj F) := h
  let e := (StalkInverseImage.stalkUnitNatIso f η).app F
  exact Finite.of_injective e.hom (ConcreteCategory.bijective_of_isIso e.hom).injective

/-- A genuine constructible partition gives finite original geometric stalks.
The proof uses the original immersion of the stratum containing the point. -/
theorem finite_geometricStalk_of_partition {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) (t : ConstructiblePartition F)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ X) :
    Finite ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1}) |>.obj F) := by
  obtain ⟨i, y, hy⟩ := t.covers (η default)
  have : IsImmersion (t.inclusion i) := t.immersion i
  obtain ⟨ζ, hζ⟩ := exists_fieldPoint_lift_of_mem_range (t.inclusion i) η ⟨y, hy⟩
  rw [← hζ]
  exact finite_geometricStalk_of_inverseImage (t.inclusion i) F ζ
    (finite_geometricStalk_of_finiteLocallyConstant _ (t.locally_constant i) ζ)

/-- The affine-local constructible predicate implies finiteness at every
original geometric stalk, without a global finite-partition hypothesis. -/
theorem finite_geometricStalk_of_isConstructible {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsConstructible F)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ X) :
    Finite ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1}) |>.obj F) := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show η default ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨t⟩ := hF ⟨U, hU⟩
  obtain ⟨ζ, hζ⟩ := exists_fieldPoint_lift_of_mem_range U.ι η
    ⟨⟨η default, hxU⟩, rfl⟩
  rw [← hζ]
  exact finite_geometricStalk_of_inverseImage U.ι F ζ
    (finite_geometricStalk_of_partition _ t ζ)

/-- Every actual constructible abelian sheaf is internally torsion. -/
theorem isTorsion_of_isConstructible {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsConstructible F) : IsTorsion X F := by
  apply isTorsion_of_geometricStalks
  intro Ω _ _ η
  have := finite_geometricStalk_of_isConstructible F hF η
  exact isAddTorsion_of_finite

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
