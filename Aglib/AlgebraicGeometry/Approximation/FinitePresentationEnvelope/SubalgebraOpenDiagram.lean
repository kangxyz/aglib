/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.OpenLocalizationRange
public import Aglib.RingTheory.FiniteType.FilteredSubalgebra
public import Aglib.RingTheory.FiniteType.LocalizationSubalgebra
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered

/-!
# Finite-subalgebra diagrams preserving actual open overlaps

A finite compatible family of denominators describes the images of a diagram
of open immersions into spectra. At each ring stage retain the finitely
generated integer subalgebras containing these denominators and inducing
isomorphisms on their principal localizations. These subalgebras are cofinal
when the original open schemes are locally of finite type over the integers.

The original open schemes are reindexed, not replaced. Their composites with
the actual spectral inclusion maps are open immersions with the prescribed
principal-open images. Consequently every transition square is cartesian.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

attribute [local instance] ULift.algebra'

/-- A principal open contained in the image of an arithmetic finite-type
open scheme has a finite-type integer localization ring. -/
theorem finiteType_away_of_arithmetic_open
    {R : CommRingCat.{u}} {W : Scheme.{u}} (e : W ⟶ Spec R)
    [IsOpenImmersion e]
    [LocallyOfFiniteType (specULiftZIsTerminal.from W)]
    (r : R) (hr : PrimeSpectrum.basicOpen r ≤ e.opensRange) :
    Algebra.FiniteType ℤ (Localization.Away r) := by
  let a : Spec (CommRingCat.of (Localization.Away r)) ⟶ Spec R :=
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
  have ha : Set.range a ⊆ Set.range e := by
    change a.opensRange ≤ e.opensRange
    rw [Hom.opensRange_localizationAway]
    exact hr
  let q := IsOpenImmersion.lift e a ha
  have hq : q ≫ e = a := IsOpenImmersion.lift_fac e a ha
  have : IsOpenImmersion (q ≫ e) := by rw [hq]; infer_instance
  have : IsOpenImmersion q := IsOpenImmersion.of_comp q e
  have hfin : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) (Localization.Away r)))) := by
    have heq : Spec.map (CommRingCat.ofHom
        (algebraMap (ULift.{u} ℤ) (Localization.Away r))) =
        q ≫ specULiftZIsTerminal.from W := specULiftZIsTerminal.hom_ext _ _
    rw [heq]
    infer_instance
  have hring := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hfin
  change (algebraMap (ULift.{u} ℤ) (Localization.Away r)).FiniteType at hring
  have hz : (Int.castRingHom (ULift.{u} ℤ)).FiniteType :=
    RingHom.FiniteType.of_surjective _ fun z ↦ ⟨z.down, by ext; simp⟩
  have hcomp := hring.comp hz
  have heq : (algebraMap (ULift.{u} ℤ) (Localization.Away r)).comp
      (Int.castRingHom (ULift.{u} ℤ)) = algebraMap ℤ (Localization.Away r) :=
    Subsingleton.elim _ _
  rw [heq] at hcomp
  exact RingHom.finiteType_algebraMap.mp hcomp

namespace FinitePresentationEnvelope.SubalgebraOpenDiagram

open CommRingCat.FilteredSubalgebra

variable {I : Type u} [Category.{u} I] (F : I ⥤ CommRingCat.{u})
  {L : Type u} (h : ∀ i, L → F.obj i)

/-- Eligibility retains the denominators and the bijectivity of the actual
localized subalgebra inclusions. -/
def Eligible (i : I) (A : Subalgebra ℤ (F.obj i)) : Prop :=
  ∃ hh : ∀ l, h i l ∈ A, ∀ l,
    Function.Bijective (Localization.awayMap A.val.toRingHom (⟨h i l, hh l⟩ : A))

/-- The native dependent finite-subalgebra index, retaining actual base arrows. -/
abbrev Index := CommRingCat.FilteredSubalgebra.Index F (Eligible F h)

/-- The denominator viewed in its eligible finite subalgebra. -/
def denominator (X : Index F h) (l : L) : X.algebra :=
  ⟨h X.base l, X.eligible.choose l⟩

@[simp]
theorem denominator_coe (X : Index F h) (l : L) :
    (denominator F h X l : F.obj X.base) = h X.base l := rfl

/-- The original localized inclusion is bijective at every eligible object. -/
theorem denominator_awayMap_bijective (X : Index F h) (l : L) :
    Function.Bijective
      (Localization.awayMap X.algebra.val.toRingHom (denominator F h X l)) :=
  X.eligible.choose_spec l

variable (W : Iᵒᵖ ⥤ Scheme.{u}) (e : W ⟶ F.op ⋙ Scheme.Spec)
  [∀ i, IsOpenImmersion (e.app i)]
  (he : ∀ i, (e.app (op i)).opensRange = ⨆ l, PrimeSpectrum.basicOpen (h i l))

include e he in
/-- Arithmetic finite type makes the stronger localized eligibility cofinal
among all finite sets at each original ring stage. -/
theorem eligible_cofinal [Finite L]
    [∀ i, LocallyOfFiniteType (specULiftZIsTerminal.from (W.obj i))] :
    Cofinal F (Eligible F h) := by
  intro i s
  have hfin (l : L) : Algebra.FiniteType ℤ (Localization.Away (h i l)) :=
    finiteType_away_of_arithmetic_open (e.app (op i)) (h i l) (by
      rw [he i]
      exact le_iSup (fun l ↦ PrimeSpectrum.basicOpen (h i l)) l)
  obtain ⟨A, hA, hs, hh, hbij⟩ :=
    IsLocalization.Away.exists_fg_subalgebra_map_bijective (K := ℤ) (h i) s
  exact ⟨A, hA, ⟨hh, hbij⟩, hs⟩

include e he in
/-- The native eligible dependent index is filtered. -/
theorem index_isFiltered [IsFiltered I] [Finite L]
    [∀ i, LocallyOfFiniteType (specULiftZIsTerminal.from (W.obj i))] :
    IsFiltered (Index F h) :=
  CommRingCat.FilteredSubalgebra.isFiltered (eligible_cofinal F h W e he)

include e he in
/-- Forgetting the eligible finite subalgebra is a final functor. -/
theorem forget_final [IsFiltered I] [Finite L]
    [∀ i, LocallyOfFiniteType (specULiftZIsTerminal.from (W.obj i))] :
    (CommRingCat.FilteredSubalgebra.forget F (Eligible F h)).Final :=
  CommRingCat.FilteredSubalgebra.forget_final (eligible_cofinal F h W e he)

/-- The original overlap diagram is only reindexed, retaining all its objects
and actual transition maps. -/
def overlap : (Index F h)ᵒᵖ ⥤ Scheme.{u} :=
  (CommRingCat.FilteredSubalgebra.forget F (Eligible F h)).op ⋙ W

/-- The actual spectra of eligible finite subalgebras. -/
def affine : (Index F h)ᵒᵖ ⥤ Scheme.{u} :=
  (ringDiagram F (Eligible F h)).op ⋙ Scheme.Spec

/-- Applying spectrum to the actual subalgebra cocone retains the original
ring spectrum as its literal point. -/
def affineCone (c : Cocone F) : Cone (affine F h) :=
  Scheme.Spec.mapCone (ringCocone F (Eligible F h) c).op

/-- Every affine cone projection is the actual composite inclusion on rings. -/
@[simp]
theorem affineCone_π_app (c : Cocone F) (X : (Index F h)ᵒᵖ) :
    (affineCone F h c).π.app X = Spec.map
      (CommRingCat.ofHom X.unop.algebra.val.toRingHom ≫ c.ι.app X.unop.base) := rfl

include e he in
/-- The eligible finite-subalgebra spectra retain the original ring limit. -/
def affineConeIsLimit [IsFiltered I] [Finite L]
    [∀ i, LocallyOfFiniteType (specULiftZIsTerminal.from (W.obj i))]
    (c : Cocone F) (hc : IsColimit c) : IsLimit (affineCone F h c) :=
  isLimitOfPreserves Scheme.Spec
    (ringCoconeIsColimit (eligible_cofinal F h W e he) hc).op

omit [∀ i, IsOpenImmersion (e.app i)] in
include e in
/-- The overlap map is the original open immersion followed by the spectrum
of the literal subalgebra inclusion. -/
def toAffine : overlap F h W ⟶ affine F h := by
  let a := Functor.whiskerLeft
    (CommRingCat.FilteredSubalgebra.forget F (Eligible F h)).op e
  let b := Functor.whiskerRight
    (NatTrans.op (CommRingCat.FilteredSubalgebra.inclusion F (Eligible F h))) Scheme.Spec
  exact a ≫ b

omit [∀ i, IsOpenImmersion (e.app i)] in
/-- The component formula exposes the original scheme and literal ring map. -/
@[simp]
theorem toAffine_app (X : (Index F h)ᵒᵖ) :
    (toAffine F h W e).app X = e.app (op X.unop.base) ≫
      Spec.map (CommRingCat.ofHom X.unop.algebra.val.toRingHom) := rfl

include he in
/-- Every original overlap maps openly into its eligible affine stage. -/
theorem toAffine_isOpenImmersion (X : (Index F h)ᵒᵖ) :
    IsOpenImmersion ((toAffine F h W e).app X) :=
  isOpenImmersion_comp_of_awayMap_bijective (e.app (op X.unop.base))
    (CommRingCat.ofHom X.unop.algebra.val.toRingHom)
    (denominator F h X.unop) (he X.unop.base)
    (denominator_awayMap_bijective F h X.unop)

/-- The exact principal-open image of each original overlap component. -/
theorem toAffine_opensRange (X : (Index F h)ᵒᵖ) :
    let := toAffine_isOpenImmersion F h W e he X
    ((toAffine F h W e).app X).opensRange =
      ⨆ l, PrimeSpectrum.basicOpen (denominator F h X.unop l) :=
  opensRange_comp_of_awayMap_bijective (e.app (op X.unop.base))
    (CommRingCat.ofHom X.unop.algebra.val.toRingHom)
    (denominator F h X.unop) (he X.unop.base)
    (denominator_awayMap_bijective F h X.unop)

/-- Compatible original denominators remain compatible under the actual
restricted ring maps. -/
theorem map_denominator
    (hh : ∀ {i j} (f : i ⟶ j) l, (F.map f).hom (h i l) = h j l)
    {X Y : Index F h} (f : X ⟶ Y) (l : L) :
    f.ringHom F (Eligible F h) (denominator F h X l) = denominator F h Y l :=
  Subtype.ext (hh f.base l)

include he in
/-- All actual transition squares of the reindexed overlap maps are cartesian. -/
theorem toAffine_equifibered
    (hh : ∀ {i j} (f : i ⟶ j) l, (F.map f).hom (h i l) = h j l) :
    (toAffine F h W e).Equifibered := by
  let (X : (Index F h)ᵒᵖ) := toAffine_isOpenImmersion F h W e he X
  intro X Y f
  apply IsOpenImmersion.isPullback _ _ _ _
    ((toAffine F h W e).naturality f).symm
  rw [toAffine_opensRange F h W e he, toAffine_opensRange F h W e he,
    Hom.preimage_iSup]
  congr 1
  funext l
  change PrimeSpectrum.basicOpen
      (f.unop.ringHom F (Eligible F h) (denominator F h Y.unop l)) = _
  rw [map_denominator F h hh]

include he in
/-- The original overlap-to-affine cone square is cartesian whenever its
literal projection triangle and principal-image formula hold. -/
theorem toAffine_cone_isPullback (c : Cocone F) (X : (Index F h)ᵒᵖ)
    {Z : Scheme.{u}} (g₀ : Z ⟶ Spec c.pt) [IsOpenImmersion g₀]
    (p : Z ⟶ W.obj (op X.unop.base))
    (H : p ≫ e.app (op X.unop.base) = g₀ ≫ Spec.map (c.ι.app X.unop.base))
    (hg₀ : g₀.opensRange = ⨆ l,
      PrimeSpectrum.basicOpen ((c.ι.app X.unop.base).hom (h X.unop.base l))) :
    IsPullback p g₀ ((toAffine F h W e).app X) ((affineCone F h c).π.app X) := by
  let := toAffine_isOpenImmersion F h W e he X
  change IsPullback p g₀ ((toAffine F h W e).app X)
    (Spec.map (CommRingCat.ofHom X.unop.algebra.val.toRingHom ≫ c.ι.app X.unop.base))
  apply isPullback_of_principal_opensRange p g₀ ((toAffine F h W e).app X)
    (CommRingCat.ofHom X.unop.algebra.val.toRingHom ≫ c.ι.app X.unop.base)
    (denominator F h X.unop)
  · change g₀ ≫ Spec.map
        (CommRingCat.ofHom X.unop.algebra.val.toRingHom ≫ c.ι.app X.unop.base) =
      p ≫ (e.app (op X.unop.base) ≫
        Spec.map (CommRingCat.ofHom X.unop.algebra.val.toRingHom))
    rw [Spec.map_comp, ← Category.assoc, ← H, Category.assoc]
  · exact toAffine_opensRange F h W e he X
  · exact hg₀

/-- Every eligible affine stage is quasi-compact. -/
instance affine_compact (X : (Index F h)ᵒᵖ) : CompactSpace ((affine F h).obj X) :=
  inferInstanceAs (CompactSpace (Spec (CommRingCat.of X.unop.algebra)))

/-- Eligible affine stages are locally of finite type over the arithmetic base. -/
instance affine_finiteType (X : (Index F h)ᵒᵖ) :
    LocallyOfFiniteType (specULiftZIsTerminal.from ((affine F h).obj X)) := by
  have : Algebra.FiniteType (ULift.{u} ℤ) X.unop.algebra :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ULift.{u} ℤ) X.unop.algebra
  have heq : specULiftZIsTerminal.from ((affine F h).obj X) =
      Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) X.unop.algebra)) :=
    specULiftZIsTerminal.hom_ext _ _
  rw [heq]
  apply HasRingHomProperty.Spec_iff.mpr
  exact RingHom.finiteType_algebraMap.mpr inferInstance

end FinitePresentationEnvelope.SubalgebraOpenDiagram
end AlgebraicGeometry.Scheme
