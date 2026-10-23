/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveBundle.RankTwoExtension.Complement
public import Aglib.AlgebraicGeometry.Modules.Invertible.Locus
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Conormal.Frames
public import Aglib.AlgebraicGeometry.Modules.Differentials.Diagonal.Affine
public import Aglib.AlgebraicGeometry.Modules.InternalHom.GluingIsomorphisms
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.OpenImmersion
public import Aglib.AlgebraicGeometry.IdealSheaf.Modules.ConormalMap
public import Aglib.RingTheory.Ideal.RegularPrincipal
public import Mathlib.RingTheory.Polynomial.Ideal
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Actual local ideals and conormal frames of the quotient section

The original polynomial coordinate generates the actual kernel of evaluation
at zero over every commutative coefficient ring. Its native ideal-module and
conormal frames transport through the original open chart and cartesian bundle
squares. The overlap coordinate calculation retains its square-ideal error.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Polynomial
open Scheme.Modules Scheme.Modules.Differentials Scheme.Hom Scheme.ProjectiveLine
open Scheme.Modules.Invertible
open scoped Polynomial TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveBundle.RankTwoExtension

namespace Conormal

/-- The actual global ideal section corresponding to an original spectral kernel element. -/
def affineIdealElement {A B : CommRingCat.{u}} (σ : A ⟶ B)
    (x : RingHom.ker σ.hom) : (idealModule (Spec.map σ)).val.obj (op ⊤) :=
  (affineIdealIso σ).hom.val.app (op ⊤)
    (tilde.toOpen (ModuleCat.of A (RingHom.ker σ.hom)) ⊤ x)

private theorem affineIdealElement_inclusion {A B : CommRingCat.{u}} (σ : A ⟶ B)
    (x : RingHom.ker σ.hom) :
    (idealInclusion (Spec.map σ)).val.app (op ⊤) (affineIdealElement σ x) =
      (Scheme.ΓSpecIso A).inv x.val := by
  have h := congrArg (fun q => q.val.app (op ⊤)
    (tilde.toOpen (ModuleCat.of A (RingHom.ker σ.hom)) ⊤ x))
    (affineIdealIso_hom_inclusion σ)
  refine h.trans ?_
  exact ConcreteCategory.congr_hom
    (tilde.toOpen_map_app (ModuleCat.ofHom (RingHom.ker σ.hom).subtype) ⊤) x

/-- Original spectral ideal elements commute with the canonical ideal pushforward map. -/
theorem affineIdealElement_map {A B C D : CommRingCat.{u}}
    (σ : A ⟶ B) (τ : C ⟶ D) (b : A ⟶ C) (a : Spec D ⟶ Spec B)
    (hs : a ≫ Spec.map σ = Spec.map τ ≫ Spec.map b)
    (x : RingHom.ker σ.hom) (y : RingHom.ker τ.hom) (hy : y.val = b x.val) :
    (idealPushforwardMap (Spec.map σ) (Spec.map τ) (Spec.map b) a hs).val.app
      (op ⊤) (affineIdealElement σ x) = affineIdealElement τ y := by
  have hi : Function.Injective ((idealInclusion (Spec.map τ)).val.app (op ⊤)) := by
    intro v w hvw
    apply (idealSectionsEquiv (Spec.map τ) ⊤).injective
    apply Subtype.ext
    simpa only [idealSectionsEquiv_val] using hvw
  apply hi
  have hn := congrArg (fun q => q.val.app (op ⊤) (affineIdealElement σ x))
    (idealPushforwardMap_inclusion (Spec.map σ) (Spec.map τ)
      (Spec.map b) a hs)
  change (idealInclusion (Spec.map τ)).val.app (op ⊤)
      ((idealPushforwardMap (Spec.map σ) (Spec.map τ) (Spec.map b)
        a hs).val.app (op ⊤) (affineIdealElement σ x)) =
    (Spec.map b).appTop ((idealInclusion (Spec.map σ)).val.app (op ⊤)
      (affineIdealElement σ x)) at hn
  rw [hn, affineIdealElement_inclusion, affineIdealElement_inclusion, hy]
  exact congrArg (fun q : A ⟶ Γ(Spec C, ⊤) => q x.val)
    (Scheme.ΓSpecIso_inv_naturality b).symm

/-- The actual global conormal section induced by an original ideal section through pullback. -/
def conormalElement {D X : Scheme.{u}} (i : D ⟶ X)
    (m : (idealModule i).val.obj (op ⊤)) :
    ((Modules.pullback i).obj (idealModule i)).val.obj (op ⊤) :=
  ((pullbackPushforwardAdjunction i).unit.app (idealModule i)).val.app (op ⊤) m

/-- The canonical map between actual pulled-back kernel ideals for `i = i' ≫ b`,
using the identity on their common source. -/
abbrev conormalMap {D X Y : Scheme.{u}}
    (i : D ⟶ X) (i' : D ⟶ Y) (b : Y ⟶ X) (h : i = i' ≫ b) :
    (Modules.pullback i).obj (idealModule i) ⟶
      (Modules.pullback i').obj (idealModule i') :=
  Scheme.Hom.conormalMap i i' b h

/-- The actual spectral conormal section induced by an original kernel element. -/
def affineConormalElement {A B : CommRingCat.{u}} (σ : A ⟶ B)
    (x : RingHom.ker σ.hom) :
    ((Modules.pullback (Spec.map σ)).obj (idealModule (Spec.map σ))).val.obj (op ⊤) :=
  conormalElement (Spec.map σ) (affineIdealElement σ x)

private theorem affineConormalElement_eq_of_class_eq {A B : CommRingCat.{u}}
    (σ : A ⟶ B) (hσ : Function.Surjective σ) (x y : RingHom.ker σ.hom)
    (h : relativeConormalAffineClass (𝟙 A) σ hσ x =
      relativeConormalAffineClass (𝟙 A) σ hσ y) :
    affineConormalElement σ x = affineConormalElement σ y := by
  let e := relativeConormalAffineIdealPullbackIso (𝟙 A) σ hσ
  have he : Function.Injective (e.hom.val.app (op ⊤)) := by
    intro x y hxy
    have hh := congrArg (e.inv.val.app (op ⊤)) hxy
    exact (congrArg (fun q => q.val.app (op ⊤) x) e.hom_inv_id).symm.trans
      (hh.trans (congrArg (fun q => q.val.app (op ⊤) y) e.hom_inv_id))
  apply he
  exact (Diagonal.affineConormalIso_unit_top σ hσ x).trans
    ((congrArg (tilde.toOpen (relativeConormalAffineModule (𝟙 A) σ hσ) ⊤)
      ((Diagonal.affineClassMap_apply σ hσ x).trans
        (h.trans (Diagonal.affineClassMap_apply σ hσ y).symm))).trans
      (Diagonal.affineConormalIso_unit_top σ hσ y).symm)

/-- The canonical common-source conormal map preserves the original pulled-back ideal section. -/
theorem conormalMap_unit_top {D X Y : Scheme.{u}}
    (i : D ⟶ X) (i' : D ⟶ Y) (b : Y ⟶ X) (h : i = i' ≫ b)
    (m : (idealModule i).val.obj (op ⊤)) :
    (conormalMap i i' b h).val.app (op ⊤) (conormalElement i m) =
      conormalElement i' ((idealPushforwardMap i i' b (𝟙 D)
        (by simpa only [Category.id_comp] using h)).val.app (op ⊤) m) := by
  dsimp only [conormalMap, conormalElement]
  change ((Modules.pullback i').map (idealPullbackMap i i' b (𝟙 D)
      (by simpa only [Category.id_comp] using h))).val.app (op ⊤)
    (((pullbackComp i' b).inv.app (idealModule i)).val.app (op ⊤)
      (((pullbackCongr h).hom.app (idealModule i)).val.app (op ⊤)
        (((pullbackPushforwardAdjunction i).unit.app (idealModule i)).val.app (op ⊤) m))) = _
  rw [Diagonal.pullbackCongr_unit_top, Diagonal.pullbackComp_inv_unit_top,
    Diagonal.pullback_map_unit_top, Diagonal.idealPullbackMap_unit_top]

/-- A computed original ideal pushforward gives the same actual conormal image. -/
theorem conormalMap_element {D X Y : Scheme.{u}}
    (i : D ⟶ X) (i' : D ⟶ Y) (b : Y ⟶ X) (h : i = i' ≫ b)
    (m : (idealModule i).val.obj (op ⊤)) (n : (idealModule i').val.obj (op ⊤))
    (hmn : (idealPushforwardMap i i' b (𝟙 D)
      (by simpa only [Category.id_comp] using h)).val.app (op ⊤) m = n) :
    (conormalMap i i' b h).val.app (op ⊤) (conormalElement i m) =
      conormalElement i' n :=
  (conormalMap_unit_top i i' b h m).trans (congrArg (conormalElement i') hmn)

/-- The canonical map on actual spectral conormals with the same original quotient spectrum. -/
def affineConormalMap {A B C : CommRingCat.{u}}
    (σ : A ⟶ B) (τ : C ⟶ B) (b : A ⟶ C)
    (hs : Spec.map σ = Spec.map τ ≫ Spec.map b) :
    (Modules.pullback (Spec.map σ)).obj (idealModule (Spec.map σ)) ⟶
      (Modules.pullback (Spec.map τ)).obj (idealModule (Spec.map τ)) :=
  conormalMap (Spec.map σ) (Spec.map τ) (Spec.map b) hs

variable (R : Type u) [CommRing R]

/-- The original zero section in the polynomial affine chart. -/
abbrev coordinateSection : Spec (.of R) ⟶ Spec (.of R[X]) :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))

/-- The original coordinate is regular even over a nonreduced coefficient ring. -/
theorem coordinate_regular : IsSMulRegular R[X] (Polynomial.X : R[X]) :=
  Polynomial.isRegular_X.left.isSMulRegular

/-- The original evaluation kernel is the ideal of the original coordinate. -/
theorem coordinate_kernel :
    RingHom.ker (Polynomial.evalRingHom (0 : R)) = Ideal.span {Polynomial.X} := by
  simpa only [Polynomial.C_0, sub_zero] using Polynomial.ker_evalRingHom (0 : R)

/-- The actual spectral kernel ideal has the original coordinate as singleton basis. -/
def coordinateIdealIso :
    idealModule (coordinateSection R) ≅ SheafOfModules.unit (Spec (.of R[X])).ringCatSheaf :=
  (affineIdealIso (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))).symm ≪≫
    tildeBasisIso _ (Ideal.regularPrincipalIdealBasis _ (Polynomial.X : R[X])
      (coordinate_regular R) (coordinate_kernel R)) ≪≫ coproductUniqueIso _

/-- The original coordinate gives a weakly regular singleton over any coefficient ring. -/
theorem coordinate_weaklyRegular :
    RingTheory.Sequence.IsWeaklyRegular R[X] [(Polynomial.X : R[X])] :=
  (RingTheory.Sequence.isWeaklyRegular_singleton_iff R[X] (Polynomial.X : R[X])).mpr
    (coordinate_regular R)

/-- The singleton coordinate list generates the original evaluation kernel. -/
theorem coordinate_kernel_list :
    Ideal.ofList [(Polynomial.X : R[X])] = RingHom.ker (Polynomial.evalRingHom (0 : R)) := by
  rw [Ideal.ofList_singleton, coordinate_kernel]

/-- The native conormal of evaluation at zero is framed by its original coordinate class. -/
def coordinateConormalIso :
    (Modules.pullback (coordinateSection R)).obj (idealModule (coordinateSection R)) ≅
      SheafOfModules.unit (Spec (.of R)).ringCatSheaf :=
  relativeConormalAffineGeometricFreeIso
    (CommRingCat.ofHom (Polynomial.C : R →+* R[X]))
    (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))
    (fun r => ⟨Polynomial.C r, Polynomial.eval_C⟩)
    [Polynomial.X] (coordinate_weaklyRegular R) (coordinate_kernel_list R) ≪≫
      coproductUniqueIso (fun _ : ULift.{u} (Fin 1) =>
        SheafOfModules.unit (Spec (.of R)).ringCatSheaf)

/-- The original coordinate-zero chart square for infinity is cartesian. -/
theorem infinity_chart_square :
    IsPullback (𝟙 (Spec (.of R))) (coordinateSection R)
      (Sections.infinity R) (chart R 1) :=
  IsPullback.of_horiz_isIso_mono ⟨by simp [Sections.infinity, Sections.chartSection]⟩

/-- The actual projective infinity ideal restricts to the actual zero-section kernel ideal. -/
def infinityIdealChartIso :
    (Modules.pullback (chart R 1)).obj (idealModule (Sections.infinity R)) ≅
      idealModule (coordinateSection R) := by
  let h : (𝟙 (Spec (.of R))) ≫ Sections.infinity R = coordinateSection R ≫ chart R 1 := by
    simp [Sections.infinity, Sections.chartSection]
  let : IsIso (idealPullbackMap (Sections.infinity R) (coordinateSection R)
      (chart R 1) (𝟙 _) h) :=
    idealPullbackMap_isIso_of_isOpenImmersion _ _ _ _ h (infinity_chart_square R)
  exact asIso (idealPullbackMap (Sections.infinity R) (coordinateSection R)
    (chart R 1) (𝟙 _) h)

/-- The actual conormal of the original infinity section has its coordinate-class frame. -/
def infinityConormalIso :
    (Modules.pullback (Sections.infinity R)).obj (idealModule (Sections.infinity R)) ≅
      SheafOfModules.unit (Spec (.of R)).ringCatSheaf :=
  ((pullbackComp (coordinateSection R) (chart R 1)).app
    (idealModule (Sections.infinity R))).symm ≪≫
    (Modules.pullback (coordinateSection R)).mapIso (infinityIdealChartIso R) ≪≫
    coordinateConormalIso R

/-- The actual kernel ideal of a map with empty source is the entire structure module. -/
def emptyIdealIso {D Y : Scheme.{u}} (j : D ⟶ Y) [IsEmpty D] :
    idealModule j ≅ SheafOfModules.unit Y.ringCatSheaf := by
  have hj : structureModuleMap j = 0 := by
    apply Scheme.Modules.hom_ext
    intro U
    ext x
    change j.app U x = 0
    have hU : j ⁻¹ᵁ U = ⊥ := by
      ext y
      exact isEmptyElim y
    have : Subsingleton Γ(D, j ⁻¹ᵁ U) := by
      rw [hU]
      infer_instance
    exact Subsingleton.elim _ _
  let : IsIso (idealInclusion j) := kernel.ι_of_zero hj
  exact asIso (idealInclusion j)

/-- Off infinity the actual kernel ideal restricts to the unit ideal. -/
def infinityIdealChartZeroIso :
    (Modules.pullback (chart R 0)).obj (idealModule (Sections.infinity R)) ≅
      SheafOfModules.unit (Spec (.of R[X])).ringCatSheaf := by
  let q := Sections.infinity R
  let j := chart R 0
  have hdisjoint : Disjoint (Set.range q) (Set.range j) := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ hx
    exact Sections.infinity_not_mem_chart_zero R x hx
  let : IsEmpty (Limits.pullback q j : Scheme.{u}) := Scheme.isEmpty_pullback_iff.mpr hdisjoint
  let h : Limits.pullback.fst q j ≫ q = Limits.pullback.snd q j ≫ j :=
    Limits.pullback.condition
  let : IsIso (idealPullbackMap q (Limits.pullback.snd q j) j
      (Limits.pullback.fst q j) h) :=
    idealPullbackMap_isIso_of_isOpenImmersion _ _ _ _ h (IsPullback.of_hasPullback q j)
  exact asIso (idealPullbackMap q (Limits.pullback.snd q j) j
    (Limits.pullback.fst q j) h) ≪≫ emptyIdealIso (Limits.pullback.snd q j)

private theorem unit_locallyRankOne (Y : Scheme.{u}) :
    IsLocallyRankOne Y (SheafOfModules.unit Y.ringCatSheaf) :=
  isLocallyRankOne_of_iso Y (coproductUniqueIso _) (trivialLineBundle Y).property

/-- The actual infinity kernel ideal is locally free of rank one on the whole projective line. -/
theorem infinityIdeal_locallyRankOne :
    IsLocallyRankOne (projectiveP1 R) (idealModule (Sections.infinity R)) := by
  apply isLocallyRankOne_of_forall_isLocallyRankOneAt
  intro z
  obtain ⟨j, x, rfl⟩ := chart_covered R z
  refine ⟨Spec (.of R[X]), chart R j, inferInstance, ⟨x, rfl⟩, ?_⟩
  fin_cases j
  · exact isLocallyRankOne_of_iso _ (infinityIdealChartZeroIso R).symm
      (unit_locallyRankOne _)
  · exact isLocallyRankOne_of_iso _
      ((infinityIdealChartIso R) ≪≫ coordinateIdealIso R).symm (unit_locallyRankOne _)

variable {A : Type u} [CommRing A]

/-- The coordinate change has an explicit error divisible by the square of the original
coordinate. This calculation requires only the displayed inverse relation. -/
theorem coordinate_change_error (x t z : A) (hz : (1 + t * x) * z = 1) :
    x * z - x = -(t * z) * x ^ 2 := by
  calc
    x * z - x = x * z - x * ((1 + t * x) * z) := by rw [hz, mul_one]
    _ = -(t * z) * x ^ 2 := by ring

/-- The same actual coordinate class is preserved modulo its square ideal. -/
theorem coordinate_change_mod_square (x t z : A) (hz : (1 + t * x) * z = 1) :
    Ideal.Quotient.mk ((Ideal.span {x}) ^ 2) (x * z) =
      Ideal.Quotient.mk ((Ideal.span {x}) ^ 2) x := by
  apply Ideal.Quotient.eq.mpr
  rw [coordinate_change_error x t z hz]
  apply Ideal.mul_mem_left
  simp only [pow_two]
  exact Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_singleton x))
    (Ideal.subset_span (Set.mem_singleton x))

/-- The exact coordinate change preserves its class in the native extension conormal. -/
theorem coordinate_change_cotangent {K B : Type u} [CommRing K] [CommRing B] [Algebra K B]
    (P : Algebra.Extension K B) (x : P.ker) (t z : P.Ring)
    (hz : (1 + t * x.val) * z = 1) :
    Algebra.Extension.Cotangent.mk (z • x) = Algebra.Extension.Cotangent.mk x := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (Algebra.Extension.Cotangent.mk_eq_zero_iff _).mpr
  change z * x.val - x.val ∈ P.ker ^ 2
  rw [mul_comm z, coordinate_change_error x.val t z hz]
  apply Ideal.mul_mem_left
  simp only [pow_two]
  exact Ideal.mul_mem_mul x.property x.property

/-- The original overlap ring for the unipotent coordinate change near infinity. -/
abbrev overlapRing (t : R) := Sections.translationOverlapRing R t

/-- The literal changed coordinate in the original principal localization. -/
def overlapCoordinate (t : R) : overlapRing R t :=
  Sections.translationOverlapCoordinate R t

private theorem overlapDenominator_algebraMap (t : R) :
    algebraMap R[X] (overlapRing R t) (Sections.translationOverlapPolynomial R t) =
      1 + algebraMap R[X] (overlapRing R t) (Polynomial.C t) *
        algebraMap R[X] (overlapRing R t) Polynomial.X := by
  change algebraMap R[X] (overlapRing R t)
    (1 + Polynomial.C t * (Polynomial.X : R[X])) = _
  rw [map_add, map_one, map_mul]

/-- In the actual overlap localization the error is the original square-coordinate multiple. -/
theorem overlapCoordinate_error (t : R) :
    overlapCoordinate R t - algebraMap R[X] (overlapRing R t) Polynomial.X =
      -(algebraMap R[X] (overlapRing R t) (Polynomial.C t) *
        IsLocalization.Away.invSelf (Sections.translationOverlapPolynomial R t)) *
        (algebraMap R[X] (overlapRing R t) Polynomial.X) ^ 2 := by
  apply coordinate_change_error
  have h := IsLocalization.Away.mul_invSelf (S := overlapRing R t)
    (Sections.translationOverlapPolynomial R t)
  rw [overlapDenominator_algebraMap] at h
  exact h

/-- Evaluation at the original zero section extends to the actual overlap localization. -/
def overlapZero (t : R) : overlapRing R t →+* R :=
  IsLocalization.Away.lift (Sections.translationOverlapPolynomial R t)
    (g := Polynomial.evalRingHom (0 : R)) (by simp [Sections.translationOverlapPolynomial])

@[simp] theorem overlapZero_algebraMap (t : R) (p : R[X]) :
    overlapZero R t (algebraMap R[X] (overlapRing R t) p) = Polynomial.eval 0 p :=
  IsLocalization.Away.lift_eq _ _ p

/-- The actual overlap inverse restricts to one on the original zero section. -/
@[simp] theorem overlapZero_invSelf (t : R) :
    overlapZero R t
      (IsLocalization.Away.invSelf (Sections.translationOverlapPolynomial R t)) = 1 := by
  have hden : overlapZero R t (algebraMap R[X] (overlapRing R t)
      (Sections.translationOverlapPolynomial R t)) = 1 := by
    rw [overlapZero_algebraMap]
    simp only [Sections.translationOverlapPolynomial, Polynomial.eval_add, Polynomial.eval_one,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, mul_zero, add_zero]
  have h := congrArg (overlapZero R t)
    (IsLocalization.Away.mul_invSelf (S := overlapRing R t)
      (Sections.translationOverlapPolynomial R t))
  rw [map_mul, hden, map_one, one_mul] at h
  exact h

@[simp] theorem overlapZero_coordinate (t : R) :
    overlapZero R t (overlapCoordinate R t) = 0 := by
  change overlapZero R t
    (algebraMap R[X] (overlapRing R t) Polynomial.X *
      IsLocalization.Away.invSelf (Sections.translationOverlapPolynomial R t)) = 0
  rw [map_mul, overlapZero_algebraMap, Polynomial.eval_X, zero_mul]

/-- The original transformed-coordinate map preserves the original zero section. -/
theorem overlapZero_translationMap (t : R) :
    (overlapZero R t).comp (Sections.translationOverlapMap R t) =
      Polynomial.evalRingHom (0 : R) := by
  apply Polynomial.ringHom_ext
  · intro r
    change overlapZero R t
      (Polynomial.eval₂ ((algebraMap R[X] (overlapRing R t)).comp Polynomial.C)
        (overlapCoordinate R t) (Polynomial.C r)) = Polynomial.eval 0 (Polynomial.C r)
    rw [Polynomial.eval₂_C]
    exact overlapZero_algebraMap R t (Polynomial.C r)
  · change overlapZero R t
      (Polynomial.eval₂ ((algebraMap R[X] (overlapRing R t)).comp Polynomial.C)
        (overlapCoordinate R t) Polynomial.X) = Polynomial.eval 0 Polynomial.X
    rw [Polynomial.eval₂_X, Polynomial.eval_X]
    exact overlapZero_coordinate R t

/-- The original zero section inside the exact unipotent overlap. -/
abbrev overlapZeroSection (t : R) : Spec (.of R) ⟶ Spec (.of (overlapRing R t)) :=
  Spec.map (CommRingCat.ofHom (overlapZero R t))

/-- The overlap section retains its original polynomial-chart factorization. -/
@[reassoc] theorem overlapZeroSection_chart (t : R) :
    overlapZeroSection R t ≫
      Spec.map (CommRingCat.ofHom (algebraMap R[X] (overlapRing R t))) = coordinateSection R := by
  rw [overlapZeroSection, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (overlapZero_algebraMap R t)

/-- The same actual zero section also factors through the original changed-coordinate map. -/
@[reassoc] theorem overlapZeroSection_changedChart (t : R) :
    overlapZeroSection R t ≫
      Spec.map (CommRingCat.ofHom (Sections.translationOverlapMap R t)) = coordinateSection R := by
  rw [overlapZeroSection, ← Spec.map_comp]
  exact congrArg (fun φ : R[X] →+* R => Spec.map (CommRingCat.ofHom φ))
    (overlapZero_translationMap R t)

/-- The actual polynomial zero ideal base-changes to the actual zero ideal on the overlap. -/
def overlapIdealChartIso (t : R) :
    (Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R[X] (overlapRing R t))))).obj
      (idealModule (coordinateSection R)) ≅ idealModule (overlapZeroSection R t) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap R[X] (overlapRing R t)))
  have h : (𝟙 (Spec (.of R))) ≫ coordinateSection R = overlapZeroSection R t ≫ b := by
    simpa only [Category.id_comp] using (overlapZeroSection_chart R t).symm
  let : IsIso (idealPullbackMap (coordinateSection R) (overlapZeroSection R t) b (𝟙 _) h) :=
    idealPullbackMap_isIso_of_isOpenImmersion _ _ _ _ h
      (IsPullback.of_horiz_isIso_mono ⟨h⟩)
  exact asIso (idealPullbackMap (coordinateSection R) (overlapZeroSection R t) b (𝟙 _) h)

private theorem overlapZero_surjective (t : R) : Function.Surjective (overlapZero R t) := by
  intro r
  exact ⟨algebraMap R[X] (overlapRing R t) (Polynomial.C r), by simp⟩

private def originalKernelCoordinate : RingHom.ker (Polynomial.evalRingHom (0 : R)) :=
  ⟨Polynomial.X, by simp⟩

private def overlapOriginalKernelCoordinate (t : R) : RingHom.ker (overlapZero R t) :=
  ⟨algebraMap R[X] (overlapRing R t) Polynomial.X, by simp⟩

private def overlapChangedKernelCoordinate (t : R) : RingHom.ker (overlapZero R t) :=
  ⟨overlapCoordinate R t, by simp⟩

private theorem overlapConormalElement_eq (t : R) :
    affineConormalElement (CommRingCat.ofHom (overlapZero R t))
      (overlapChangedKernelCoordinate R t) =
      affineConormalElement (CommRingCat.ofHom (overlapZero R t))
        (overlapOriginalKernelCoordinate R t) := by
  let σ := CommRingCat.ofHom (overlapZero R t)
  let : Algebra (overlapRing R t) R := (overlapZero R t).toAlgebra
  let P := relativeConormalAffineExtension (𝟙 (CommRingCat.of (overlapRing R t))) σ
    (overlapZero_surjective R t)
  apply affineConormalElement_eq_of_class_eq σ (overlapZero_surjective R t)
  change Algebra.Extension.Cotangent.mk (show P.ker from overlapChangedKernelCoordinate R t) =
    Algebra.Extension.Cotangent.mk (show P.ker from overlapOriginalKernelCoordinate R t)
  have he : (show P.ker from overlapChangedKernelCoordinate R t) =
      (IsLocalization.Away.invSelf (Sections.translationOverlapPolynomial R t) :
        overlapRing R t) • (show P.ker from overlapOriginalKernelCoordinate R t) := by
    apply Subtype.ext
    exact mul_comm _ _
  rw [he]
  apply coordinate_change_cotangent P (show P.ker from overlapOriginalKernelCoordinate R t)
    (algebraMap R[X] (overlapRing R t) (Polynomial.C t))
  have h := IsLocalization.Away.mul_invSelf (S := overlapRing R t)
    (Sections.translationOverlapPolynomial R t)
  rw [overlapDenominator_algebraMap] at h
  exact h

/-- The canonical conormal map through the original polynomial overlap inclusion. -/
def overlapOriginalConormalMap (t : R) :
    (Modules.pullback (coordinateSection R)).obj (idealModule (coordinateSection R)) ⟶
      (Modules.pullback (overlapZeroSection R t)).obj (idealModule (overlapZeroSection R t)) :=
  affineConormalMap (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))
    (CommRingCat.ofHom (overlapZero R t))
    (CommRingCat.ofHom (algebraMap R[X] (overlapRing R t))) (overlapZeroSection_chart R t).symm

/-- The canonical conormal map through the original translated polynomial overlap. -/
def overlapChangedConormalMap (t : R) :
    (Modules.pullback (coordinateSection R)).obj (idealModule (coordinateSection R)) ⟶
      (Modules.pullback (overlapZeroSection R t)).obj (idealModule (overlapZeroSection R t)) :=
  affineConormalMap (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))
    (CommRingCat.ofHom (overlapZero R t))
    (CommRingCat.ofHom (Sections.translationOverlapMap R t))
    (overlapZeroSection_changedChart R t).symm

private def GlobalSectionImagesEq {X : Scheme.{u}} {M N : X.Modules}
    (f g : M ⟶ N) (m : M.val.obj (op ⊤)) : Prop :=
  f.val.app (op ⊤) m = g.val.app (op ⊤) m

private theorem conormalMap_elements_eq {D X Y : Scheme.{u}}
    (i : D ⟶ X) (i' : D ⟶ Y) (b₁ b₀ : Y ⟶ X)
    (h₁ : i = i' ≫ b₁) (h₀ : i = i' ≫ b₀)
    (m : (idealModule i).val.obj (op ⊤))
    (n₁ n₀ : (idealModule i').val.obj (op ⊤))
    (hm₁ : (idealPushforwardMap i i' b₁ (𝟙 D)
      (by simpa only [Category.id_comp] using h₁)).val.app (op ⊤) m = n₁)
    (hm₀ : (idealPushforwardMap i i' b₀ (𝟙 D)
      (by simpa only [Category.id_comp] using h₀)).val.app (op ⊤) m = n₀)
    (hn : conormalElement i' n₁ = conormalElement i' n₀) :
    GlobalSectionImagesEq (conormalMap i i' b₁ h₁) (conormalMap i i' b₀ h₀)
      (conormalElement i m) :=
  (conormalMap_element i i' b₁ h₁ m n₁ hm₁).trans
    (hn.trans (conormalMap_element i i' b₀ h₀ m n₀ hm₀).symm)

private theorem overlapChangedKernelCoordinate_image (t : R) :
    (overlapChangedKernelCoordinate R t).val =
      Sections.translationOverlapMap R t (originalKernelCoordinate R).val := by
  change overlapCoordinate R t = Sections.translationOverlapMap R t Polynomial.X
  simp only [Sections.translationOverlapMap, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X]
  rfl

private theorem overlapChangedIdealElement_image (t : R) :
    (idealPushforwardMap (coordinateSection R) (overlapZeroSection R t)
      (Spec.map (CommRingCat.ofHom (Sections.translationOverlapMap R t))) (𝟙 (Spec (.of R)))
      (by simpa only [Category.id_comp] using
        (overlapZeroSection_changedChart R t).symm)).val.app (op ⊤)
      (affineIdealElement (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))
        (originalKernelCoordinate R)) =
    affineIdealElement (CommRingCat.ofHom (overlapZero R t))
      (overlapChangedKernelCoordinate R t) :=
  affineIdealElement_map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))
    (CommRingCat.ofHom (overlapZero R t))
    (CommRingCat.ofHom (Sections.translationOverlapMap R t)) (𝟙 (Spec (.of R)))
    (by simpa only [Category.id_comp] using (overlapZeroSection_changedChart R t).symm)
    (originalKernelCoordinate R) (overlapChangedKernelCoordinate R t)
    (overlapChangedKernelCoordinate_image R t)

private theorem overlapOriginalIdealElement_image (t : R) :
    (idealPushforwardMap (coordinateSection R) (overlapZeroSection R t)
      (Spec.map (CommRingCat.ofHom (algebraMap R[X] (overlapRing R t)))) (𝟙 (Spec (.of R)))
      (by simpa only [Category.id_comp] using
        (overlapZeroSection_chart R t).symm)).val.app (op ⊤)
      (affineIdealElement (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))
        (originalKernelCoordinate R)) =
    affineIdealElement (CommRingCat.ofHom (overlapZero R t))
      (overlapOriginalKernelCoordinate R t) :=
  affineIdealElement_map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))
    (CommRingCat.ofHom (overlapZero R t))
    (CommRingCat.ofHom (algebraMap R[X] (overlapRing R t))) (𝟙 (Spec (.of R)))
    (by simpa only [Category.id_comp] using (overlapZeroSection_chart R t).symm)
    (originalKernelCoordinate R) (overlapOriginalKernelCoordinate R t) rfl

private theorem overlapChangedConormalMap_eq (t : R) :
    overlapChangedConormalMap R t = conormalMap (coordinateSection R) (overlapZeroSection R t)
      (Spec.map (CommRingCat.ofHom (Sections.translationOverlapMap R t)))
      (overlapZeroSection_changedChart R t).symm := rfl

private theorem overlapOriginalConormalMap_eq (t : R) :
    overlapOriginalConormalMap R t = conormalMap (coordinateSection R) (overlapZeroSection R t)
      (Spec.map (CommRingCat.ofHom (algebraMap R[X] (overlapRing R t))))
      (overlapZeroSection_chart R t).symm := rfl

private theorem affineConormalElement_eq {A B : CommRingCat.{u}} (σ : A ⟶ B)
    (x : RingHom.ker σ.hom) :
    affineConormalElement σ x = conormalElement (Spec.map σ) (affineIdealElement σ x) := rfl

private theorem overlapConormalMaps_coordinate (t : R) :
    GlobalSectionImagesEq (overlapChangedConormalMap R t) (overlapOriginalConormalMap R t)
      (affineConormalElement (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))
        (originalKernelCoordinate R)) := by
  rw [overlapChangedConormalMap_eq, overlapOriginalConormalMap_eq, affineConormalElement_eq]
  exact conormalMap_elements_eq (coordinateSection R) (overlapZeroSection R t)
    (Spec.map (CommRingCat.ofHom (Sections.translationOverlapMap R t)))
    (Spec.map (CommRingCat.ofHom (algebraMap R[X] (overlapRing R t))))
    (overlapZeroSection_changedChart R t).symm (overlapZeroSection_chart R t).symm
    (affineIdealElement (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))
      (originalKernelCoordinate R))
    (affineIdealElement (CommRingCat.ofHom (overlapZero R t))
      (overlapChangedKernelCoordinate R t))
    (affineIdealElement (CommRingCat.ofHom (overlapZero R t))
      (overlapOriginalKernelCoordinate R t))
    (overlapChangedIdealElement_image R t) (overlapOriginalIdealElement_image R t)
    (overlapConormalElement_eq R t)

private def coordinateClassFrame :
    (Modules.pullback (coordinateSection R)).obj (idealModule (coordinateSection R)) ≅
      SheafOfModules.unit (Spec (.of R)).ringCatSheaf :=
  relativeConormalAffineGeometricFreeIso (𝟙 (CommRingCat.of R[X]))
    (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))
    (fun r => ⟨Polynomial.C r, Polynomial.eval_C⟩)
    [Polynomial.X] (coordinate_weaklyRegular R) (coordinate_kernel_list R) ≪≫
      coproductUniqueIso (fun _ : ULift.{u} (Fin 1) =>
        SheafOfModules.unit (Spec (.of R)).ringCatSheaf)

private theorem coordinateClassFrame_generator :
    (coordinateClassFrame R).hom.val.app (op ⊤)
      (affineConormalElement (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))
        (originalKernelCoordinate R)) = (1 : Γ(Spec (.of R), ⊤)) := by
  let σ := CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))
  let hσ : Function.Surjective σ := fun r => ⟨Polynomial.C r, Polynomial.eval_C⟩
  let j : Fin 1 := 0
  change (coproductUniqueIso
    (fun _ : ULift.{u} (Fin 1) =>
      SheafOfModules.unit (Spec (.of R)).ringCatSheaf)).hom.val.app (op ⊤)
        ((relativeConormalAffineFreeIso (𝟙 (CommRingCat.of R[X])) σ hσ
          [Polynomial.X] (coordinate_weaklyRegular R) (coordinate_kernel_list R)).hom.val.app
            (op ⊤) ((relativeConormalAffineIdealPullbackIso (𝟙 _) σ hσ).hom.val.app
              (op ⊤) (affineConormalElement σ (originalKernelCoordinate R)))) =
      (1 : Γ(Spec (.of R), ⊤))
  rw [show (relativeConormalAffineIdealPullbackIso (𝟙 _) σ hσ).hom.val.app (op ⊤)
      (affineConormalElement σ (originalKernelCoordinate R)) =
    tilde.toOpen (relativeConormalAffineModule (𝟙 _) σ hσ) ⊤
      (relativeConormalAffineClass (𝟙 _) σ hσ (originalKernelCoordinate R)) from
    (Diagonal.affineConormalIso_unit_top σ hσ (originalKernelCoordinate R)).trans
      (congrArg (tilde.toOpen (relativeConormalAffineModule (𝟙 _) σ hσ) ⊤)
        (Diagonal.affineClassMap_apply σ hσ (originalKernelCoordinate R)))]
  have hb := relativeConormalAffineFreeIso_class (𝟙 (CommRingCat.of R[X])) σ hσ
    [Polynomial.X] (coordinate_weaklyRegular R) (coordinate_kernel_list R) j ⊤
  rw [show (relativeConormalAffineFreeIso (𝟙 (CommRingCat.of R[X])) σ hσ
      [Polynomial.X] (coordinate_weaklyRegular R) (coordinate_kernel_list R)).hom.val.app
        (op ⊤) (tilde.toOpen (relativeConormalAffineModule (𝟙 _) σ hσ) ⊤
          (relativeConormalAffineClass (𝟙 _) σ hσ (originalKernelCoordinate R))) =
      (SheafOfModules.freeSection (R := (Spec (.of R)).ringCatSheaf) (ULift.up j)).val
        (op ⊤) from hb]
  have hι : SheafOfModules.ιFree (R := (Spec (.of R)).ringCatSheaf) (ULift.up j) ≫
      (coproductUniqueIso
        (fun _ : ULift.{u} (Fin 1) =>
          SheafOfModules.unit (Spec (.of R)).ringCatSheaf)).hom = 𝟙 _ := by
    simp only [SheafOfModules.ιFree, ι_coproductUniqueIso_hom, eqToHom_refl]
  exact congrArg (fun q => q.val.app (op ⊤) (1 : Γ(Spec (.of R), ⊤))) hι

private def conormalTensorIso {K A B : CommRingCat.{u}} (α : K ⟶ A) (σ : A ⟶ B)
    (hσ : Function.Surjective σ) :
    (ModuleCat.extendScalars σ.hom).obj (ModuleCat.of A (RingHom.ker σ.hom)) ≅
      relativeConormalAffineModule α σ hσ := by
  let := α.hom.toAlgebra
  let := (α ≫ σ).hom.toAlgebra
  let := σ.hom.toAlgebra
  exact (relativeConormalAffineExtension α σ hσ).cotangentEquiv.toModuleIso

private theorem conormalTensorIso_tmul {K A B : CommRingCat.{u}} (α : K ⟶ A)
    (σ : A ⟶ B) (hσ : Function.Surjective σ) (x : RingHom.ker σ.hom) :
    letI := σ.hom.toAlgebra
    (conormalTensorIso α σ hσ).hom ((1 : B) ⊗ₜ[A] x) =
      relativeConormalAffineClass α σ hσ x := by
  let := α.hom.toAlgebra
  let := (α ≫ σ).hom.toAlgebra
  let := σ.hom.toAlgebra
  let E := relativeConormalAffineExtension α σ hσ
  change E.cotangentEquiv ((1 : B) ⊗ₜ[E.Ring] (show E.ker from x)) =
    Algebra.Extension.Cotangent.mk (show E.ker from x)
  exact (E.contangentEquiv_tmul 1 (show E.ker from x)).trans (one_smul B _)

private def conormalClassTransfer {K A B : CommRingCat.{u}} (α : K ⟶ A) (σ : A ⟶ B)
    (hσ : Function.Surjective σ) :
    relativeConormalAffineModule (𝟙 A) σ hσ ⟶ relativeConormalAffineModule α σ hσ :=
  (conormalTensorIso (𝟙 A) σ hσ).inv ≫ (conormalTensorIso α σ hσ).hom

private theorem conormalClassTransfer_class {K A B : CommRingCat.{u}} (α : K ⟶ A)
    (σ : A ⟶ B) (hσ : Function.Surjective σ) (x : RingHom.ker σ.hom) :
    conormalClassTransfer α σ hσ (relativeConormalAffineClass (𝟙 A) σ hσ x) =
      relativeConormalAffineClass α σ hσ x := by
  let := σ.hom.toAlgebra
  change (conormalTensorIso α σ hσ).hom
    ((conormalTensorIso (𝟙 A) σ hσ).inv
      (relativeConormalAffineClass (𝟙 A) σ hσ x)) = _
  rw [← conormalTensorIso_tmul (𝟙 A) σ hσ x, Iso.hom_inv_id_apply]
  exact conormalTensorIso_tmul α σ hσ x

private theorem affineConormalIdealIso_transfer {K A B : CommRingCat.{u}} (α : K ⟶ A)
    (σ : A ⟶ B) (hσ : Function.Surjective σ) :
    (relativeConormalAffineIdealPullbackIso α σ hσ).hom =
      (relativeConormalAffineIdealPullbackIso (𝟙 A) σ hσ).hom ≫
        (tilde.functor B).map (conormalClassTransfer α σ hσ) := by
  let G := (Modules.pullback (Spec.map σ)).mapIso (affineIdealIso σ).symm ≪≫
    (tildePullbackIso σ).app (ModuleCat.of A (RingHom.ker σ.hom))
  change G.hom ≫ (tilde.functor B).map (conormalTensorIso α σ hσ).hom =
    (G.hom ≫ (tilde.functor B).map (conormalTensorIso (𝟙 A) σ hσ).hom) ≫
      (tilde.functor B).map
        ((conormalTensorIso (𝟙 A) σ hσ).inv ≫ (conormalTensorIso α σ hσ).hom)
  rw [CategoryTheory.Functor.map_comp, Category.assoc,
    ← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

private theorem affineConormalElement_class {K A B : CommRingCat.{u}} (α : K ⟶ A)
    (σ : A ⟶ B) (hσ : Function.Surjective σ) (x : RingHom.ker σ.hom) :
    (relativeConormalAffineIdealPullbackIso α σ hσ).hom.val.app (op ⊤)
      (affineConormalElement σ x) =
    tilde.toOpen (relativeConormalAffineModule α σ hσ) ⊤
      (relativeConormalAffineClass α σ hσ x) := by
  let q := conormalClassTransfer α σ hσ
  have hi : (relativeConormalAffineIdealPullbackIso (𝟙 A) σ hσ).hom.val.app (op ⊤)
      (affineConormalElement σ x) =
    tilde.toOpen (relativeConormalAffineModule (𝟙 A) σ hσ) ⊤
      (relativeConormalAffineClass (𝟙 A) σ hσ x) :=
    (Diagonal.affineConormalIso_unit_top σ hσ x).trans
      (congrArg (tilde.toOpen (relativeConormalAffineModule (𝟙 A) σ hσ) ⊤)
        (Diagonal.affineClassMap_apply σ hσ x))
  have ht := congrArg (fun f => f.val.app (op ⊤) (affineConormalElement σ x))
    (affineConormalIdealIso_transfer α σ hσ)
  refine ht.trans ?_
  change ((tilde.functor B).map q).val.app (op ⊤)
    ((relativeConormalAffineIdealPullbackIso (𝟙 A) σ hσ).hom.val.app (op ⊤)
      (affineConormalElement σ x)) = _
  rw [hi]
  exact (ConcreteCategory.congr_hom (tilde.toOpen_map_app q ⊤)
    (relativeConormalAffineClass (𝟙 A) σ hσ x)).trans
      (congrArg (tilde.toOpen (relativeConormalAffineModule α σ hσ) ⊤)
        (conormalClassTransfer_class α σ hσ x))

private theorem geometricConormalFrame_class {K A B : CommRingCat.{u}}
    (α : K ⟶ A) (σ : A ⟶ B) (hσ : Function.Surjective σ) (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s) (hker : Ideal.ofList s = RingHom.ker σ.hom)
    (j : Fin s.length) :
    (relativeConormalAffineGeometricFreeIso α σ hσ s hs hker).hom.val.app (op ⊤)
      (affineConormalElement σ ⟨s.get j, hker.le (Ideal.subset_span (s.get_mem j))⟩) =
    (SheafOfModules.freeSection (R := (Spec B).ringCatSheaf) (ULift.up j)).val (op ⊤) :=
  (congrArg ((relativeConormalAffineFreeIso α σ hσ s hs hker).hom.val.app (op ⊤))
    (affineConormalElement_class α σ hσ
      ⟨s.get j, hker.le (Ideal.subset_span (s.get_mem j))⟩)).trans
    (relativeConormalAffineFreeIso_class α σ hσ s hs hker j ⊤)

/-- The actual coordinate conormal frame over `Polynomial.C` sends the original coordinate
class to the unit section. -/
theorem coordinateConormalIso_generator :
    (coordinateConormalIso R).hom.val.app (op ⊤)
      (affineConormalElement (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))
        ⟨Polynomial.X, by simp⟩) = (1 : Γ(Spec (.of R), ⊤)) := by
  let j : Fin 1 := 0
  let e := coproductUniqueIso (fun _ : ULift.{u} (Fin 1) =>
    SheafOfModules.unit (Spec (.of R)).ringCatSheaf)
  have h := geometricConormalFrame_class
    (CommRingCat.ofHom (Polynomial.C : R →+* R[X]))
    (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))
    (fun r => ⟨Polynomial.C r, Polynomial.eval_C⟩)
    [Polynomial.X] (coordinate_weaklyRegular R) (coordinate_kernel_list R) j
  have hι : SheafOfModules.ιFree (R := (Spec (.of R)).ringCatSheaf) (ULift.up j) ≫
      e.hom = 𝟙 _ := by
    simp only [e, SheafOfModules.ιFree, ι_coproductUniqueIso_hom, eqToHom_refl]
  exact (congrArg (e.hom.val.app (op ⊤)) h).trans
    (congrArg (fun q => q.val.app (op ⊤) (1 : Γ(Spec (.of R), ⊤))) hι)

/-- A unit frame makes the original global generator detect equality of module-sheaf maps. -/
theorem hom_ext_of_globalUnitFrame {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ SheafOfModules.unit X.ringCatSheaf) (m : M.val.obj (op ⊤))
    (he : e.hom.val.app (op ⊤) m = (1 : Γ(X, ⊤))) (f g : M ⟶ N)
    (hfg : f.val.app (op ⊤) m = g.val.app (op ⊤) m) : f = g := by
  apply (cancel_epi e.inv).mp
  apply (unitHomGlobalSectionsEquiv X N).injective
  change f.val.app (op ⊤) (e.inv.val.app (op ⊤) (1 : Γ(X, ⊤))) =
    g.val.app (op ⊤) (e.inv.val.app (op ⊤) (1 : Γ(X, ⊤)))
  have hm : e.inv.val.app (op ⊤) (1 : Γ(X, ⊤)) = m :=
    (congrArg (e.inv.val.app (op ⊤)) he).symm.trans
      (congrArg (fun q => q.val.app (op ⊤) m) e.hom_inv_id)
  rw [hm]
  exact hfg

private theorem hom_ext_of_globalUnitFrame_images {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ SheafOfModules.unit X.ringCatSheaf) (m : M.val.obj (op ⊤))
    (he : e.hom.val.app (op ⊤) m = (1 : Γ(X, ⊤))) (f g : M ⟶ N)
    (hfg : GlobalSectionImagesEq f g m) : f = g :=
  hom_ext_of_globalUnitFrame e m he f g hfg

/-- The two canonical maps on the actual conormal agree on the native unipotent overlap. -/
theorem overlapConormalMaps_equal (t : R) :
    overlapChangedConormalMap R t = overlapOriginalConormalMap R t := by
  exact hom_ext_of_globalUnitFrame_images (coordinateClassFrame R)
    (affineConormalElement (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))
      (originalKernelCoordinate R)) (coordinateClassFrame_generator R)
    (overlapChangedConormalMap R t) (overlapOriginalConormalMap R t)
    (overlapConormalMaps_coordinate R t)

end Conormal

variable {X : Scheme.{u}} {E : X.Modules}
variable (i : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ E)
  (g : E ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
  (hig : i ≫ g = 0) (hS : (extensionComplex i g hig).ShortExact)

/-- The actual ideal on a frame chart is the same actual infinity ideal under its source iso. -/
def localQuotientIdealIso (a : AffineFrame g) :
    idealModule (localQuotientSection g a) ≅
      idealModule (Sections.infinity Γ(X, a.U.1)) := by
  let q := Sections.infinity Γ(X, a.U.1)
  let h : a.isoSpec.hom ≫ q = localQuotientSection g a ≫ 𝟙 _ := by
    simp only [Category.comp_id]
    rfl
  let : IsIso (idealPullbackMap q (localQuotientSection g a) (𝟙 _) a.isoSpec.hom h) :=
    idealPullbackMap_isIso_of_iso_square _ _ _ _ _
  exact (asIso (idealPullbackMap q (localQuotientSection g a) (𝟙 _) a.isoSpec.hom h)).symm ≪≫
    (pullbackId (X := projectiveP1 Γ(X, a.U.1))).app (idealModule q)

/-- The actual local quotient conormal is framed by the original affine coordinate class. -/
def localQuotientConormalIso (a : AffineFrame g) :
    (Modules.pullback (localQuotientSection g a)).obj (idealModule (localQuotientSection g a)) ≅
      SheafOfModules.unit a.U.1.toScheme.ringCatSheaf :=
  (Modules.pullback (localQuotientSection g a)).mapIso (localQuotientIdealIso g a) ≪≫
    ((pullbackComp a.isoSpec.hom (Sections.infinity Γ(X, a.U.1))).app
      (idealModule (Sections.infinity Γ(X, a.U.1)))).symm ≪≫
    (Modules.pullback a.isoSpec.hom).mapIso (Conormal.infinityConormalIso Γ(X, a.U.1)) ≪≫
    pullbackUnitIso a.isoSpec.hom

/-- The canonical ideal map on each original bundle chart is an isomorphism. -/
def quotientIdealChartIso (a : AffineFrame g) :
    (Modules.pullback (chartInclusion i g hig hS a)).obj
      (idealModule (quotientSection i g hig hS)) ≅
      idealModule (localQuotientSection g a) := by
  let h := quotientSection_chart i g hig hS a
  let : IsIso (idealPullbackMap (quotientSection i g hig hS) (localQuotientSection g a)
      (chartInclusion i g hig hS a) a.U.1.ι h) :=
    idealPullbackMap_isIso_of_isOpenImmersion _ _ _ _ h
      (quotientSection_chart_isPullback i g hig hS a)
  exact asIso (idealPullbackMap (quotientSection i g hig hS) (localQuotientSection g a)
    (chartInclusion i g hig hS a) a.U.1.ι h)

/-- The actual ideal of the constructed quotient section is locally free of rank one. -/
theorem quotientIdeal_locallyRankOne :
    IsLocallyRankOne (projectiveBundle i g hig hS) (idealModule (quotientSection i g hig hS)) := by
  let : Epi g := hS.epi_g
  apply isLocallyRankOne_of_forall_isLocallyRankOneAt
  intro z
  obtain ⟨a, p, hp⟩ := (gluingData i g hig hS).cover.exists_eq z
  refine ⟨projectiveP1 Γ(X, a.U.1), chartInclusion i g hig hS a, inferInstance, ⟨p, hp⟩, ?_⟩
  exact isLocallyRankOne_of_iso _
    ((quotientIdealChartIso i g hig hS a) ≪≫ localQuotientIdealIso g a).symm
      (Conormal.infinityIdeal_locallyRankOne Γ(X, a.U.1))

/-- Each original base frame trivializes the actual pulled-back quotient ideal. -/
def quotientConormalChartIso (a : AffineFrame g) :
    (Modules.pullback a.U.1.ι).obj
      ((Modules.pullback (quotientSection i g hig hS)).obj
        (idealModule (quotientSection i g hig hS))) ≅
        SheafOfModules.unit a.U.1.toScheme.ringCatSheaf :=
  (pullbackComp a.U.1.ι (quotientSection i g hig hS)).app
      (idealModule (quotientSection i g hig hS)) ≪≫
    (pullbackCongr (quotientSection_chart i g hig hS a)).app
      (idealModule (quotientSection i g hig hS)) ≪≫
    ((pullbackComp (localQuotientSection g a) (chartInclusion i g hig hS a)).app
      (idealModule (quotientSection i g hig hS))).symm ≪≫
    (Modules.pullback (localQuotientSection g a)).mapIso (quotientIdealChartIso i g hig hS a) ≪≫
    localQuotientConormalIso g a

/-- The existing canonical conormal frame expressed on the actual open restriction. -/
def quotientConormalRestrictionIso (a : AffineFrame g) :
    ((Modules.pullback (quotientSection i g hig hS)).obj
      (idealModule (quotientSection i g hig hS))).restrict a.U.1.ι ≅
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf).restrict a.U.1.ι :=
  (restrictFunctorIsoPullback a.U.1.ι).app
    ((Modules.pullback (quotientSection i g hig hS)).obj
      (idealModule (quotientSection i g hig hS))) ≪≫
    quotientConormalChartIso i g hig hS a ≪≫ (restrictUnitIso a.U.1.ι).symm

/-- The exact native-overlap compatibility required of the original conormal frames. -/
def QuotientConormalFramesCompatible : Prop :=
  InternalHom.RestrictionHomCompatible (fun a : AffineFrame g => a.U.1.ι)
    ((Modules.pullback (quotientSection i g hig hS)).obj (idealModule (quotientSection i g hig hS)))
    (SheafOfModules.unit X.ringCatSheaf)
    (fun a => (quotientConormalRestrictionIso i g hig hS a).hom)

/-- Compatible original ideal frames glue to an isomorphism of the actual conormal with `O_X`.
The displayed compatibility is a premise; local rank one alone does not discharge it. -/
def quotientConormalIsoOfCompatibleFrames
    (hcomp : QuotientConormalFramesCompatible i g hig hS) :
    (Modules.pullback (quotientSection i g hig hS)).obj (idealModule (quotientSection i g hig hS)) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  let : Epi g := hS.epi_g
  exact InternalHom.glueRestrictionIso (fun a : AffineFrame g => a.U.1.toScheme)
    (fun a => a.U.1.ι) (fun x => (frameCover g).exists_eq x)
    _ _ (quotientConormalRestrictionIso i g hig hS) hcomp

end AlgebraicGeometry.Scheme.ProjectiveBundle.RankTwoExtension
