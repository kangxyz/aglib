/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pushforward
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.AffineTrace
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Charts
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalCharts.Quotient

/-!
# Transport of the original Serre comparison through an actual canonical isomorphism

The input and output transports use the installed single-functor shift
isomorphisms. The unit coefficient is the actual value of the installed
closed right adjoint. A local chart supplies the dimension inequality at a
point; the complementary branch is an empty source. No global dimension
inequality or Noetherian hypothesis is imposed by these constructions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

section NativeReindex

set_option autoImplicit false

open CategoryTheory CategoryTheory.Abelian

universe u v w w' u' v' w'' t

namespace RelativeCanonicalReindex

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- Use the installed single-functor shift comparisons for both sides. -/
def singleReindexIso (N : A) (c q r : ℤ) (h : q - r = c) :
    ((DerivedCategory.singleFunctor A 0).obj N)⟦r⟧ ≅
      ((DerivedCategory.singleFunctor A c).obj N)⟦q⟧ :=
  ((DerivedCategory.singleFunctors A).shiftIso r (-r) 0 (by omega)).app N ≪≫
    (((DerivedCategory.singleFunctors A).shiftIso q (-r) c (by omega)).app N).symm

/-- The original reindexing is the native degree-zero purity arrow shifted by `r`,
followed by the same shift-addition comparison. -/
theorem singleReindexIso_hom_eq_shift (N : A) (c q r : ℤ) (h : q - r = c) :
    (singleReindexIso N c q r h).hom =
      (((DerivedCategory.singleFunctors A).shiftIso c 0 c (by omega)).inv.app N)⟦r⟧' ≫
        (shiftFunctorAdd' (DerivedCategory A) c r q (by omega)).inv.app
          ((DerivedCategory.singleFunctor A c).obj N) := by
  simp only [singleReindexIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  rw [(DerivedCategory.singleFunctors A).shiftIso_add'_inv_app r c q (by omega)
    (-r) 0 c (by omega) (by omega)]
  simp only [Iso.hom_inv_id_app_assoc]

/-- The two original output reindexings agree after the native shift-addition
comparisons. This is valid for arbitrary integer dimensions and shifts. -/
theorem singleReindexIso_output_inv (N : A) (n d c q r : ℤ)
    (hc : c = n - d) (hq : c + r = q) :
    (shiftFunctorAdd' (DerivedCategory A) c r q hq).inv.app
        ((DerivedCategory.singleFunctor A n).obj N) ≫
        (singleReindexIso N n q (r - d) (by omega)).inv =
      ((singleReindexIso N n c (-d) (by omega)).inv)⟦r⟧' ≫
        (shiftFunctorAdd' (DerivedCategory A) (-d) r (r - d) (by omega)).inv.app
          ((DerivedCategory.singleFunctor A 0).obj N) := by
  simp only [singleReindexIso, Iso.trans_inv, Iso.symm_inv, Iso.app_hom, Iso.app_inv]
  rw [(DerivedCategory.singleFunctors A).shiftIso_add'_hom_app r c q hq
    (-(r - d)) (-(-d)) n (by omega) (by omega)]
  rw [(DerivedCategory.singleFunctors A).shiftIso_add'_inv_app r (-d) (r - d)
    (by omega) (-(r - d)) (-(-d)) 0 (by omega) (by omega)]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc,
    Iso.hom_inv_id_app_assoc]

/-- The empty-source branch needs no comparison of the two geometric dimensions. -/
-- Retain the original public Ext-universe interface for the zero-source comparison.
@[nolint unusedArguments]
theorem comparison_bijective_of_zero_source [HasExt.{w'} A]
    {B : Type*} [Category* B] [Limits.HasZeroMorphisms B]
    (M N : A) (r : ℕ) (hM : Limits.IsZero M)
    {K T : B} (hK : Limits.IsZero K)
    (f : Ext.{w'} M N r → (K ⟶ T)) : Function.Bijective f := by
  constructor
  · intro x y _
    apply Ext.ext
    exact ((DerivedCategory.singleFunctor A 0).map_isZero hM).eq_of_src _ _
  · intro y
    exact ⟨0, hK.eq_of_src _ _⟩

variable {S : Type t} [CommRing S] [Linear S A]

/-- Postcomposition by the actual target isomorphism is linear. -/
def postcompHomLinearEquiv {B : Type*} [Category* B]
    [Preadditive B] [Linear S B] (M : B) {N N' : B} (e : N ≅ N') :
    (M ⟶ N) ≃ₗ[S] (M ⟶ N') where
  toFun x := x ≫ e.hom
  invFun x := x ≫ e.inv
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp only [Preadditive.add_comp]
  map_smul' s x := by simp only [RingHom.id_apply, Linear.smul_comp]

/-- Transport into the original right-adjoint value; no new duality map is chosen. -/
def purityInputLinearEquiv [HasExt.{w'} A] (M N : A)
    (K : DerivedCategory A) (c : ℤ)
    (E : K ≅ (DerivedCategory.singleFunctor A c).obj N)
    (q r : ℕ) (h : (q : ℤ) - r = c) :
    Ext.{w'} M N r ≃ₗ[S]
      ((DerivedCategory.singleFunctor A 0).obj M ⟶ K⟦(q : ℤ)⟧) :=
  (Ext.homLinearEquiv (R := S)).trans
    (postcompHomLinearEquiv ((DerivedCategory.singleFunctor A 0).obj M)
      (singleReindexIso N c q r h ≪≫
        (shiftFunctor (DerivedCategory A) (q : ℤ)).mapIso E.symm))

/-- The actual degree-zero identity input is the original native purity arrow. -/
theorem purityInputLinearEquiv_mk₀_id [HasExt.{w'} A] (N : A)
    (K : DerivedCategory A) (c : ℕ)
    (E : K ≅ (DerivedCategory.singleFunctor A (c : ℤ)).obj N) :
    purityInputLinearEquiv (S := S) N N K (c : ℤ) E c 0 (by omega) (Ext.mk₀ (𝟙 N)) =
      ((DerivedCategory.singleFunctors A).shiftIso (c : ℤ) 0 c (by omega)).inv.app N ≫
        (E.inv)⟦(c : ℤ)⟧' := by
  change (Ext.mk₀ (𝟙 N)).hom ≫
    (singleReindexIso N (c : ℤ) c 0 (by omega)).hom ≫ (E.inv)⟦(c : ℤ)⟧' = _
  rw [Ext.mk₀_hom]
  simp [singleReindexIso, ShiftedHom.mk₀, shiftFunctorZero']

/-- Every original Ext input is its native shifted composition with the SAME
degree-zero identity input. No geometric dimension comparison is assumed. -/
theorem purityInputLinearEquiv_eq_hom_comp [HasExt.{w'} A] (M N : A)
    (K : DerivedCategory A) (c q r : ℕ) (h : c + r = q)
    (E : K ≅ (DerivedCategory.singleFunctor A (c : ℤ)).obj N) (α : Ext.{w'} M N r) :
    purityInputLinearEquiv (S := S) M N K (c : ℤ) E q r (by omega) α =
      α.hom.comp
        (purityInputLinearEquiv (S := S) N N K (c : ℤ) E c 0 (by omega)
          (Ext.mk₀ (𝟙 N))) (show (c : ℤ) + (r : ℤ) = (q : ℤ) by omega) := by
  rw [purityInputLinearEquiv_mk₀_id]
  change α.hom ≫ (singleReindexIso N (c : ℤ) q r (by omega)).hom ≫
    (E.inv)⟦(q : ℤ)⟧' = _
  rw [singleReindexIso_hom_eq_shift]
  simp only [ShiftedHom.comp, Functor.map_comp, Category.assoc]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun z => α.hom ≫
      (((DerivedCategory.singleFunctors A).shiftIso (c : ℤ) 0 c (by omega)).inv.app N)
        ⟦(r : ℤ)⟧' ≫ z)
      ((shiftFunctorAdd' (DerivedCategory A) (c : ℤ) r q (by omega)).inv.naturality E.inv).symm

/-- The input composition formula retains an actual integer-indexed target.
The degree equality transports the whole identity inside this proof. -/
theorem purityInputLinearEquiv_eq_hom_comp_of_degree [HasExt.{w'} A] (M N : A)
    (K : DerivedCategory A) (c : ℤ) (c₀ q r : ℕ) (hc : (c₀ : ℤ) = c)
    (h : c₀ + r = q) (E : K ≅ (DerivedCategory.singleFunctor A c).obj N)
    (α : Ext.{w'} M N r) :
    purityInputLinearEquiv (S := S) M N K c E q r (by omega) α =
      α.hom.comp
        (purityInputLinearEquiv (S := S) N N K c E c₀ 0 (by omega)
          (Ext.mk₀ (𝟙 N))) (show (c₀ : ℤ) + (r : ℤ) = (q : ℤ) by omega) := by
  subst c
  exact purityInputLinearEquiv_eq_hom_comp (S := S) M N K c₀ q r h E α

/-- The target uses the same installed shifts, including negative `r - d`. -/
def purityOutputLinearEquiv (M : DerivedCategory A) (N : A)
    (n d q r : ℕ) (h : (q : ℤ) - r = (n : ℤ) - d) :
    (M ⟶ ((DerivedCategory.singleFunctor A n).obj N)⟦(q : ℤ)⟧) ≃ₗ[S]
      (M ⟶ ((DerivedCategory.singleFunctor A 0).obj N)⟦(r : ℤ) - d⟧) :=
  postcompHomLinearEquiv M
    (singleReindexIso N n q ((r : ℤ) - d) (by omega)).symm

end RelativeCanonicalReindex

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

theorem module_isZero_of_empty {X : Scheme.{u}} [IsEmpty X] (M : X.Modules) :
    Limits.IsZero M := by
  rw [isZero_iff_stalks]
  intro x
  exact isEmptyElim x

theorem derivedPushforwardSingle_isZero_of_empty {X Y : Scheme.{u}} [IsEmpty X]
    (f : X ⟶ Y) (M : X.Modules) :
    Limits.IsZero ((derivedPushforwardPlus f ⋙ DerivedCategory.Plus.ι).obj
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) := by
  let : (derivedPushforwardPlus f).Additive := by
    unfold derivedPushforwardPlus
    infer_instance
  exact (derivedPushforwardPlus f ⋙ DerivedCategory.Plus.ι).map_isZero
    ((DerivedCategory.Plus.singleFunctor X.Modules 0).map_isZero
      (module_isZero_of_empty M))

end AlgebraicGeometry.Scheme.Modules

namespace RelativeCanonicalReindex

open CategoryTheory CategoryTheory.Abelian

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [HasExt.{w'} A] {S : Type t} [CommRing S] [Linear S A]

/-- The original comparison can be transported before its bijectivity is known. -/
def serreLinearMapOfPurity
    {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w''} B]
    [Linear S B] (M Ω : A) (K : DerivedCategory A) (D : DerivedCategory B)
    (N : B) (n d q r : ℕ) (h : (q : ℤ) - r = (n : ℤ) - d)
    (E : K ≅ (DerivedCategory.singleFunctor A ((n : ℤ) - d)).obj Ω)
    (Φ : ((DerivedCategory.singleFunctor A 0).obj M ⟶ K⟦(q : ℤ)⟧) →ₗ[S]
      (D ⟶ ((DerivedCategory.singleFunctor B n).obj N)⟦(q : ℤ)⟧)) :
    Ext.{w'} M Ω r →ₗ[S]
      (D ⟶ ((DerivedCategory.singleFunctor B 0).obj N)⟦(r : ℤ) - d⟧) :=
  (purityOutputLinearEquiv D N n d q r h).toLinearMap.comp
    (Φ.comp (purityInputLinearEquiv M Ω K ((n : ℤ) - d) E q r h).toLinearMap)

theorem serreLinearMapOfPurity_apply
    {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w''} B]
    [Linear S B] (M Ω : A) (K : DerivedCategory A) (D : DerivedCategory B)
    (N : B) (n d q r : ℕ) (h : (q : ℤ) - r = (n : ℤ) - d)
    (E : K ≅ (DerivedCategory.singleFunctor A ((n : ℤ) - d)).obj Ω)
    (Φ : ((DerivedCategory.singleFunctor A 0).obj M ⟶ K⟦(q : ℤ)⟧) →ₗ[S]
      (D ⟶ ((DerivedCategory.singleFunctor B n).obj N)⟦(q : ℤ)⟧))
    (x : Ext.{w'} M Ω r) :
    serreLinearMapOfPurity M Ω K D N n d q r h E Φ x =
      Φ (purityInputLinearEquiv (S := S) M Ω K ((n : ℤ) - d) E q r h x) ≫
        (singleReindexIso N n q ((r : ℤ) - d) (by omega)).inv := rfl

theorem serreLinearMapOfPurity_bijective
    {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w''} B]
    [Linear S B] (M Ω : A) (K : DerivedCategory A) (D : DerivedCategory B)
    (N : B) (n d q r : ℕ) (h : (q : ℤ) - r = (n : ℤ) - d)
    (E : K ≅ (DerivedCategory.singleFunctor A ((n : ℤ) - d)).obj Ω)
    (Φ : ((DerivedCategory.singleFunctor A 0).obj M ⟶ K⟦(q : ℤ)⟧) →ₗ[S]
      (D ⟶ ((DerivedCategory.singleFunctor B n).obj N)⟦(q : ℤ)⟧))
    (hΦ : Function.Bijective Φ) :
    Function.Bijective (serreLinearMapOfPurity M Ω K D N n d q r h E Φ) :=
  (purityOutputLinearEquiv (S := S) D N n d q r h).bijective.comp
    (hΦ.comp (purityInputLinearEquiv (S := S) M Ω K ((n : ℤ) - d) E q r h).bijective)

end RelativeCanonicalReindex

end NativeReindex

section NativeUnit

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Cohomology

universe u

namespace RelativeCanonicalUnit

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

variable {X P Y : Scheme.{u}} (i : X ⟶ P) [IsClosedImmersion i] (p : P ⟶ Y) (n : ℕ)

/-- Apply the installed right adjoint to the original geometric unit isomorphism. -/
def unitValueIso :
    (derivedClosedImmersionRightAdjointPlus i).obj
      ((DerivedCategory.Plus.singleFunctor P.Modules 0).obj
        ((relativeTopDifferentialCoefficientsFunctor p n).obj
          (SheafOfModules.unit Y.ringCatSheaf))) ≅
      closedImmersionCanonicalValue i p n :=
  (derivedClosedImmersionRightAdjointPlus i).mapIso
    ((DerivedCategory.Plus.singleFunctor P.Modules 0).mapIso
      (relativeTopDifferentialCoefficientsUnitIso p n))

/-- The exact input of the original Serre map, identified using an actual purity map. -/
def unitPurityIso (d : ℕ)
    (E : closedImmersionCanonicalValue i p n ≅
      (DerivedCategory.Plus.singleFunctor X.Modules ((n : ℤ) - d)).obj
        (moduleExteriorPower X (Differentials.relativeDifferentialSheaf (i ≫ p)) d)) :
    DerivedCategory.Plus.ι.obj
      ((derivedClosedImmersionRightAdjointPlus i).obj
        ((DerivedCategory.Plus.singleFunctor P.Modules 0).obj
          ((relativeTopDifferentialCoefficientsFunctor p n).obj
            (SheafOfModules.unit Y.ringCatSheaf)))) ≅
      (DerivedCategory.singleFunctor X.Modules ((n : ℤ) - d)).obj
        (moduleExteriorPower X (Differentials.relativeDifferentialSheaf (i ≫ p)) d) :=
  DerivedCategory.Plus.ι.mapIso (unitValueIso i p n ≪≫ E)

end RelativeCanonicalUnit

end NativeUnit

section NativeDimension

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Differentials

universe u

namespace RelativeCanonicalDimension

variable {X P Y : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ Y) (n d : ℕ)
  [hi : IsClosedImmersion i] [hp : SmoothOfRelativeDimension n p]
  [hf : SmoothOfRelativeDimension d (i ≫ p)]

include hi hp hf in
/-- A point supplies the actual regular chart and hence the local dimension bound. -/
theorem dimension_le_at_point (x : X) : d ≤ n := by
  have h := (smoothClosedImmersionLocalChart i p n d x).dimension_eq
  omega

include hi hp hf in
/-- The complementary case is an empty source, rather than an extra premise. -/
theorem source_isEmpty (h : n < d) : IsEmpty X where
  false x := (not_le_of_gt h) (dimension_le_at_point i p n d x)

end RelativeCanonicalDimension

namespace RelativeCanonicalReindex

/-- The nonnegative Ext degree is selected only after a geometric dimension bound. -/
theorem serreDegree_eq (n d r : ℕ) (h : d ≤ n) :
    ((r + (n - d) : ℕ) : ℤ) - (r : ℤ) = (n : ℤ) - d := by
  omega

end RelativeCanonicalReindex

end NativeDimension
