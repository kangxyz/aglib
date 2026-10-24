/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.SerreTransport
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.ClosedEmbedding.Linear
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.ClosedEmbedding.UnitTrace
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.Linear
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.DegreeZero
public import Aglib.Algebra.Homology.DerivedCategory.TStructure.HomToSingle
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Comparison.AffineComparison
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Derived
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Locality
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleUnit.ShortExact
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Derived.Connecting
public import Mathlib.LinearAlgebra.Dual.Defs
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.FinitePresentation

/-!
# The original unit-coefficient Serre map for a Cohen--Macaulay curve

The closed-stalk regular-parameter hypothesis is the one in
`CohenMacaulayCurve`. Its actual canonical reconstruction reindexes the
original closed-embedding Serre map. The native input and output shift
comparisons retain the source/Yoneda normalization and its original signs.

The projective index condition `1 ≤ n` is explicit: the natural Serre
degree is `r + (n - 1)`, while the canonical homology remains in integer
degree `n - 1`. No smoothness, reducedness, normality or Gorenstein
condition on the source is imposed. The coefficient is the original unit
over `k`; no intrinsic surface coefficient line is identified with `k`.
-/

@[expose] public noncomputable section

universe u v w u' v' w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent RelativeCanonicalReindex

attribute [local instance] AlgebraicGeometry.Scheme.Modules.moduleSpecΓFunctor_additive

private theorem cmCurveToInjectiveSingle_eq_zero
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    (K : DerivedCategory A) (a i : ℤ) [K.IsGE a] (I : A) [Injective I]
    (hi : i < a) (f : K ⟶ (DerivedCategory.singleFunctor A i).obj I) : f = 0 := by
  obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE K a
  apply (cancel_epi e.inv).mp
  simpa only [Limits.comp_zero] using
    DerivedCategory.to_singleFunctor_obj_eq_zero_of_injective
      (K := L) (i := i) (e.inv ≫ f) a hi

/-- Native homology determines maps to an injective coefficient single,
without an upper bound on the source object. -/
theorem DerivedCategory.homToSingleAddHom_bijective_of_injective
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    (K : DerivedCategory A) (i : ℤ) (I : A) [Injective I] :
    Function.Bijective (DerivedCategory.homToSingleAddHom K i I) := by
  let t := DerivedCategory.TStructure.t (C := A)
  let T := (t.triangleLTGE (i + 1)).obj K
  have hT := t.triangleLTGE_distinguished (i + 1) K
  let V := (DerivedCategory.singleFunctor A i).obj I
  let p : (T.obj₂ ⟶ V) →+ (T.obj₁ ⟶ V) :=
    { toFun f := T.mor₁ ≫ f
      map_zero' := Limits.comp_zero
      map_add' f g := by exact Preadditive.comp_add _ _ _ _ _ _ }
  have hp : Function.Bijective p := by
    constructor
    · intro f g hfg
      have hz : T.mor₁ ≫ (f - g) = 0 := by
        rw [Preadditive.comp_sub, sub_eq_zero]
        exact hfg
      obtain ⟨h, hh⟩ := T.yoneda_exact₂ hT (f - g) hz
      have hh0 : h = 0 := cmCurveToInjectiveSingle_eq_zero T.obj₃ (i + 1) i I
        (by omega) h
      exact sub_eq_zero.mp (hh.trans
        ((congrArg (fun z : T.obj₃ ⟶ V => T.mor₂ ≫ z) hh0).trans (Limits.comp_zero)))
    · intro f
      let : t.IsGE (T.obj₃⟦(-1 : ℤ)⟧) (i + 2) :=
        t.isGE_shift T.obj₃ (i + 1) (-1) (i + 2) (by omega)
      have hz : T.invRotate.mor₁ ≫ f = 0 :=
        cmCurveToInjectiveSingle_eq_zero (T.obj₃⟦(-1 : ℤ)⟧) (i + 2) i I
          (by omega) (T.invRotate.mor₁ ≫ f)
      obtain ⟨g, hg⟩ := T.invRotate.yoneda_exact₂
        (CategoryTheory.Pretriangulated.inv_rot_of_distTriang _ hT) f hz
      exact ⟨g, hg.symm⟩
  let H := DerivedCategory.homologyFunctor A i
  have h₀ := DerivedCategory.isZero_of_isGE T.obj₃ (i + 1) i (by omega)
  have hprev := DerivedCategory.isZero_of_isGE T.obj₃ (i + 1) (i - 1) (by omega)
  let : Epi (H.map T.mor₁) :=
    ((DerivedCategory.homologyFunctor A 0).homologySequence_epi_shift_map_mor₁_iff
      T hT i).mpr (h₀.eq_of_tgt _ _)
  let : Mono (H.map T.mor₁) :=
    ((DerivedCategory.homologyFunctor A 0).homologySequence_mono_shift_map_mor₁_iff
      T hT (i - 1) i (by omega)).mpr (hprev.eq_of_src _ _)
  let : IsIso (H.map T.mor₁) := isIso_of_mono_of_epi _
  let : T.obj₁.IsLE i := t.isLE_of_le T.obj₁ ((i + 1) - 1) i (by omega)
  let E := (AddEquiv.ofBijective p hp).trans
    ((DerivedCategory.homToSingleAddEquiv T.obj₁ i I).trans
      (Linear.homCongr ℤ (asIso (H.map T.mor₁)) (Iso.refl I)).toAddEquiv)
  have heq : (E : (T.obj₂ ⟶ V) → _) = DerivedCategory.homToSingleAddHom T.obj₂ i I := by
    funext f
    change (Linear.homCongr ℤ (asIso (H.map T.mor₁)) (Iso.refl I))
      (DerivedCategory.homToSingleAddEquiv T.obj₁ i I (p f)) = _
    rw [Linear.homCongr_apply, DerivedCategory.homToSingleAddEquiv_apply]
    simp only [Iso.refl_hom, Category.comp_id]
    change inv (H.map T.mor₁) ≫
        (H.map (T.mor₁ ≫ f) ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso A i).hom.app I) = _
    rw [H.map_comp]
    change inv (H.map T.mor₁) ≫
        ((H.map T.mor₁ ≫ H.map f) ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso A i).hom.app I) =
      H.map f ≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso A i).hom.app I
    simpa only [Category.assoc] using
      IsIso.inv_hom_id_assoc (H.map T.mor₁)
        (H.map f ≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso A i).hom.app I)
  change Function.Bijective (DerivedCategory.homToSingleAddHom T.obj₂ i I)
  rw [← heq]
  exact E.bijective

/-- The original homology map to an injective coefficient single is an
additive equivalence, derived from its native truncation triangle. -/
def DerivedCategory.homToInjectiveSingleAddEquiv
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    (K : DerivedCategory A) (i : ℤ) (I : A) [Injective I] :
    (K ⟶ (DerivedCategory.singleFunctor A i).obj I) ≃+
      ((DerivedCategory.homologyFunctor A i).obj K ⟶ I) :=
  AddEquiv.ofBijective (DerivedCategory.homToSingleAddHom K i I)
    (DerivedCategory.homToSingleAddHom_bijective_of_injective K i I)

private theorem cmCurvePurityTransport_eq_trace
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A] [HasExt A]
    {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    {S : Type*} [CommRing S] [Linear S A] [Linear S B]
    (G : DerivedCategory.Plus A ⥤ DerivedCategory B) [G.CommShift ℤ]
    (W : A) (K : DerivedCategory A) (N : B) (n c : ℕ)
    (hc : (c : ℤ) = (n : ℤ) - 1)
    (E : K ≅ (DerivedCategory.singleFunctor A ((n : ℤ) - 1)).obj W)
    (Φ : ∀ (F : A) (q : ℕ),
      ((DerivedCategory.singleFunctor A 0).obj F ⟶ K⟦(q : ℤ)⟧) →ₗ[S]
        (G.obj ((DerivedCategory.Plus.singleFunctor A 0).obj F) ⟶
          ((DerivedCategory.singleFunctor B (n : ℤ)).obj N)⟦(q : ℤ)⟧))
    (hΦ : ∀ (F F' : A) (a b q : ℕ) (η : Ext F F' a)
      (g : (DerivedCategory.singleFunctor A 0).obj F' ⟶ K⟦(b : ℤ)⟧)
      (hab : a + b = q),
      Φ F q (η.hom.comp g (by omega)) =
        (η.homPlus.map G).comp (Φ F' b g) (by omega))
    (F : A) (r : ℕ) (β : Ext F W r) :
    serreLinearMapOfPurity (S := S) F W K
        (G.obj ((DerivedCategory.Plus.singleFunctor A 0).obj F)) N
        n 1 (r + c) r (by omega) E (Φ F (r + c)) β =
      (β.homPlus.map G).comp
        (serreLinearMapOfPurity (S := S) W W K
          (G.obj ((DerivedCategory.Plus.singleFunctor A 0).obj W)) N
          n 1 (0 + c) 0 (by omega) E (Φ W (0 + c)) (Ext.mk₀ (𝟙 W)))
        (by omega) := by
  let δ := purityInputLinearEquiv (S := S) W W K ((n : ℤ) - 1) E (0 + c) 0
    (by omega) (Ext.mk₀ (𝟙 W))
  have hinput := purityInputLinearEquiv_eq_hom_comp_of_degree (S := S)
    F W K ((n : ℤ) - 1) (0 + c) (r + c) r (by omega) (by omega) E β
  have hout := singleReindexIso_output_inv N (n : ℤ) 1
    ((0 + c : ℕ) : ℤ) ((r + c : ℕ) : ℤ) (r : ℤ) (by omega) (by omega)
  rw [serreLinearMapOfPurity_apply, serreLinearMapOfPurity_apply]
  change Φ F (r + c)
      (purityInputLinearEquiv (S := S) F W K ((n : ℤ) - 1) E (r + c) r
        (by omega) β) ≫
      (singleReindexIso N (n : ℤ) ((r + c : ℕ) : ℤ) ((r : ℤ) - 1)
        (by omega)).inv =
    (β.homPlus.map G).comp
      (Φ W (0 + c) δ ≫
        (singleReindexIso N (n : ℤ) ((0 + c : ℕ) : ℤ) ((0 : ℤ) - 1)
          (by omega)).inv) (by omega)
  rw [hinput, hΦ F W r (0 + c) (r + c) β δ (by omega)]
  simp only [ShiftedHom.comp, Functor.map_comp, Category.assoc]
  rw [hout]
  rfl

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.isQuasicoherent_unit

/-- The standard derived-category model for modules over the coefficient ring. -/
local instance cmCurveSerreModuleDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

variable (k : Type u) [Field k] (ι : Type u)
    {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (hCM : ∀ x : C, IsClosed ({x} : Set C) →
      ∃ b ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk x),
        IsSMulRegular (C.presheaf.stalk x) b ∧
          (Ideal.span {b}).radical = IsLocalRing.maximalIdeal (C.presheaf.stalk x))

/-- The literal original unit, with its scheme-module category fixed
before inferring Ext and native derived endpoints. -/
abbrev cmCurveSerreUnit (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The actual structural field action along the chosen projective embedding. -/
abbrev cmCurveSerreScalar : k →+* Γ(C, ⊤) :=
  j.appTop.hom.comp
    ((toSpec k ι).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)

/-- The original derived direct image of an arbitrary source module single. -/
abbrev cmCurveSerreDirectImage (F : C.Modules) :
    DerivedCategory (Spec (.of k)).Modules :=
  (derivedPushforwardPlus (j ≫ toSpec k ι) ⋙ DerivedCategory.Plus.ι).obj
    ((DerivedCategory.Plus.singleFunctor C.Modules 0).obj F)

/-- The actual canonical reconstruction viewed in the full derived category. -/
def cmCurveSerreCanonicalIso :
    DerivedCategory.Plus.ι.obj (cmCurveDualizingObject k ι j n) ≅
      (DerivedCategory.singleFunctor C.Modules ((n : ℤ) - 1)).obj
        (cmCurveCanonicalModule k ι j n) :=
  DerivedCategory.Plus.ι.mapIso (cmCurveCanonicalIso k ι j n e hCM)

/-- The original unit-coefficient curve Serre map, transported through the
actual canonical reconstruction and both native single-shift comparisons. -/
def cmCurveSerreDerivedLinearMap (F : C.Modules) (r : ℕ) (hn : 1 ≤ n) :
    letI := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    letI := moduleCategoryLinearOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
    Ext.{u + 1} F (cmCurveCanonicalModule k ι j n) r →ₗ[k]
      (cmCurveSerreDirectImage k ι j F ⟶
        ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj
          (SheafOfModules.unit (Spec (.of k)).ringCatSheaf))⟦(r : ℤ) - 1⟧) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCategoryLinearOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  exact serreLinearMapOfPurity F (cmCurveCanonicalModule k ι j n)
    (DerivedCategory.Plus.ι.obj (cmCurveDualizingObject k ι j n))
    (cmCurveSerreDirectImage k ι j F)
    (SheafOfModules.unit (Spec (.of k)).ringCatSheaf)
    n 1 (r + (n - 1)) r (serreDegree_eq n 1 r hn)
    (cmCurveSerreCanonicalIso k ι j n e hCM)
    (relativeClosedEmbeddingSerreLinearMap j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
      (IsPullback.id_horiz (toSpec k ι)) (Scheme.ΓSpecIso (.of k)).inv.hom
      n e (SheafOfModules.unit (Spec (.of k)).ringCatSheaf) F (r + (n - 1)))

/-- The forward formula displays the original Serre map, the inverse
homology-normalized reconstruction, and the installed integer shifts. -/
theorem cmCurveSerreDerivedLinearMap_apply (F : C.Modules) (r : ℕ) (hn : 1 ≤ n)
    (β : Ext.{u + 1} F (cmCurveCanonicalModule k ι j n) r) :
    cmCurveSerreDerivedLinearMap k ι j n e hCM F r hn β =
      relativeClosedEmbeddingSerreMap j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
        (IsPullback.id_horiz (toSpec k ι)) n e
        (SheafOfModules.unit (Spec (.of k)).ringCatSheaf) F (r + (n - 1))
        (β.hom ≫
          (singleReindexIso (cmCurveCanonicalModule k ι j n)
            ((n : ℤ) - 1) ((r + (n - 1) : ℕ) : ℤ) (r : ℤ)
            (serreDegree_eq n 1 r hn)).hom ≫
          ((cmCurveSerreCanonicalIso k ι j n e hCM).inv)⟦((r + (n - 1) : ℕ) : ℤ)⟧') ≫
        (@singleReindexIso (Spec (.of k)).Modules _ _
          (AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory (Spec (.of k)))
          (SheafOfModules.unit (Spec (.of k)).ringCatSheaf)
          (n : ℤ) ((r + (n - 1) : ℕ) : ℤ) ((r : ℤ) - 1) (by omega)).inv := rfl

/-- Coherent sources give bijectivity of the same transported original map;
concentration is proved from the displayed regular-parameter hypothesis. -/
theorem cmCurveSerreDerivedLinearMap_bijective (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (r : ℕ) (hn : 1 ≤ n) :
    Function.Bijective (cmCurveSerreDerivedLinearMap k ι j n e hCM F r hn) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCategoryLinearOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  apply serreLinearMapOfPurity_bijective
  exact relativeClosedEmbeddingSerreMap_bijective j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
    (IsPullback.id_horiz (toSpec k ι)) n e
    (SheafOfModules.unit (Spec (.of k)).ringCatSheaf) F hF (r + (n - 1))

/-- The coherent unit-coefficient curve duality into the original base-derived
Hom, with the original Serre comparison as its displayed forward map. -/
def cmCurveSerreDerivedDuality (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (r : ℕ) (hn : 1 ≤ n) :
    letI := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    letI := moduleCategoryLinearOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
    Ext.{u + 1} F (cmCurveCanonicalModule k ι j n) r ≃ₗ[k]
      (cmCurveSerreDirectImage k ι j F ⟶
        ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj
          (SheafOfModules.unit (Spec (.of k)).ringCatSheaf))⟦(r : ℤ) - 1⟧) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCategoryLinearOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  exact LinearEquiv.ofBijective
    (cmCurveSerreDerivedLinearMap k ι j n e hCM F r hn)
    (cmCurveSerreDerivedLinearMap_bijective k ι j n e hCM F hF r hn)

/-- Packaging the proved bijection does not change the original forward arrow. -/
theorem cmCurveSerreDerivedDuality_apply (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (r : ℕ) (hn : 1 ≤ n)
    (β : Ext.{u + 1} F (cmCurveCanonicalModule k ι j n) r) :
    cmCurveSerreDerivedDuality k ι j n e hCM F hF r hn β =
      cmCurveSerreDerivedLinearMap k ι j n e hCM F r hn β := rfl

/-- The original degree-zero canonical identity determines one normalized
curve trace arrow before any identification of its cohomology with `k`. -/
def cmCurveSerreDerivedTrace (hn : 1 ≤ n) :
    cmCurveSerreDirectImage k ι j (cmCurveCanonicalModule k ι j n) ⟶
      ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj
        (SheafOfModules.unit (Spec (.of k)).ringCatSheaf))⟦(0 : ℤ) - 1⟧ :=
  cmCurveSerreDerivedLinearMap k ι j n e hCM
    (cmCurveCanonicalModule k ι j n) 0 hn (Ext.mk₀ (𝟙 _))

/-- Every Ext degree is composition with the same original normalized
trace, retaining the native shifted-Hom composition and its signs. -/
theorem cmCurveSerreDerivedLinearMap_eq_trace (F : C.Modules) (r : ℕ) (hn : 1 ≤ n)
    (β : Ext.{u + 1} F (cmCurveCanonicalModule k ι j n) r) :
    cmCurveSerreDerivedLinearMap k ι j n e hCM F r hn β =
      (β.homPlus.map (derivedPushforwardPlus (j ≫ toSpec k ι) ⋙
        DerivedCategory.Plus.ι)).comp
        (cmCurveSerreDerivedTrace k ι j n e hCM hn) (by omega) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCategoryLinearOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  exact cmCurvePurityTransport_eq_trace (S := k)
    (derivedPushforwardPlus (j ≫ toSpec k ι) ⋙ DerivedCategory.Plus.ι)
    (cmCurveCanonicalModule k ι j n)
    (DerivedCategory.Plus.ι.obj (cmCurveDualizingObject k ι j n))
    (SheafOfModules.unit (Spec (.of k)).ringCatSheaf) n (n - 1) (by omega)
    (cmCurveSerreCanonicalIso k ι j n e hCM)
    (fun T q => relativeClosedEmbeddingSerreLinearMap j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
      (IsPullback.id_horiz (toSpec k ι)) (Scheme.ΓSpecIso (.of k)).inv.hom
      n e (SheafOfModules.unit (Spec (.of k)).ringCatSheaf) T q)
    (by
      intro T T' a b q η g hab
      change relativeClosedEmbeddingSerreMap j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
          (IsPullback.id_horiz (toSpec k ι)) n e
          (SheafOfModules.unit (Spec (.of k)).ringCatSheaf) T q
          (η.hom.comp g (by omega)) =
        (η.homPlus.map (derivedPushforwardPlus (j ≫ toSpec k ι) ⋙
          DerivedCategory.Plus.ι)).comp
          (relativeClosedEmbeddingSerreMap j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
            (IsPullback.id_horiz (toSpec k ι)) n e
            (SheafOfModules.unit (Spec (.of k)).ringCatSheaf) T' b g) (by omega)
      exact relativeClosedEmbeddingSerreMap_comp j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
        (IsPullback.id_horiz (toSpec k ι)) n e
        (SheafOfModules.unit (Spec (.of k)).ringCatSheaf) η g hab)
    F r β

/-- The reindexed original comparison preserves arbitrary Yoneda
precomposition with its native unsigned Ext products and shifted signs. -/
theorem cmCurveSerreDerivedLinearMap_comp {F F' : C.Modules} {a b r : ℕ}
    (hn : 1 ≤ n) (η : Ext.{u + 1} F F' a)
    (β : Ext.{u + 1} F' (cmCurveCanonicalModule k ι j n) b) (hab : a + b = r) :
    cmCurveSerreDerivedLinearMap k ι j n e hCM F r hn (η.comp β hab) =
      (η.homPlus.map (derivedPushforwardPlus (j ≫ toSpec k ι) ⋙
        DerivedCategory.Plus.ι)).comp
        (cmCurveSerreDerivedLinearMap k ι j n e hCM F' b hn β) (by omega) := by
  rw [cmCurveSerreDerivedLinearMap_eq_trace, cmCurveSerreDerivedLinearMap_eq_trace,
    Ext.homPlus_comp, ShiftedHom.map_comp]
  exact ShiftedHom.comp_assoc _ _ _ (by omega) (by omega) (by omega)

/-- In degree zero, Yoneda naturality is exactly the original derived
pushforward of the source module morphism. -/
theorem cmCurveSerreDerivedLinearMap_precomp {F F' : C.Modules}
    (f : F ⟶ F') (r : ℕ) (hn : 1 ≤ n)
    (β : Ext.{u + 1} F' (cmCurveCanonicalModule k ι j n) r) :
    cmCurveSerreDerivedLinearMap k ι j n e hCM F r hn
        ((Ext.mk₀ f).comp β (Nat.zero_add r)) =
      (derivedPushforwardPlus (j ≫ toSpec k ι) ⋙ DerivedCategory.Plus.ι).map
          ((DerivedCategory.Plus.singleFunctor C.Modules 0).map f) ≫
        cmCurveSerreDerivedLinearMap k ι j n e hCM F' r hn β := by
  let G := derivedPushforwardPlus (j ≫ toSpec k ι) ⋙ DerivedCategory.Plus.ι
  let γ := cmCurveSerreDerivedLinearMap k ι j n e hCM F' r hn β
  have h := cmCurveSerreDerivedLinearMap_comp k ι j n e hCM hn
    (Ext.mk₀ f) β (Nat.zero_add r)
  have hm : (Ext.mk₀ f).homPlus.map G = ShiftedHom.mk₀ (0 : ℤ) rfl
      (G.map ((DerivedCategory.Plus.singleFunctor C.Modules 0).map f)) := by
    rw [Ext.homPlus_mk₀]
    exact ShiftedHom.map_mk₀ (0 : ℤ) rfl _ G
  exact h.trans ((congrArg (fun z : ShiftedHom
      (G.obj ((DerivedCategory.Plus.singleFunctor C.Modules 0).obj F))
      (G.obj ((DerivedCategory.Plus.singleFunctor C.Modules 0).obj F')) (0 : ℤ) =>
        z.comp γ (show ((r : ℤ) - 1) + 0 = (r : ℤ) - 1 by omega)) hm).trans
    (ShiftedHom.mk₀_comp (0 : ℤ) rfl _ γ))

/-- The actual module-valued derived sections of the original source module single. -/
abbrev cmCurveSerreDerivedSections (F : C.Modules) : DerivedCategory (ModuleCat.{u} k) :=
  ((moduleGlobalSectionsFunctorOfHom C
      ((j ≫ toSpec k ι).appTop.hom.comp (Scheme.ΓSpecIso (.of
        k)).inv.hom)).rightDerivedFunctorPlus
      ⋙ DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor C.Modules 0).obj F)

/-- The original cohomology carrier with the actual structural field action. -/
abbrev cmCurveSerreCohomology (F : C.Modules) (i : ℕ) : ModuleCat.{u + 1} k :=
  (moduleCohomologyFunctorOfHom C
    ((j ≫ toSpec k ι).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom) i).obj F

/-- Actual affine unit sections are `k` by the original spectrum/global-sections
isomorphism, with its native structural scalar action. -/
def cmCurveSerreSpecUnitSectionsIso :
    (moduleSpecΓFunctor (R := .of k)).obj
      (SheafOfModules.unit (Spec (.of k)).ringCatSheaf) ≅ ModuleCat.of k k := by
  let E := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
  let L : ((moduleSpecΓFunctor (R := .of k)).obj
      (SheafOfModules.unit (Spec (.of k)).ringCatSheaf)) ≃ₗ[k] k :=
    { __ := E.toAddEquiv
      map_smul' r x := by
        change E (E.symm r * (show Γ(Spec (.of k), ⊤) from x)) =
          r * E (show Γ(Spec (.of k), ⊤) from x)
        rw [map_mul, E.apply_symm_apply] }
  exact L.toModuleIso

/-- The original resolution-section equivalence and coefficient isomorphism
transport homology functionals to functionals on actual sheaf cohomology. -/
def cmCurveSerreHomologyDualAddEquiv (F : C.Modules)
    (i : ℕ) (N : ModuleCat.{u} k) (eN : N ≅ ModuleCat.of k k) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) (i : ℤ)).obj
        (cmCurveSerreDerivedSections k ι j F) ⟶ N) ≃+
      Module.Dual k (cmCurveSerreCohomology k ι j F i) := by
  letI := moduleCohomologyModuleOfHom C
    ((j ≫ toSpec k ι).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom) F i
  let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv C
    ((j ≫ toSpec k ι).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
    (injectiveResolution F) i
  exact ((ModuleCat.homLinearEquiv (S := k)).trans
    (LinearEquiv.arrowCongr E eN.toLinearEquiv)).toAddEquiv

/-- The original chain of six additive comparisons, checked on abstract
carriers before the native cohomology specialization. -/
def cmCurveAdditiveComparisonOfSix
    {X A B C D E Y : Type*}
    [AddCommGroup X] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup D] [AddCommGroup E] [AddCommGroup Y]
    (e₀ : X ≃+ A) (e₁ : A ≃+ B) (e₂ : B ≃+ C)
    (e₃ : C ≃+ D) (e₄ : D ≃+ E) (e₅ : E ≃+ Y) : X ≃+ Y :=
  e₀.trans (e₁.trans (e₂.trans (e₃.trans (e₄.trans e₅))))

/-- The same additive constructor retains its actual forward composite. -/
theorem cmCurveAdditiveComparisonOfSix_apply
    {X A B C D E Y : Type*}
    [AddCommGroup X] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup D] [AddCommGroup E] [AddCommGroup Y]
    (e₀ : X ≃+ A) (e₁ : A ≃+ B) (e₂ : B ≃+ C)
    (e₃ : C ≃+ D) (e₄ : D ≃+ E) (e₅ : E ≃+ Y) (x : X) :
    cmCurveAdditiveComparisonOfSix e₀ e₁ e₂ e₃ e₄ e₅ x =
      e₅ (e₄ (e₃ (e₂ (e₁ (e₀ x))))) := rfl

/-- The unchanged affine Hom comparison, native injective-target homology
map, and original section-resolution comparison extract actual cohomology duals. -/
def cmCurveSerreCohomologyAddEquiv (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (r : ℕ) (hr : r ≤ 1) (hn : 1 ≤ n) :
    Ext.{u + 1} F (cmCurveCanonicalModule k ι j n) r ≃+
      Module.Dual k (cmCurveSerreCohomology k ι j F (1 - r)) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCategoryLinearOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  letI : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
  let q := r + (n - 1)
  let O : (Spec (.of k)).Modules := SheafOfModules.unit (Spec (.of k)).ringCatSheaf
  let N := (moduleSpecΓFunctor (R := .of k)).obj O
  letI : Module.Injective k N := Module.injective_of_isSemisimpleRing k N
  letI : Injective N := Module.injective_object_of_injective_module k N
  let E := purityInputLinearEquiv (S := k) F (cmCurveCanonicalModule k ι j n)
    (DerivedCategory.Plus.ι.obj (cmCurveDualizingObject k ι j n)) ((n : ℤ) - 1)
    (cmCurveSerreCanonicalIso k ι j n e hCM) q r (by dsimp [q]; omega)
  let Φ := relativeClosedEmbeddingSerreDuality j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
    (IsPullback.id_horiz (toSpec k ι)) (Scheme.ΓSpecIso (.of k)).inv.hom
    n e O F hF q
  let A := moduleSpecDerivedPushforwardHomAddEquiv (j ≫ toSpec k ι) F O n q
  let T := ((DerivedCategory.singleFunctors (ModuleCat.{u} k)).shiftIso
    (q : ℤ) ((1 - r : ℕ) : ℤ) (n : ℤ) (by dsimp [q]; omega)).app N
  exact cmCurveAdditiveComparisonOfSix E.toAddEquiv Φ.toAddEquiv A
    (Linear.homCongr k (Iso.refl _) T).toAddEquiv
    (DerivedCategory.homToInjectiveSingleAddEquiv (cmCurveSerreDerivedSections k ι j F)
      ((1 - r : ℕ) : ℤ) N)
    (cmCurveSerreHomologyDualAddEquiv k ι j F (1 - r) N
      (cmCurveSerreSpecUnitSectionsIso k))

/-- The native Hom-to-single homology map has its original functorial value. -/
theorem _root_.DerivedCategory.cmCurve_homToSingleAddHom_apply
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    (K : DerivedCategory A) (i : ℤ) (N : A)
    (f : K ⟶ (DerivedCategory.singleFunctor A i).obj N) :
    DerivedCategory.homToSingleAddHom K i N f =
      (DerivedCategory.homologyFunctor A i).map f ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso A i).hom.app N := rfl

/-- Native Hom transport by a target iso has its original postcomposition
value when the source iso is the identity. -/
theorem cmCurveHomCongrRefl_apply
    {A : Type*} [Category* A] [Preadditive A]
    {k : Type*} [CommRing k] [Linear k A]
    {X Y Z : A} (E : Y ≅ Z) (f : X ⟶ Y) :
    Linear.homCongr k (Iso.refl X) E f = f ≫ E.hom := by
  simpa only [Iso.refl_inv, Category.id_comp] using
    (Linear.homCongr_apply k (Iso.refl X) E f)

/-- The unchanged cohomology comparison has its original affine,
homology, and resolution-section value, through the shared constructor. -/
theorem cmCurveSerreCohomologyAddEquiv_apply (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (r : ℕ) (hr : r ≤ 1) (hn : 1 ≤ n)
    (β : Ext.{u + 1} (C := C.Modules) F (cmCurveCanonicalModule k ι j n) r) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    let := moduleCategoryLinearOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
    let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
    let O : (Spec (.of k)).Modules := cmCurveSerreUnit (Spec (.of k))
    let N := (moduleSpecΓFunctor (R := .of k)).obj O
    let q := r + (n - 1)
    let E := purityInputLinearEquiv (S := k) F (cmCurveCanonicalModule k ι j n)
      (DerivedCategory.Plus.ι.obj (cmCurveDualizingObject k ι j n)) ((n : ℤ) - 1)
      (cmCurveSerreCanonicalIso k ι j n e hCM) q r (by dsimp [q]; omega)
    let Φ := relativeClosedEmbeddingSerreDuality j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
      (IsPullback.id_horiz (toSpec k ι)) (Scheme.ΓSpecIso (.of k)).inv.hom
      n e O F hF q
    let A := moduleSpecDerivedPushforwardHomAddEquiv (j ≫ toSpec k ι) F O n q
    let T := ((DerivedCategory.singleFunctors (ModuleCat.{u} k)).shiftIso
      (q : ℤ) ((1 - r : ℕ) : ℤ) (n : ℤ) (by dsimp [q]; omega)).app N
    cmCurveSerreCohomologyAddEquiv k ι j n e hCM F hF r hr hn β =
      cmCurveSerreHomologyDualAddEquiv k ι j F (1 - r) N
        (cmCurveSerreSpecUnitSectionsIso k)
        ((DerivedCategory.homToSingleAddHom (cmCurveSerreDerivedSections k ι j F)
          ((1 - r : ℕ) : ℤ) N) (A (Φ (E β)) ≫ T.hom)) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCategoryLinearOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
  let O : (Spec (.of k)).Modules := cmCurveSerreUnit (Spec (.of k))
  let N := (moduleSpecΓFunctor (R := .of k)).obj O
  let : Module.Injective k N := Module.injective_of_isSemisimpleRing k N
  let : Injective N := Module.injective_object_of_injective_module k N
  let q := r + (n - 1)
  let E := purityInputLinearEquiv (S := k) F (cmCurveCanonicalModule k ι j n)
    (DerivedCategory.Plus.ι.obj (cmCurveDualizingObject k ι j n)) ((n : ℤ) - 1)
    (cmCurveSerreCanonicalIso k ι j n e hCM) q r (by dsimp [q]; omega)
  let Φ := relativeClosedEmbeddingSerreDuality j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
    (IsPullback.id_horiz (toSpec k ι)) (Scheme.ΓSpecIso (.of k)).inv.hom
    n e O F hF q
  let A := moduleSpecDerivedPushforwardHomAddEquiv (j ≫ toSpec k ι) F O n q
  let T := ((DerivedCategory.singleFunctors (ModuleCat.{u} k)).shiftIso
    (q : ℤ) ((1 - r : ℕ) : ℤ) (n : ℤ) (by dsimp [q]; omega)).app N
  let H := DerivedCategory.homToInjectiveSingleAddEquiv
    (cmCurveSerreDerivedSections k ι j F) ((1 - r : ℕ) : ℤ) N
  let S := cmCurveSerreHomologyDualAddEquiv k ι j F (1 - r) N
    (cmCurveSerreSpecUnitSectionsIso k)
  have h := cmCurveAdditiveComparisonOfSix_apply E.toAddEquiv Φ.toAddEquiv A
    (Linear.homCongr k (Iso.refl _) T).toAddEquiv H S β
  exact h.trans (congrArg (fun f => S (H f))
    (cmCurveHomCongrRefl_apply T (A (Φ (E β)))))

/-- The coherent original derived Serre arrow uses the same canonical
input and the same original duality forward map as the additive comparison. -/
theorem cmCurveSerreDerivedLinearMap_input_apply (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (r : ℕ) (hn : 1 ≤ n)
    (β : Ext.{u + 1} (C := C.Modules) F (cmCurveCanonicalModule k ι j n) r) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    let := moduleCategoryLinearOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
    let O : (Spec (.of k)).Modules := cmCurveSerreUnit (Spec (.of k))
    let q := r + (n - 1)
    let E := purityInputLinearEquiv (S := k) F (cmCurveCanonicalModule k ι j n)
      (DerivedCategory.Plus.ι.obj (cmCurveDualizingObject k ι j n)) ((n : ℤ) - 1)
      (cmCurveSerreCanonicalIso k ι j n e hCM) q r (by dsimp [q]; omega)
    let Φ := relativeClosedEmbeddingSerreDuality j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
      (IsPullback.id_horiz (toSpec k ι)) (Scheme.ΓSpecIso (.of k)).inv.hom
      n e O F hF q
    cmCurveSerreDerivedLinearMap k ι j n e hCM F r hn β =
      Φ (E β) ≫ (singleReindexIso O (n : ℤ) (q : ℤ) ((r : ℤ) - 1) (by omega)).inv := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCategoryLinearOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  exact serreLinearMapOfPurity_apply F (cmCurveCanonicalModule k ι j n)
    (DerivedCategory.Plus.ι.obj (cmCurveDualizingObject k ι j n))
    (cmCurveSerreDirectImage k ι j F) (cmCurveSerreUnit (Spec (.of k)))
    n 1 (r + (n - 1)) r (serreDegree_eq n 1 r hn)
    (cmCurveSerreCanonicalIso k ι j n e hCM)
    (relativeClosedEmbeddingSerreLinearMap j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
      (IsPullback.id_horiz (toSpec k ι)) (Scheme.ΓSpecIso (.of k)).inv.hom
      n e (cmCurveSerreUnit (Spec (.of k))) F (r + (n - 1))) β

/-- The original evaluation pipeline over abstract module carriers. -/
def cmCurveEvaluationOfEquivs {k : Type*} [CommRing k]
    {X A B S : Type*} [AddCommGroup X] [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup S] [Module k X] [Module k A] [Module k B] [Module k S]
    (c : S →ₗ[k] k) (U : A ≃ₗ[k] S) (E : A ≃ₗ[k] B) (P : X →ₗ[k] B) : X →ₗ[k] k :=
  c.comp (U.toLinearMap.comp (E.symm.toLinearMap.comp P))

/-- The staged evaluation retains exactly its original composite value. -/
theorem cmCurveEvaluationOfEquivs_apply {k : Type*} [CommRing k]
    {X A B S : Type*} [AddCommGroup X] [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup S] [Module k X] [Module k A] [Module k B] [Module k S]
    (c : S →ₗ[k] k) (U : A ≃ₗ[k] S) (E : A ≃ₗ[k] B) (P : X →ₗ[k] B) (x : X) :
    cmCurveEvaluationOfEquivs c U E P x = c (U (E.symm (P x))) := rfl

/-- The original affine unit coefficient is the original ΓSpec map on values. -/
theorem cmCurveSerreSpecUnitSectionsIso_apply
    (x : (moduleSpecΓFunctor (R := .of k)).obj (cmCurveSerreUnit (Spec (.of k)))) :
    (cmCurveSerreSpecUnitSectionsIso k).hom x =
      (Scheme.ΓSpecIso (.of k)).hom (show Γ(Spec (.of k), ⊤) from x) := rfl

/-- The original native single-unit evaluator together with its
proved original preimage formula. -/
structure CmCurveUnitEvaluationData
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    {k : Type*} [CommRing k] [Linear k A] [Linear k B] [HasShift B ℤ]
    (S : A ⥤ B) [S.Full] [S.Faithful] [S.Additive] [S.Linear k]
    (O : A) (X : B) (η : S.obj O ⟶ X)
    {N : Type*} [AddCommGroup N] [Module k N]
    (U : (O ⟶ O) ≃ₗ[k] N) (c : N →ₗ[k] k) where
  /-- The original linear composite through the native single preimage. -/
  toLinearMap : (X ⟶ (S.obj O)⟦(0 : ℤ)⟧) →ₗ[k] k
  /-- Its value retains the original structural arrow and native zero shift. -/
  apply (φ : X ⟶ (S.obj O)⟦(0 : ℤ)⟧) :
    toLinearMap φ = c (U (S.preimage
      (η ≫ φ ≫ (shiftFunctorZero B ℤ).hom.app (S.obj O))))

/-- Construct both the native evaluator and its original-map formula from
the same fully faithful single functor and endpoint data. -/
def cmCurveUnitEvaluationPacket
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    {k : Type*} [CommRing k] [Linear k A] [Linear k B] [HasShift B ℤ]
    (S : A ⥤ B) [S.Full] [S.Faithful] [S.Additive] [S.Linear k]
    (O : A) (X : B) (η : S.obj O ⟶ X)
    {N : Type*} [AddCommGroup N] [Module k N]
    (U : (O ⟶ O) ≃ₗ[k] N) (c : N →ₗ[k] k) :
    CmCurveUnitEvaluationData S O X η U c := by
  let E : (O ⟶ O) ≃ₗ[k] (S.obj O ⟶ S.obj O) :=
    LinearEquiv.ofBijective (S.mapLinearMap k) ⟨S.map_injective, S.map_surjective⟩
  let P : (X ⟶ (S.obj O)⟦(0 : ℤ)⟧) →ₗ[k] (S.obj O ⟶ S.obj O) :=
    (Linear.rightComp k (S.obj O)
      ((shiftFunctorZero B ℤ).hom.app (S.obj O))).comp
        (Linear.leftComp k ((S.obj O)⟦(0 : ℤ)⟧) η)
  refine ⟨cmCurveEvaluationOfEquivs c U E P, ?_⟩
  intro φ
  let z : S.obj O ⟶ S.obj O :=
    η ≫ φ ≫ (shiftFunctorZero B ℤ).hom.app (S.obj O)
  have hP : P φ = z := by
    simp only [P, LinearMap.comp_apply, Linear.leftComp_apply,
      Linear.rightComp_apply, z, Category.assoc]
  have hE : E.symm z = S.preimage z := by
    apply S.map_injective
    exact (E.apply_symm_apply z).trans (S.map_preimage z).symm
  exact (cmCurveEvaluationOfEquivs_apply c U E P φ).trans
    (congrArg (fun f => c (U f)) ((congrArg E.symm hP).trans hE))

/-- Precompose with the original structural derived unit, return through
the native fully faithful single, and evaluate the original morphism at `1`. -/
def cmCurveSerreUnitEvaluationLinearMap :
    letI := moduleCategoryLinearOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
    (cmCurveSerreDirectImage k ι j (SheafOfModules.unit C.ringCatSheaf) ⟶
      ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj
        (SheafOfModules.unit (Spec (.of k)).ringCatSheaf))⟦(0 : ℤ)⟧) →ₗ[k] k := by
  let Y := Spec (.of k)
  let O : Y.Modules := cmCurveSerreUnit Y
  let := moduleCategoryLinearOfHom Y (Scheme.ΓSpecIso (.of k)).inv.hom
  let S := DerivedCategory.singleFunctor Y.Modules 0
  let X := cmCurveSerreDirectImage k ι j (cmCurveSerreUnit C)
  let η : S.obj O ⟶ X := DerivedCategory.Plus.ι.map
    (moduleDerivedPushforwardUnit Y (j ≫ toSpec k ι))
  let U : (O ⟶ O) ≃ₗ[k] (moduleSpecΓFunctor (R := .of k)).obj O :=
    unitHomGlobalSectionsLinearEquivOfHom Y (Scheme.ΓSpecIso (.of k)).inv.hom O
  exact (cmCurveUnitEvaluationPacket S O X η U
    (cmCurveSerreSpecUnitSectionsIso k).hom.hom).toLinearMap

/-- Evaluation after the original inverse cohomology equivalence has
its native class value on abstract carriers. -/
theorem cmCurveTraceCompInverse_apply
    {k : Type*} [CommRing k] {X H D : Type*}
    [AddCommGroup X] [AddCommGroup H] [AddCommGroup D]
    [Module k X] [Module k H] [Module k D]
    (E : X ≃ₗ[k] H) (Φ : X →ₗ[k] D) (t : D →ₗ[k] k) (x : X) :
    (t.comp (Φ.comp E.symm.toLinearMap)) (E x) = t (Φ x) :=
  congrArg (fun z => t (Φ z)) (E.symm_apply_apply x)

/-- The original unit-coefficient curve trace on actual `H¹`: apply the
same Serre map to its Ext class, precompose with the actual structural
derived unit, then evaluate its original unit-module morphism at `1`.
No structural `H⁰` isomorphism is required to construct this linear map. -/
def cmCurveSerreTrace (hn : 1 ≤ n) :
    letI := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    letI := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j)
      (cmCurveCanonicalModule k ι j n) 1
    Sheaf.H.{u + 1} (moduleAddSheaf C (cmCurveCanonicalModule k ι j n)) 1 →ₗ[k] k := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j)
    (cmCurveCanonicalModule k ι j n) 1
  let := moduleCategoryLinearOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  let O : C.Modules := SheafOfModules.unit C.ringCatSheaf
  let W : C.Modules := cmCurveCanonicalModule k ι j n
  let E : Ext.{u + 1} (C := C.Modules) O W 1 ≃ₗ[k]
      Sheaf.H.{u + 1} (moduleAddSheaf C W) 1 :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) W 1
  let Φ : Ext.{u + 1} (C := C.Modules) O W 1 →ₗ[k]
      (cmCurveSerreDirectImage k ι j O ⟶
        ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj
          (SheafOfModules.unit (Spec (.of k)).ringCatSheaf))⟦(0 : ℤ)⟧) :=
    cmCurveSerreDerivedLinearMap k ι j n e hCM O 1 hn
  exact (cmCurveSerreUnitEvaluationLinearMap k ι j).comp
    (Φ.comp E.symm.toLinearMap)


/-- The already installed trace has its original Ext-class value. -/
theorem cmCurveSerreTrace_apply_ext (hn : 1 ≤ n)
    (β : Ext.{u + 1} (C := C.Modules) (cmCurveSerreUnit C)
      (cmCurveCanonicalModule k ι j n) 1) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j)
      (cmCurveCanonicalModule k ι j n) 1
    cmCurveSerreTrace k ι j n e hCM hn
        (moduleExtCohomologyMap C (cmCurveCanonicalModule k ι j n) 1 β) =
      cmCurveSerreUnitEvaluationLinearMap k ι j
        (cmCurveSerreDerivedLinearMap k ι j n e hCM (cmCurveSerreUnit C) 1 hn β) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j)
    (cmCurveCanonicalModule k ι j n) 1
  let := moduleCategoryLinearOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  let O : C.Modules := cmCurveSerreUnit C
  let W : C.Modules := cmCurveCanonicalModule k ι j n
  let E : Ext.{u + 1} (C := C.Modules) O W 1 ≃ₗ[k]
      Sheaf.H.{u + 1} (moduleAddSheaf C W) 1 :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) W 1
  let Φ := cmCurveSerreDerivedLinearMap k ι j n e hCM O 1 hn
  let t := cmCurveSerreUnitEvaluationLinearMap k ι j
  have hE := moduleExtCohomologyLinearEquivOfCategory_apply C
    (cmCurveSerreScalar k ι j) W 1 β
  exact (congrArg (cmCurveSerreTrace k ι j n e hCM hn) hE.symm).trans
    (cmCurveTraceCompInverse_apply E Φ t β)

end AlgebraicGeometry.Scheme.Cohomology
