/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve.Coefficients
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve.Coefficients.Serre.Affine
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Coefficient

/-!
# Original coefficient-valued Cohen--Macaulay curve Serre duality

The actual own-homology canonical object, original six maps and original
coefficient-valued trace give the curve comparison in degrees zero and one.
The positive Yoneda identity is proved for those same maps; it is not a
compatibility premise. The coefficient may be the specified intrinsic line
and is never oriented as the scalar field.
-/

@[expose] public noncomputable section

universe u v w u' v' w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent RelativeCanonicalReindex

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.isQuasicoherent_unit

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The standard derived-category instance for modules over the original coefficient ring. -/
local instance cmCurveCoefficientSerreModuleDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

private theorem cmCurveCoefficientPurityTransport_eq_trace
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


variable (k : Type u) [Field k] (ι : Type u)
    {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]

variable (n : ℕ) (e : ι ≃ Fin (n + 1))
    (V : ModuleCat.{u} k) [Module.Finite k V] (hV : Module.finrank k V = 1)
    (hCM : ∀ x : C, IsClosed ({x} : Set C) →
      ∃ b ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk x),
        IsSMulRegular (C.presheaf.stalk x) b ∧
          (Ideal.span {b}).radical = IsLocalRing.maximalIdeal (C.presheaf.stalk x))

/-- Full-derived reconstruction of the actual coefficient object's own homology. -/
def cmCurveCoefficientSerreCanonicalIso :
    DerivedCategory.Plus.ι.obj (cmCurveCoefficientDualizingObject k ι j n V) ≅
      (DerivedCategory.singleFunctor C.Modules ((n : ℤ) - 1)).obj
        (cmCurveCoefficientCanonicalModule k ι j n V) :=
  DerivedCategory.Plus.ι.mapIso (cmCurveCoefficientCanonicalIso k ι j n e V hV hCM)

/-- The literal original Serre map with coefficient tilde V, reindexed in curve degree. -/
def cmCurveCoefficientSerreDerivedLinearMap (F : C.Modules) (r : ℕ) (hn : 1 ≤ n) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    let := moduleCategoryLinearOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
    Ext.{u + 1} (C := C.Modules) F (cmCurveCoefficientCanonicalModule k ι j n V) r →ₗ[k]
      (cmCurveSerreDirectImage k ι j F ⟶
        ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj
          (tilde V))⟦(r : ℤ) - 1⟧) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCategoryLinearOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  exact serreLinearMapOfPurity F (cmCurveCoefficientCanonicalModule k ι j n V)
    (DerivedCategory.Plus.ι.obj (cmCurveCoefficientDualizingObject k ι j n V))
    (cmCurveSerreDirectImage k ι j F) (tilde V)
    n 1 (r + (n - 1)) r (serreDegree_eq n 1 r hn)
    (cmCurveCoefficientSerreCanonicalIso k ι j n e V hV hCM)
    (relativeClosedEmbeddingSerreLinearMap j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
      (IsPullback.id_horiz (toSpec k ι)) (Scheme.ΓSpecIso (.of k)).inv.hom
      n e (tilde V) F (r + (n - 1)))

/-- Coherent sources give bijectivity of that same original coefficient-valued map. -/
theorem cmCurveCoefficientSerreDerivedLinearMap_bijective (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (r : ℕ) (hn : 1 ≤ n) :
    Function.Bijective
      (cmCurveCoefficientSerreDerivedLinearMap k ι j n e V hV hCM F r hn) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCategoryLinearOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  apply serreLinearMapOfPurity_bijective
  exact relativeClosedEmbeddingSerreMap_bijective j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
    (IsPullback.id_horiz (toSpec k ι)) n e (tilde V) F hF (r + (n - 1))

/-- The original degree-zero canonical identity determines one normalized
curve trace arrow before any identification of its cohomology with `k`. -/
def cmCurveCoefficientSerreDerivedTrace (hn : 1 ≤ n) :
    cmCurveSerreDirectImage k ι j (cmCurveCoefficientCanonicalModule k ι j n V) ⟶
      ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj
        (tilde V))⟦(0 : ℤ) - 1⟧ :=
  cmCurveCoefficientSerreDerivedLinearMap k ι j n e V hV hCM
    (cmCurveCoefficientCanonicalModule k ι j n V) 0 hn (Ext.mk₀ (𝟙 _))

/-- Every Ext degree is composition with the same original normalized
trace, retaining the native shifted-Hom composition and its signs. -/
theorem cmCurveCoefficientSerreDerivedLinearMap_eq_trace (F : C.Modules) (r : ℕ) (hn : 1 ≤ n)
    (β : Ext.{u + 1} F (cmCurveCoefficientCanonicalModule k ι j n V) r) :
    cmCurveCoefficientSerreDerivedLinearMap k ι j n e V hV hCM F r hn β =
      (β.homPlus.map (derivedPushforwardPlus (j ≫ toSpec k ι) ⋙
        DerivedCategory.Plus.ι)).comp
        (cmCurveCoefficientSerreDerivedTrace k ι j n e V hV hCM hn) (by omega) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCategoryLinearOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  exact cmCurveCoefficientPurityTransport_eq_trace (S := k)
    (derivedPushforwardPlus (j ≫ toSpec k ι) ⋙ DerivedCategory.Plus.ι)
    (cmCurveCoefficientCanonicalModule k ι j n V)
    (DerivedCategory.Plus.ι.obj (cmCurveCoefficientDualizingObject k ι j n V))
    (tilde V) n (n - 1) (by omega)
    (cmCurveCoefficientSerreCanonicalIso k ι j n e V hV hCM)
    (fun T q => relativeClosedEmbeddingSerreLinearMap j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
      (IsPullback.id_horiz (toSpec k ι)) (Scheme.ΓSpecIso (.of k)).inv.hom
      n e (tilde V) T q)
    (by
      intro T T' a b q η g hab
      change relativeClosedEmbeddingSerreMap j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
          (IsPullback.id_horiz (toSpec k ι)) n e
          (tilde V) T q
          (η.hom.comp g (by omega)) =
        (η.homPlus.map (derivedPushforwardPlus (j ≫ toSpec k ι) ⋙
          DerivedCategory.Plus.ι)).comp
          (relativeClosedEmbeddingSerreMap j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
            (IsPullback.id_horiz (toSpec k ι)) n e
            (tilde V) T' b g) (by omega)
      exact relativeClosedEmbeddingSerreMap_comp j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
        (IsPullback.id_horiz (toSpec k ι)) n e
        (tilde V) η g hab)
    F r β

/-- The reindexed original comparison preserves arbitrary Yoneda
precomposition with its native unsigned Ext products and shifted signs. -/
theorem cmCurveCoefficientSerreDerivedLinearMap_comp {F F' : C.Modules} {a b r : ℕ}
    (hn : 1 ≤ n) (η : Ext.{u + 1} F F' a)
    (β : Ext.{u + 1} F' (cmCurveCoefficientCanonicalModule k ι j n V) b) (hab : a + b = r) :
    cmCurveCoefficientSerreDerivedLinearMap k ι j n e V hV hCM F r hn (η.comp β hab) =
      (η.homPlus.map (derivedPushforwardPlus (j ≫ toSpec k ι) ⋙
        DerivedCategory.Plus.ι)).comp
        (cmCurveCoefficientSerreDerivedLinearMap k ι j n e V hV hCM F' b hn β) (by omega) := by
  rw [cmCurveCoefficientSerreDerivedLinearMap_eq_trace,
    cmCurveCoefficientSerreDerivedLinearMap_eq_trace,
    Ext.homPlus_comp, ShiftedHom.map_comp]
  exact ShiftedHom.comp_assoc _ _ _ (by omega) (by omega) (by omega)

/-- The original six-map comparison, with its actual coefficient retained throughout. -/
def cmCurveCoefficientSerreCohomologyAddEquiv (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (r : ℕ) (hr : r ≤ 1) (hn : 1 ≤ n) :
    Ext.{u + 1} (C := C.Modules) F (cmCurveCoefficientCanonicalModule k ι j n V) r ≃+
      (cmCurveSerreCohomology k ι j F (1 - r) →ₗ[k] V) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCategoryLinearOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
  let T : (Spec (.of k)).Modules := tilde V
  let N := (moduleSpecΓFunctor (R := .of k)).obj T
  let : Module.Injective k N := Module.injective_of_isSemisimpleRing k N
  let : Injective N := Module.injective_object_of_injective_module k N
  let q := r + (n - 1)
  let E := purityInputLinearEquiv (S := k) F
    (cmCurveCoefficientCanonicalModule k ι j n V)
    (DerivedCategory.Plus.ι.obj (cmCurveCoefficientDualizingObject k ι j n V))
    ((n : ℤ) - 1) (cmCurveCoefficientSerreCanonicalIso k ι j n e V hV hCM)
    q r (by dsimp [q]; omega)
  let Φ := relativeClosedEmbeddingSerreDuality j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
    (IsPullback.id_horiz (toSpec k ι)) (Scheme.ΓSpecIso (.of k)).inv.hom
    n e T F hF q
  let A := moduleSpecDerivedPushforwardHomAddEquiv (j ≫ toSpec k ι) F T n q
  let S := ((DerivedCategory.singleFunctors (ModuleCat.{u} k)).shiftIso
    (q : ℤ) ((1 - r : ℕ) : ℤ) (n : ℤ) (by dsimp [q]; omega)).app N
  exact cmCurveAdditiveComparisonOfSix E.toAddEquiv Φ.toAddEquiv A
    (Linear.homCongr k (Iso.refl _) S).toAddEquiv
    (DerivedCategory.homToInjectiveSingleAddEquiv (cmCurveSerreDerivedSections k ι j F)
      ((1 - r : ℕ) : ℤ) N)
    (cmCurveCoefficientSerreHomologyTargetAddEquiv k ι j V N
      (cmCurveCoefficientSerreSpecSectionsIso k V) F (1 - r))

/-- The unchanged cohomology comparison has its original affine,
homology, and resolution-section value, through the shared constructor. -/
theorem cmCurveCoefficientSerreCohomologyAddEquiv_apply (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (r : ℕ) (hr : r ≤ 1) (hn : 1 ≤ n)
    (β : Ext.{u + 1} (C := C.Modules) F (cmCurveCoefficientCanonicalModule k ι j n V) r) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    let := moduleCategoryLinearOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
    let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
    let O : (Spec (.of k)).Modules := (tilde V)
    let N := (moduleSpecΓFunctor (R := .of k)).obj O
    let q := r + (n - 1)
    let E := purityInputLinearEquiv (S := k) F (cmCurveCoefficientCanonicalModule k ι j n V)
      (DerivedCategory.Plus.ι.obj (cmCurveCoefficientDualizingObject k ι j n V)) ((n : ℤ) - 1)
      (cmCurveCoefficientSerreCanonicalIso k ι j n e V hV hCM) q r (by dsimp [q]; omega)
    let Φ := relativeClosedEmbeddingSerreDuality j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
      (IsPullback.id_horiz (toSpec k ι)) (Scheme.ΓSpecIso (.of k)).inv.hom
      n e O F hF q
    let A := moduleSpecDerivedPushforwardHomAddEquiv (j ≫ toSpec k ι) F O n q
    let T := ((DerivedCategory.singleFunctors (ModuleCat.{u} k)).shiftIso
      (q : ℤ) ((1 - r : ℕ) : ℤ) (n : ℤ) (by dsimp [q]; omega)).app N
    cmCurveCoefficientSerreCohomologyAddEquiv k ι j n e V hV hCM F hF r hr hn β =
      cmCurveCoefficientSerreHomologyTargetAddEquiv k ι j V N
      (cmCurveCoefficientSerreSpecSectionsIso k V) F (1 - r)
        ((DerivedCategory.homToSingleAddHom (cmCurveSerreDerivedSections k ι j F)
          ((1 - r : ℕ) : ℤ) N) (A (Φ (E β)) ≫ T.hom)) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCategoryLinearOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
  let O : (Spec (.of k)).Modules := (tilde V)
  let N := (moduleSpecΓFunctor (R := .of k)).obj O
  let : Module.Injective k N := Module.injective_of_isSemisimpleRing k N
  let : Injective N := Module.injective_object_of_injective_module k N
  let q := r + (n - 1)
  let E := purityInputLinearEquiv (S := k) F (cmCurveCoefficientCanonicalModule k ι j n V)
    (DerivedCategory.Plus.ι.obj (cmCurveCoefficientDualizingObject k ι j n V)) ((n : ℤ) - 1)
    (cmCurveCoefficientSerreCanonicalIso k ι j n e V hV hCM) q r (by dsimp [q]; omega)
  let Φ := relativeClosedEmbeddingSerreDuality j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
    (IsPullback.id_horiz (toSpec k ι)) (Scheme.ΓSpecIso (.of k)).inv.hom
    n e O F hF q
  let A := moduleSpecDerivedPushforwardHomAddEquiv (j ≫ toSpec k ι) F O n q
  let T := ((DerivedCategory.singleFunctors (ModuleCat.{u} k)).shiftIso
    (q : ℤ) ((1 - r : ℕ) : ℤ) (n : ℤ) (by dsimp [q]; omega)).app N
  let H := DerivedCategory.homToInjectiveSingleAddEquiv
    (cmCurveSerreDerivedSections k ι j F) ((1 - r : ℕ) : ℤ) N
  let S := cmCurveCoefficientSerreHomologyTargetAddEquiv k ι j V N
      (cmCurveCoefficientSerreSpecSectionsIso k V) F (1 - r)
  have h := cmCurveAdditiveComparisonOfSix_apply E.toAddEquiv Φ.toAddEquiv A
    (Linear.homCongr k (Iso.refl _) T).toAddEquiv H S β
  exact h.trans (congrArg (fun f => S (H f))
    (cmCurveHomCongrRefl_apply T (A (Φ (E β)))))

/-- The coherent original derived Serre arrow uses the same canonical
input and the same original duality forward map as the additive comparison. -/
theorem cmCurveCoefficientSerreDerivedLinearMap_input_apply (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (r : ℕ) (hn : 1 ≤ n)
    (β : Ext.{u + 1} (C := C.Modules) F (cmCurveCoefficientCanonicalModule k ι j n V) r) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    let := moduleCategoryLinearOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
    let O : (Spec (.of k)).Modules := (tilde V)
    let q := r + (n - 1)
    let E := purityInputLinearEquiv (S := k) F (cmCurveCoefficientCanonicalModule k ι j n V)
      (DerivedCategory.Plus.ι.obj (cmCurveCoefficientDualizingObject k ι j n V)) ((n : ℤ) - 1)
      (cmCurveCoefficientSerreCanonicalIso k ι j n e V hV hCM) q r (by dsimp [q]; omega)
    let Φ := relativeClosedEmbeddingSerreDuality j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
      (IsPullback.id_horiz (toSpec k ι)) (Scheme.ΓSpecIso (.of k)).inv.hom
      n e O F hF q
    cmCurveCoefficientSerreDerivedLinearMap k ι j n e V hV hCM F r hn β =
      Φ (E β) ≫ (singleReindexIso O (n : ℤ) (q : ℤ) ((r : ℤ) - 1) (by omega)).inv := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCategoryLinearOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  exact serreLinearMapOfPurity_apply F (cmCurveCoefficientCanonicalModule k ι j n V)
    (DerivedCategory.Plus.ι.obj (cmCurveCoefficientDualizingObject k ι j n V))
    (cmCurveSerreDirectImage k ι j F) ((tilde V))
    n 1 (r + (n - 1)) r (serreDegree_eq n 1 r hn)
    (cmCurveCoefficientSerreCanonicalIso k ι j n e V hV hCM)
    (relativeClosedEmbeddingSerreLinearMap j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
      (IsPullback.id_horiz (toSpec k ι)) (Scheme.ΓSpecIso (.of k)).inv.hom
      n e ((tilde V)) F (r + (n - 1))) β

/-- The original additive forward comparison extracts the original
native shifted homology arrow in every complementary curve degree. -/
theorem cmCurveCoefficientSerreCohomologyAddEquiv_moduleHom (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (r : ℕ) (hr : r ≤ 1) (hn : 1 ≤ n)
    (β : Ext.{u + 1} (C := C.Modules) F (cmCurveCoefficientCanonicalModule k ι j n V) r)
    (x : cmCurveSerreCohomology k ι j F (1 - r)) :
    let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F (1 - r)
    let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv C
      (cmCurveSerreScalar k ι j) (injectiveResolution F) (1 - r)
    cmCurveCoefficientSerreCohomologyAddEquiv k ι j n e V hV hCM F hF r hr hn β x =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).shiftMap
        (cmCurveCoefficientSerreModuleHom k ι j V F ((r : ℤ) - 1)
          (cmCurveCoefficientSerreDerivedLinearMap k ι j n e V hV hCM F r hn β))
        ((1 - r : ℕ) : ℤ) 0 (by omega) ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).hom.app
            (V)) (E.symm x) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCategoryLinearOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F (1 - r)
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
  let O : (Spec (.of k)).Modules := (tilde V)
  let N := (moduleSpecΓFunctor (R := .of k)).obj O
  let q := r + (n - 1)
  let i := 1 - r
  let E₀ := purityInputLinearEquiv (S := k) F (cmCurveCoefficientCanonicalModule k ι j n V)
    (DerivedCategory.Plus.ι.obj (cmCurveCoefficientDualizingObject k ι j n V)) ((n : ℤ) - 1)
    (cmCurveCoefficientSerreCanonicalIso k ι j n e V hV hCM) q r (by dsimp [q]; omega)
  let Φ := relativeClosedEmbeddingSerreDuality j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
    (IsPullback.id_horiz (toSpec k ι)) (Scheme.ΓSpecIso (.of k)).inv.hom n e O F hF q
  let A := moduleSpecDerivedPushforwardHomAddEquiv (j ≫ toSpec k ι) F O n q
  let T := ((DerivedCategory.singleFunctors (ModuleCat.{u} k)).shiftIso
    (q : ℤ) (i : ℤ) (n : ℤ) (by dsimp [q, i]; omega)).app N
  let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv C
    (cmCurveSerreScalar k ι j) (injectiveResolution F) i
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0
  let e₀ := (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (ModuleCat.{u} k) 0).hom.app (V)
  let a := Φ (E₀ β)
  have hraw := congrArg (fun l => l x)
    (cmCurveCoefficientSerreCohomologyAddEquiv_apply k ι j n e V hV hCM F hF r hr hn β)
  have hhom := congrArg
    (fun f => cmCurveCoefficientSerreHomologyTargetAddEquiv k ι j V N
      (cmCurveCoefficientSerreSpecSectionsIso k V) F i f x)
    (DerivedCategory.cmCurve_homToSingleAddHom_apply
      (cmCurveSerreDerivedSections k ι j F) (i : ℤ) N (A a ≫ T.hom))
  have hfun := cmCurveCoefficientSerreAffineHom_homology_of_reindex k ι j n e V F hF q i
    ((r : ℤ) - 1) (by dsimp [q]; omega) (by dsimp [i]; omega) a x
  have hmap := congrArg (cmCurveCoefficientSerreModuleHom k ι j V F ((r : ℤ) - 1))
    (cmCurveCoefficientSerreDerivedLinearMap_input_apply k ι j n e V hV hCM F hF r hn β).symm
  have hpoint := congrArg
    (fun f => (H.shiftMap f (i : ℤ) 0 (by dsimp [i]; omega) ≫ e₀) (E.symm x)) hmap
  exact hraw.trans (hhom.trans (hfun.trans hpoint))

/-- The actual V-valued trace is linear before any structural H0 isomorphism. -/
def cmCurveCoefficientSerreTrace (hn : 1 ≤ n) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j)
      (cmCurveCoefficientCanonicalModule k ι j n V) 1
    cmCurveSerreCohomology k ι j (cmCurveCoefficientCanonicalModule k ι j n V) 1 →ₗ[k] V := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let W : C.Modules := cmCurveCoefficientCanonicalModule k ι j n V
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) W 1
  let := moduleCategoryLinearOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  let O : C.Modules := cmCurveSerreUnit C
  let E : Ext.{u + 1} (C := C.Modules) O W 1 ≃ₗ[k]
      cmCurveSerreCohomology k ι j W 1 :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) W 1
  let Φ := cmCurveCoefficientSerreDerivedLinearMap k ι j n e V hV hCM O 1 hn
  exact (cmCurveCoefficientSerreUnitEvaluationLinearMap k ι j V).comp
    (Φ.comp E.symm.toLinearMap)

/-- The actual trace on an original Ext class is the same structural-unit evaluator. -/
theorem cmCurveCoefficientSerreTrace_apply_ext (hn : 1 ≤ n)
    (β : Ext.{u + 1} (C := C.Modules) (cmCurveSerreUnit C)
      (cmCurveCoefficientCanonicalModule k ι j n V) 1) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j)
      (cmCurveCoefficientCanonicalModule k ι j n V) 1
    cmCurveCoefficientSerreTrace k ι j n e V hV hCM hn
      (moduleExtCohomologyMap C (cmCurveCoefficientCanonicalModule k ι j n V) 1 β) =
        cmCurveCoefficientSerreUnitEvaluationLinearMap k ι j V
          (cmCurveCoefficientSerreDerivedLinearMap k ι j n e V hV hCM
            (cmCurveSerreUnit C) 1 hn β) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let W : C.Modules := cmCurveCoefficientCanonicalModule k ι j n V
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) W 1
  let E : Ext.{u + 1} (C := C.Modules) (cmCurveSerreUnit C) W 1 ≃ₗ[k]
      cmCurveSerreCohomology k ι j W 1 :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) W 1
  let Φ := cmCurveCoefficientSerreDerivedLinearMap k ι j n e V hV hCM (cmCurveSerreUnit C) 1 hn
  let t := cmCurveCoefficientSerreUnitEvaluationLinearMap k ι j V
  have hE : E β = moduleExtCohomologyMap C W 1 β :=
    moduleExtCohomologyLinearEquivOfCategory_apply C (cmCurveSerreScalar k ι j) W 1 β
  exact congrArg (fun z => t (Φ z))
    ((congrArg E.symm hE.symm).trans (E.symm_apply_apply β))

/-- Native shifted composition evaluates an original Ext class by the same V-valued trace. -/
theorem cmCurveCoefficientSerreModuleHom_pairing (F : C.Modules) (hn : 1 ≤ n)
    {i r : ℕ} (hir : i + r = 1)
    (a : Ext.{u + 1} (C := C.Modules) (cmCurveSerreUnit C) F i)
    (β : Ext.{u + 1} (C := C.Modules) F (cmCurveCoefficientCanonicalModule k ι j n V) r) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j)
      (cmCurveCoefficientCanonicalModule k ι j n V) 1
    let G := moduleGlobalSectionsFunctorOfHom C (cmCurveSerreScalar k ι j)
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0
    let E₀ := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).app
      (ModuleCat.of k k)
    let E₁ := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).app V
    let u := DerivedCategory.Plus.ι.map (moduleDerivedStructureUnit C (cmCurveSerreScalar k ι j))
    (H.shiftMap (cmCurveCoefficientSerreModuleHom k ι j V F ((r : ℤ) - 1)
        (cmCurveCoefficientSerreDerivedLinearMap k ι j n e V hV hCM F r hn β))
      (i : ℤ) 0 (by omega) ≫ E₁.hom)
      (H.shiftMap (a.homPlus.map (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι))
        0 (i : ℤ) (by omega) (H.map u (E₀.inv (1 : k)))) =
      cmCurveCoefficientSerreTrace k ι j n e V hV hCM hn
        (moduleExtCohomologyMap C (cmCurveCoefficientCanonicalModule k ι j n V) 1
          (a.comp β hir)) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j)
    (cmCurveCoefficientCanonicalModule k ι j n V) 1
  dsimp only
  let O : C.Modules := cmCurveSerreUnit C
  let G := moduleGlobalSectionsFunctorOfHom C (cmCurveSerreScalar k ι j)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0
  let E₀ := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).app
    (ModuleCat.of k k)
  let E₁ := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).app V
  let u := DerivedCategory.Plus.ι.map (moduleDerivedStructureUnit C (cmCurveSerreScalar k ι j))
  let ψ := cmCurveCoefficientSerreModuleHom k ι j V F ((r : ℤ) - 1)
    (cmCurveCoefficientSerreDerivedLinearMap k ι j n e V hV hCM F r hn β)
  let ζ := a.comp β hir
  let χ := cmCurveCoefficientSerreModuleHom k ι j V O 0
    (cmCurveCoefficientSerreDerivedLinearMap k ι j n e V hV hCM O 1 hn ζ)
  have hχ : χ = (a.homPlus.map (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)).comp ψ
      (show ((r : ℤ) - 1) + (i : ℤ) = 0 by omega) := by
    have h := congrArg (cmCurveCoefficientSerreModuleHom k ι j V O 0)
      (cmCurveCoefficientSerreDerivedLinearMap_comp k ι j n e V hV hCM hn a β hir)
    exact h.trans (cmCurveCoefficientSerreModuleHom_comp k ι j V a
      (cmCurveCoefficientSerreDerivedLinearMap k ι j n e V hV hCM F r hn β) (by omega))
  have hH : H.shiftMap χ 0 0 (by omega) =
      H.shiftMap (a.homPlus.map (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι))
        0 (i : ℤ) (by omega) ≫ H.shiftMap ψ (i : ℤ) 0 (by omega) :=
    (congrArg (fun z => H.shiftMap z 0 0 (by omega)) hχ).trans
      (H.shiftMap_shiftedComp _ _ (by omega) (by omega) (by omega))
  have hpoint : (H.shiftMap ψ (i : ℤ) 0 (by omega) ≫ E₁.hom)
      (H.shiftMap (a.homPlus.map (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι))
        0 (i : ℤ) (by omega) (H.map u (E₀.inv (1 : k)))) =
      (H.shiftMap χ 0 0 (by omega) ≫ E₁.hom) (H.map u (E₀.inv (1 : k))) := by
    rw [hH]
    rfl
  exact hpoint.trans ((cmCurveCoefficientSerreModuleHom_unit k ι j V
    (cmCurveCoefficientSerreDerivedLinearMap k ι j n e V hV hCM O 1 hn ζ)).trans
      (cmCurveCoefficientSerreTrace_apply_ext k ι j n e V hV hCM hn ζ).symm)

/-- The original six maps equal the positive Yoneda pairing on every original class. -/
theorem cmCurveCoefficientSerreCohomologyAddEquiv_pairing (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (r : ℕ) (hr : r ≤ 1) (hn : 1 ≤ n)
    (β : Ext.{u + 1} (C := C.Modules) F (cmCurveCoefficientCanonicalModule k ι j n V) r)
    (a : Ext.{u + 1} (C := C.Modules) (cmCurveSerreUnit C) F (1 - r)) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F (1 - r)
    let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j)
      (cmCurveCoefficientCanonicalModule k ι j n V) 1
    cmCurveCoefficientSerreCohomologyAddEquiv k ι j n e V hV hCM F hF r hr hn β
      (moduleExtCohomologyMap C F (1 - r) a) =
      cmCurveCoefficientSerreTrace k ι j n e V hV hCM hn
        (moduleExtCohomologyMap C (cmCurveCoefficientCanonicalModule k ι j n V) 1
          (a.comp β (by omega))) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F (1 - r)
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j)
    (cmCurveCoefficientCanonicalModule k ι j n V) 1
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0
  let E₁ := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).hom.app V
  let χ := cmCurveCoefficientSerreModuleHom k ι j V F ((r : ℤ) - 1)
    (cmCurveCoefficientSerreDerivedLinearMap k ι j n e V hV hCM F r hn β)
  have hraw := cmCurveCoefficientSerreCohomologyAddEquiv_moduleHom k ι j n e V hV hCM
    F hF r hr hn β (moduleExtCohomologyMap C F (1 - r) a)
  have hclass := cmCurveSerreDerivedClass_full k ι j F (1 - r) (by omega) a
  have hpoint := congrArg
    (fun z => (H.shiftMap χ ((1 - r : ℕ) : ℤ) 0 (by omega) ≫ E₁) z) hclass
  exact hraw.trans (hpoint.trans
    (cmCurveCoefficientSerreModuleHom_pairing k ι j n e V hV hCM F hn (by omega) a β))

/-- The native positive Ext pairing is linear with any specified module codomain. -/
def cmCurveCoefficientYonedaPairingOfEquiv
    {A : Type*} [Category* A] [Abelian A] [HasExt.{w} A]
    {R : Type*} [CommRing R] [Linear R A] {O F W : A} {i r m : ℕ}
    {H M : Type*} [AddCommGroup H] [Module R H] [AddCommGroup M] [Module R M]
    (E : Ext.{w} O F i ≃ₗ[R] H) (t : Ext.{w} O W m →ₗ[R] M)
    (h : i + r = m) : Ext.{w} F W r →ₗ[R] (H →ₗ[R] M) where
  toFun β := t.comp ((β.postcompOfLinear R O h).comp E.symm.toLinearMap)
  map_add' β γ := by
    ext x
    exact (congrArg t (Ext.comp_add (E.symm x) β γ h)).trans (t.map_add _ _)
  map_smul' a β := by
    ext x
    exact (congrArg t (Ext.comp_smul (E.symm x) β h a)).trans (t.map_smul a _)

/-- The same generic positive pairing retains full unsigned Ext composition. -/
theorem cmCurveCoefficientYonedaPairingOfEquiv_comp
    {A : Type*} [Category* A] [Abelian A] [HasExt.{w} A]
    {R : Type*} [CommRing R] [Linear R A] {O F G W : A}
    {i a b l r m : ℕ} {HF HG M : Type*}
    [AddCommGroup HF] [AddCommGroup HG] [Module R HF] [Module R HG]
    [AddCommGroup M] [Module R M]
    (EF : Ext.{w} O F i ≃ₗ[R] HF) (EG : Ext.{w} O G l ≃ₗ[R] HG)
    (t : Ext.{w} O W m →ₗ[R] M) (η : Ext.{w} F G a) (β : Ext.{w} G W b)
    (hab : a + b = r) (hil : i + a = l) (hir : i + r = m) (hlb : l + b = m)
    (x : HF) :
    cmCurveCoefficientYonedaPairingOfEquiv EF t hir (η.comp β hab) x =
      cmCurveCoefficientYonedaPairingOfEquiv EG t hlb β
        (cmCurveYonedaActionOfEquivs EF EG η hil x) := by
  change t ((EF.symm x).comp (η.comp β hab) hir) =
    t ((EG.symm (EG ((EF.symm x).comp η hil))).comp β hlb)
  rw [EG.symm_apply_apply]
  exact congrArg t (Ext.comp_assoc (EF.symm x) η β hil hab (by omega)).symm

/-- The actual positive coefficient pairing uses the same installed trace. -/
def cmCurveCoefficientSerreYonedaPairing (F : C.Modules)
    (r : ℕ) (hr : r ≤ 1) (hn : 1 ≤ n) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    Ext.{u + 1} (C := C.Modules) F (cmCurveCoefficientCanonicalModule k ι j n V) r →ₗ[k]
      (cmCurveSerreCohomology k ι j F (1 - r) →ₗ[k] V) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let W : C.Modules := cmCurveCoefficientCanonicalModule k ι j n V
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F (1 - r)
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) W 1
  let E : Ext.{u + 1} (C := C.Modules) (cmCurveSerreUnit C) F (1 - r) ≃ₗ[k]
      cmCurveSerreCohomology k ι j F (1 - r) :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) F (1 - r)
  let EW : Ext.{u + 1} (C := C.Modules) (cmCurveSerreUnit C) W 1 ≃ₗ[k]
      cmCurveSerreCohomology k ι j W 1 :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) W 1
  exact cmCurveCoefficientYonedaPairingOfEquiv E
    ((cmCurveCoefficientSerreTrace k ι j n e V hV hCM hn).comp EW.toLinearMap) (by omega)

/-- The actual positive pairing keeps the original Ext/cohomology values. -/
theorem cmCurveCoefficientSerreYonedaPairing_apply (F : C.Modules)
    (r : ℕ) (hr : r ≤ 1) (hn : 1 ≤ n)
    (β : Ext.{u + 1} (C := C.Modules) F (cmCurveCoefficientCanonicalModule k ι j n V) r)
    (x : cmCurveSerreCohomology k ι j F (1 - r)) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    let E : Ext.{u + 1} (C := C.Modules) (cmCurveSerreUnit C) F (1 - r) ≃ₗ[k]
        cmCurveSerreCohomology k ι j F (1 - r) :=
      moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) F (1 - r)
    cmCurveCoefficientSerreYonedaPairing k ι j n e V hV hCM F r hr hn β x =
      cmCurveCoefficientSerreTrace k ι j n e V hV hCM hn
        (moduleExtCohomologyMap C (cmCurveCoefficientCanonicalModule k ι j n V) 1
          ((E.symm x).comp β (by omega))) := rfl

private theorem cmCurveCoefficientFunctionalsEq
    {R : Type*} [CommRing R] {A H M : Type*}
    [AddCommGroup H] [Module R H] [AddCommGroup M] [Module R M]
    (L P : H →ₗ[R] M) (E : A ≃ H)
    (h : ∀ a, L (E a) = P (E a)) : L = P := by
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := E.surjective x
  exact h a

/-- The original six-map forward comparison is the same positive V-valued pairing. -/
theorem cmCurveCoefficientSerreCohomologyAddEquiv_eq_pairing (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (r : ℕ) (hr : r ≤ 1) (hn : 1 ≤ n)
    (β : Ext.{u + 1} (C := C.Modules) F (cmCurveCoefficientCanonicalModule k ι j n V) r) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    cmCurveCoefficientSerreCohomologyAddEquiv k ι j n e V hV hCM F hF r hr hn β =
      cmCurveCoefficientSerreYonedaPairing k ι j n e V hV hCM F r hr hn β := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F (1 - r)
  let W : C.Modules := cmCurveCoefficientCanonicalModule k ι j n V
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) W 1
  let E : Ext.{u + 1} (C := C.Modules) (cmCurveSerreUnit C) F (1 - r) ≃ₗ[k]
      cmCurveSerreCohomology k ι j F (1 - r) :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) F (1 - r)
  let L : cmCurveSerreCohomology k ι j F (1 - r) →ₗ[k] V :=
    cmCurveCoefficientSerreCohomologyAddEquiv k ι j n e V hV hCM F hF r hr hn β
  let P : cmCurveSerreCohomology k ι j F (1 - r) →ₗ[k] V :=
    cmCurveCoefficientSerreYonedaPairing k ι j n e V hV hCM F r hr hn β
  refine cmCurveCoefficientFunctionalsEq L P E.toEquiv ?_
  intro a
  have hE := moduleExtCohomologyLinearEquivOfCategory_apply C
    (cmCurveSerreScalar k ι j) F (1 - r) a
  have hp := cmCurveCoefficientSerreYonedaPairing_apply k ι j n e V hV hCM F r hr hn β (E a)
  have hp' : cmCurveCoefficientSerreYonedaPairing k ι j n e V hV hCM F r hr hn β (E a) =
      cmCurveCoefficientSerreTrace k ι j n e V hV hCM hn
        (moduleExtCohomologyMap C W 1 (a.comp β (by omega))) :=
    hp.trans (congrArg
      (fun z : Ext.{u + 1} (C := C.Modules) (cmCurveSerreUnit C) F (1 - r) =>
        cmCurveCoefficientSerreTrace k ι j n e V hV hCM hn
          (moduleExtCohomologyMap C W 1 (z.comp β (by omega))))
      (E.symm_apply_apply a))
  exact (congrArg (cmCurveCoefficientSerreCohomologyAddEquiv k ι j n e V hV hCM
    F hF r hr hn β) hE).trans
      ((cmCurveCoefficientSerreCohomologyAddEquiv_pairing k ι j n e V hV hCM
        F hF r hr hn β a).trans hp'.symm)


/-- Original coefficient-valued Serre duality, with the six original maps as forward map. -/
def cmCurveCoefficientSerreDuality (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (r : ℕ) (hr : r ≤ 1) (hn : 1 ≤ n) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    Ext.{u + 1} (C := C.Modules) F (cmCurveCoefficientCanonicalModule k ι j n V) r ≃ₗ[k]
      (cmCurveSerreCohomology k ι j F (1 - r) →ₗ[k] V) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let E := cmCurveCoefficientSerreCohomologyAddEquiv k ι j n e V hV hCM F hF r hr hn
  let P := cmCurveCoefficientSerreYonedaPairing k ι j n e V hV hCM F r hr hn
  have h (x) : E x = P x :=
    cmCurveCoefficientSerreCohomologyAddEquiv_eq_pairing k ι j n e V hV hCM F hF r hr hn x
  exact { toAddEquiv := E
          map_smul' := fun a x => (h (a • x)).trans
            ((P.map_smul a x).trans (congrArg (fun y => a • y) (h x).symm)) }

/-- Linear packaging retains the literal original comparison. -/
theorem cmCurveCoefficientSerreDuality_apply (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (r : ℕ) (hr : r ≤ 1) (hn : 1 ≤ n)
    (β : Ext.{u + 1} (C := C.Modules) F (cmCurveCoefficientCanonicalModule k ι j n V) r) :
    cmCurveCoefficientSerreDuality k ι j n e V hV hCM F hF r hr hn β =
      cmCurveCoefficientSerreCohomologyAddEquiv k ι j n e V hV hCM F hF r hr hn β := rfl

/-- The original coefficient comparison preserves full positive source/Yoneda action. -/
theorem cmCurveCoefficientSerreDuality_comp {F G : C.Modules}
    (hF : affineLocallyFiniteType C F) (hG : affineLocallyFiniteType C G)
    {a b r : ℕ} (η : Ext.{u + 1} (C := C.Modules) F G a)
    (β : Ext.{u + 1} (C := C.Modules) G (cmCurveCoefficientCanonicalModule k ι j n V) b)
    (hab : a + b = r) (hr : r ≤ 1) (hn : 1 ≤ n)
    (x : cmCurveSerreCohomology k ι j F (1 - r)) :
    cmCurveCoefficientSerreDuality k ι j n e V hV hCM F hF r hr hn (η.comp β hab) x =
      cmCurveCoefficientSerreDuality k ι j n e V hV hCM G hG b (by omega) hn β
        (cmCurveSerreYonedaAction k ι j η (1 - r) (1 - b) (by omega) x) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let O : C.Modules := cmCurveSerreUnit C
  let W : C.Modules := cmCurveCoefficientCanonicalModule k ι j n V
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F (1 - r)
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) G (1 - b)
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) W 1
  let EF : Ext.{u + 1} (C := C.Modules) (cmCurveSerreUnit C) F (1 - r) ≃ₗ[k]
      cmCurveSerreCohomology k ι j F (1 - r) :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) F (1 - r)
  let EG : Ext.{u + 1} (C := C.Modules) (cmCurveSerreUnit C) G (1 - b) ≃ₗ[k]
      cmCurveSerreCohomology k ι j G (1 - b) :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) G (1 - b)
  let EW : Ext.{u + 1} (C := C.Modules) (cmCurveSerreUnit C) W 1 ≃ₗ[k]
      cmCurveSerreCohomology k ι j W 1 :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) W 1
  let t := (cmCurveCoefficientSerreTrace k ι j n e V hV hCM hn).comp EW.toLinearMap
  rw [cmCurveCoefficientSerreDuality_apply, cmCurveCoefficientSerreDuality_apply,
    cmCurveCoefficientSerreCohomologyAddEquiv_eq_pairing,
    cmCurveCoefficientSerreCohomologyAddEquiv_eq_pairing]
  exact cmCurveCoefficientYonedaPairingOfEquiv_comp EF EG t η β hab
    (by omega) (by omega) (by omega) x

/-- Ordinary source naturality uses the original sheaf-cohomology morphism. -/
theorem cmCurveCoefficientSerreDuality_precomp {F G : C.Modules}
    (hF : affineLocallyFiniteType C F) (hG : affineLocallyFiniteType C G)
    (f : F ⟶ G) (r : ℕ) (hr : r ≤ 1) (hn : 1 ≤ n)
    (β : Ext.{u + 1} (C := C.Modules) G (cmCurveCoefficientCanonicalModule k ι j n V) r)
    (x : cmCurveSerreCohomology k ι j F (1 - r)) :
    cmCurveCoefficientSerreDuality k ι j n e V hV hCM F hF r hr hn
      ((Ext.mk₀ f).comp β (Nat.zero_add r)) x =
      cmCurveCoefficientSerreDuality k ι j n e V hV hCM G hG r hr hn β
        ((moduleCohomologyFunctorOfHom C (cmCurveSerreScalar k ι j) (1 - r)).map f x) :=
  (cmCurveCoefficientSerreDuality_comp k ι j n e V hV hCM hF hG
    (Ext.mk₀ f) β (Nat.zero_add r) hr hn x).trans
      (congrArg (cmCurveCoefficientSerreDuality k ι j n e V hV hCM G hG r hr hn β)
        (cmCurveSerreYonedaAction_mk₀ k ι j f (1 - r) x))

/-- Evaluation of the same degree-one comparison on structural one is the same trace. -/
theorem cmCurveCoefficientSerreDuality_one (hn : 1 ≤ n)
    (x : cmCurveSerreCohomology k ι j (cmCurveCoefficientCanonicalModule k ι j n V) 1) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    let W : C.Modules := cmCurveCoefficientCanonicalModule k ι j n V
    let E : Ext.{u + 1} (C := C.Modules) (cmCurveSerreUnit C) W 1 ≃ₗ[k]
        cmCurveSerreCohomology k ι j W 1 :=
      moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) W 1
    cmCurveCoefficientSerreDuality k ι j n e V hV hCM (cmCurveSerreUnit C)
      (AlgebraicGeometry.Scheme.Modules.affineLocallyFiniteType_unit C) 1 (by omega) hn
        (E.symm x) (cmCurveSerreStructuralOne k ι j) =
      cmCurveCoefficientSerreTrace k ι j n e V hV hCM hn x := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let O : C.Modules := cmCurveSerreUnit C
  let W : C.Modules := cmCurveCoefficientCanonicalModule k ι j n V
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) W 1
  let E : Ext.{u + 1} (C := C.Modules) (cmCurveSerreUnit C) W 1 ≃ₗ[k]
      cmCurveSerreCohomology k ι j W 1 :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) W 1
  have h := cmCurveCoefficientSerreCohomologyAddEquiv_pairing k ι j n e V hV hCM O
    (AlgebraicGeometry.Scheme.Modules.affineLocallyFiniteType_unit C) 1 (by omega) hn
      (E.symm x) (Ext.mk₀ (𝟙 O))
  have hc := Ext.mk₀_id_comp (E.symm x)
  have he : moduleExtCohomologyMap C W 1 (E.symm x) = x :=
    (moduleExtCohomologyLinearEquivOfCategory_apply C (cmCurveSerreScalar k ι j)
      W 1 (E.symm x)).symm.trans (E.apply_symm_apply x)
  have hD := congrArg (fun f => f (cmCurveSerreStructuralOne k ι j))
    (cmCurveCoefficientSerreDuality_apply k ι j n e V hV hCM O
      (AlgebraicGeometry.Scheme.Modules.affineLocallyFiniteType_unit C) 1 (by omega) hn (E.symm x))
  exact hD.trans (h.trans (congrArg (cmCurveCoefficientSerreTrace k ι j n e V hV hCM hn)
    ((congrArg (moduleExtCohomologyMap C W 1) hc).trans he)))

/-- Degree-zero duality is the same trace after the original H1 map. -/
theorem cmCurveCoefficientSerreDuality_zero (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (hn : 1 ≤ n)
    (f : F ⟶ cmCurveCoefficientCanonicalModule k ι j n V)
    (x : cmCurveSerreCohomology k ι j F 1) :
    cmCurveCoefficientSerreDuality k ι j n e V hV hCM F hF 0 (by omega) hn
        (Ext.mk₀ f) x =
      cmCurveCoefficientSerreTrace k ι j n e V hV hCM hn
        ((moduleCohomologyFunctorOfHom C (cmCurveSerreScalar k ι j) 1).map f x) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F 1
  let W : C.Modules := cmCurveCoefficientCanonicalModule k ι j n V
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) W 1
  let E : Ext.{u + 1} (C := C.Modules) (cmCurveSerreUnit C) F 1 ≃ₗ[k]
      cmCurveSerreCohomology k ι j F 1 :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) F 1
  let a := E.symm x
  let P := cmCurveCoefficientSerreCohomologyAddEquiv k ι j n e V hV hCM F hF 0 (by omega) hn
    (Ext.mk₀ f)
  have he : moduleExtCohomologyMap C F 1 a = x :=
    (moduleExtCohomologyLinearEquivOfCategory_apply C (cmCurveSerreScalar k ι j)
      F 1 a).symm.trans (E.apply_symm_apply x)
  have h := cmCurveCoefficientSerreCohomologyAddEquiv_pairing k ι j n e V hV hCM
    F hF 0 (by omega) hn (Ext.mk₀ f) a
  have hnatu := moduleExtCohomologyMap_naturality C f 1 a
  have hD := congrArg (fun q => q x)
    (cmCurveCoefficientSerreDuality_apply k ι j n e V hV hCM F hF 0 (by omega) hn (Ext.mk₀ f))
  exact hD.trans ((congrArg P he.symm).trans (h.trans
    (congrArg (cmCurveCoefficientSerreTrace k ι j n e V hV hCM hn)
      (hnatu.trans (congrArg ((moduleCohomologyFunctorOfHom C
        (cmCurveSerreScalar k ι j) 1).map f) he)))))

omit [Module.Finite k V] in
/-- Evaluation at one identifies linear maps out of the original scalar field with any module. -/
def cmCurveCoefficientEvalOneEquiv {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M] : (R →ₗ[R] M) ≃ₗ[R] M where
  toFun f := f 1
  invFun m :=
    { toFun a := a • m
      map_add' a b := add_smul a b m
      map_smul' a b := mul_smul a b m }
  left_inv f := by
    apply LinearMap.ext
    intro a
    change a • f 1 = f a
    simpa only [smul_eq_mul, mul_one] using (f.map_smul a (1 : R)).symm
  right_inv m := one_smul R m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Module.Finite k V] in
/-- The honest structural H0 isomorphism makes evaluation at original one an equivalence. -/
def cmCurveCoefficientSerreStructuralEvaluationEquiv
    (hc : Function.Bijective (cmCurveSerreStructuralH0Map k ι j)) :
    (cmCurveSerreCohomology k ι j (cmCurveSerreUnit C) 0 →ₗ[k] V) ≃ₗ[k] V := by
  let E := LinearEquiv.ofBijective (cmCurveSerreStructuralH0Map k ι j) hc
  exact (LinearEquiv.arrowCongr E.symm (LinearEquiv.refl k V)).trans
    cmCurveCoefficientEvalOneEquiv

omit [Module.Finite k V] [IsClosedImmersion j] in
/-- This equivalence evaluates the original functional on the original structural section. -/
theorem cmCurveCoefficientSerreStructuralEvaluationEquiv_apply
    (hc : Function.Bijective (cmCurveSerreStructuralH0Map k ι j))
    (f : cmCurveSerreCohomology k ι j (cmCurveSerreUnit C) 0 →ₗ[k] V) :
    cmCurveCoefficientSerreStructuralEvaluationEquiv k ι j V hc f =
      f (cmCurveSerreStructuralOne k ι j) := by
  change f (cmCurveSerreStructuralH0Map k ι j (1 : k)) = _
  exact congrArg f (one_smul k (cmCurveSerreStructuralOne k ι j))

/-- Bijectivity of the same trace follows from the original duality and honest structural H0. -/
theorem cmCurveCoefficientSerreTrace_bijective (hn : 1 ≤ n)
    (hc : Function.Bijective (cmCurveSerreStructuralH0Map k ι j)) :
    Function.Bijective (cmCurveCoefficientSerreTrace k ι j n e V hV hCM hn) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let O : C.Modules := cmCurveSerreUnit C
  let W : C.Modules := cmCurveCoefficientCanonicalModule k ι j n V
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) W 1
  let E : Ext.{u + 1} (C := C.Modules) (cmCurveSerreUnit C) W 1 ≃ₗ[k]
      cmCurveSerreCohomology k ι j W 1 :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) W 1
  let P := cmCurveCoefficientSerreDuality k ι j n e V hV hCM O
    (AlgebraicGeometry.Scheme.Modules.affineLocallyFiniteType_unit C) 1 (by omega) hn
  let T := E.symm.trans (P.trans (cmCurveCoefficientSerreStructuralEvaluationEquiv k ι j V hc))
  have hT : (T : cmCurveSerreCohomology k ι j W 1 → V) =
      cmCurveCoefficientSerreTrace k ι j n e V hV hCM hn := by
    funext x
    change cmCurveCoefficientSerreStructuralEvaluationEquiv k ι j V hc (P (E.symm x)) = _
    exact (cmCurveCoefficientSerreStructuralEvaluationEquiv_apply k ι j V hc _).trans
      (cmCurveCoefficientSerreDuality_one k ι j n e V hV hCM hn x)
  rw [← hT]
  exact T.bijective

/-- The actual coefficient-valued trace as an equivalence, with its forward map unchanged. -/
def cmCurveCoefficientSerreTraceEquiv (hn : 1 ≤ n)
    (hc : Function.Bijective (cmCurveSerreStructuralH0Map k ι j)) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j)
      (cmCurveCoefficientCanonicalModule k ι j n V) 1
    cmCurveSerreCohomology k ι j (cmCurveCoefficientCanonicalModule k ι j n V) 1 ≃ₗ[k] V := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j)
    (cmCurveCoefficientCanonicalModule k ι j n V) 1
  exact LinearEquiv.ofBijective (cmCurveCoefficientSerreTrace k ι j n e V hV hCM hn)
    (cmCurveCoefficientSerreTrace_bijective k ι j n e V hV hCM hn hc)

/-- Trace-equivalence packaging preserves the original coefficient trace. -/
theorem cmCurveCoefficientSerreTraceEquiv_apply (hn : 1 ≤ n)
    (hc : Function.Bijective (cmCurveSerreStructuralH0Map k ι j))
    (x : cmCurveSerreCohomology k ι j (cmCurveCoefficientCanonicalModule k ι j n V) 1) :
    cmCurveCoefficientSerreTraceEquiv k ι j n e V hV hCM hn hc x =
      cmCurveCoefficientSerreTrace k ι j n e V hV hCM hn x := rfl

end AlgebraicGeometry.Scheme.Cohomology
