/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve.Serre.Trace
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve.Serre.Pairing

/-!
# Original additive comparison and positive curve pairing
-/

@[expose] public noncomputable section

universe u v w u' v' w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent RelativeCanonicalReindex

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.isQuasicoherent_unit

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.isQuasicoherent_unit

/-- The standard derived-category model for modules over the coefficient ring. -/
local instance cmCurveRawExtractionDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

variable (k : Type u) [Field k] (ι : Type u)
    {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (n : ℕ) (e : ι ≃ Fin (n + 1))

/-- The natural-degree specialization of the original affine homology
comparison uses the negative of the cohomology degree, with no integer
truncation. -/
theorem cmCurveSerreAffineHom_homology_reindex (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (q i : ℕ) (hi : q + i = n)
    (a : cmCurveSerreDirectImage k ι j F ⟶
      ((DerivedCategory.singleFunctor (Spec (.of k)).Modules (n : ℤ)).obj
        (cmCurveSerreUnit (Spec (.of k))))⟦(q : ℤ)⟧)
    (x : cmCurveSerreCohomology k ι j F i) :
    let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F i
    let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
    let O : (Spec (.of k)).Modules := cmCurveSerreUnit (Spec (.of k))
    let N := (moduleSpecΓFunctor (R := .of k)).obj O
    let B := moduleSpecDerivedPushforwardHomAddEquiv (j ≫ toSpec k ι) F O n q a
    let T := ((DerivedCategory.singleFunctors (ModuleCat.{u} k)).shiftIso
      (q : ℤ) (i : ℤ) (n : ℤ) (by exact_mod_cast hi)).app N
    let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv C
      (cmCurveSerreScalar k ι j) (injectiveResolution F) i
    cmCurveSerreHomologyDualAddEquiv k ι j F i N
        (cmCurveSerreSpecUnitSectionsIso k)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) (i : ℤ)).map (B ≫ T.hom) ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k)
            (i : ℤ)).hom.app N) x =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).shiftMap
        (cmCurveSerreModuleHom k ι j F (-(i : ℤ))
          (a ≫ (singleReindexIso O (n : ℤ) (q : ℤ) (-(i : ℤ))
            (by omega)).inv))
        (i : ℤ) 0 (by omega) ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).hom.app
            (ModuleCat.of k k)) (E.symm x) := by
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F i
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
  exact cmCurveSerreAffineHom_homology_of_reindex k ι j n e F hF q i (-(i : ℤ))
    (by omega) (by omega) a x

variable (hCM : ∀ x : C, IsClosed ({x} : Set C) →
    ∃ b ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk x),
      IsSMulRegular (C.presheaf.stalk x) b ∧
        (Ideal.span {b}).radical = IsLocalRing.maximalIdeal (C.presheaf.stalk x))

/-- The original additive forward comparison extracts the original
native shifted homology arrow in every complementary curve degree. -/
theorem cmCurveSerreCohomologyAddEquiv_moduleHom (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (r : ℕ) (hr : r ≤ 1) (hn : 1 ≤ n)
    (β : Ext.{u + 1} (C := C.Modules) F (cmCurveCanonicalModule k ι j n) r)
    (x : cmCurveSerreCohomology k ι j F (1 - r)) :
    let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F (1 - r)
    let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv C
      (cmCurveSerreScalar k ι j) (injectiveResolution F) (1 - r)
    cmCurveSerreCohomologyAddEquiv k ι j n e hCM F hF r hr hn β x =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).shiftMap
        (cmCurveSerreModuleHom k ι j F ((r : ℤ) - 1)
          (cmCurveSerreDerivedLinearMap k ι j n e hCM F r hn β))
        ((1 - r : ℕ) : ℤ) 0 (by omega) ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).hom.app
            (ModuleCat.of k k)) (E.symm x) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCategoryLinearOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F (1 - r)
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
  let O : (Spec (.of k)).Modules := cmCurveSerreUnit (Spec (.of k))
  let N := (moduleSpecΓFunctor (R := .of k)).obj O
  let q := r + (n - 1)
  let i := 1 - r
  let E₀ := purityInputLinearEquiv (S := k) F (cmCurveCanonicalModule k ι j n)
    (DerivedCategory.Plus.ι.obj (cmCurveDualizingObject k ι j n)) ((n : ℤ) - 1)
    (cmCurveSerreCanonicalIso k ι j n e hCM) q r (by dsimp [q]; omega)
  let Φ := relativeClosedEmbeddingSerreDuality j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
    (IsPullback.id_horiz (toSpec k ι)) (Scheme.ΓSpecIso (.of k)).inv.hom n e O F hF q
  let A := moduleSpecDerivedPushforwardHomAddEquiv (j ≫ toSpec k ι) F O n q
  let T := ((DerivedCategory.singleFunctors (ModuleCat.{u} k)).shiftIso
    (q : ℤ) (i : ℤ) (n : ℤ) (by dsimp [q, i]; omega)).app N
  let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv C
    (cmCurveSerreScalar k ι j) (injectiveResolution F) i
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0
  let e₀ := (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (ModuleCat.{u} k) 0).hom.app (ModuleCat.of k k)
  let a := Φ (E₀ β)
  have hraw := congrArg (fun l => l x)
    (cmCurveSerreCohomologyAddEquiv_apply k ι j n e hCM F hF r hr hn β)
  have hhom := congrArg
    (fun f => cmCurveSerreHomologyDualAddEquiv k ι j F i N
      (cmCurveSerreSpecUnitSectionsIso k) f x)
    (DerivedCategory.cmCurve_homToSingleAddHom_apply
      (cmCurveSerreDerivedSections k ι j F) (i : ℤ) N (A a ≫ T.hom))
  have hfun := cmCurveSerreAffineHom_homology_of_reindex k ι j n e F hF q i
    ((r : ℤ) - 1) (by dsimp [q]; omega) (by dsimp [i]; omega) a x
  have hmap := congrArg (cmCurveSerreModuleHom k ι j F ((r : ℤ) - 1))
    (cmCurveSerreDerivedLinearMap_input_apply k ι j n e hCM F hF r hn β).symm
  have hpoint := congrArg
    (fun f => (H.shiftMap f (i : ℤ) 0 (by dsimp [i]; omega) ≫ e₀) (E.symm x)) hmap
  exact hraw.trans (hhom.trans (hfun.trans hpoint))

/-- In degree zero, the unchanged additive Serre equivalence evaluates
its original module-valued arrow by the original shifted homology map. -/
theorem cmCurveSerreCohomologyAddEquiv_zero_moduleHom (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (hn : 1 ≤ n)
    (β : Ext.{u + 1} (C := C.Modules) F (cmCurveCanonicalModule k ι j n) 0)
    (x : cmCurveSerreCohomology k ι j F 1) :
    let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F 1
    let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv C
      (cmCurveSerreScalar k ι j) (injectiveResolution F) 1
    cmCurveSerreCohomologyAddEquiv k ι j n e hCM F hF 0 (by omega) hn β x =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).shiftMap
        (cmCurveSerreModuleHom k ι j F (-1)
          (cmCurveSerreDerivedLinearMap k ι j n e hCM F 0 hn β))
        1 0 (by omega) ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).hom.app
            (ModuleCat.of k k)) (E.symm x) := by
  exact cmCurveSerreCohomologyAddEquiv_moduleHom k ι j n e hCM F hF 0
    (by omega) hn β x

/-- In degree one, the unchanged additive Serre equivalence is the same
original module-valued arrow on native degree-zero homology. -/
theorem cmCurveSerreCohomologyAddEquiv_one_moduleHom (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (hn : 1 ≤ n)
    (β : Ext.{u + 1} (C := C.Modules) F (cmCurveCanonicalModule k ι j n) 1)
    (x : cmCurveSerreCohomology k ι j F 0) :
    let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F 0
    let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv C
      (cmCurveSerreScalar k ι j) (injectiveResolution F) 0
    cmCurveSerreCohomologyAddEquiv k ι j n e hCM F hF 1 (by omega) hn β x =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).shiftMap
        (cmCurveSerreModuleHom k ι j F 0
          (cmCurveSerreDerivedLinearMap k ι j n e hCM F 1 hn β))
        0 0 (by omega) ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).hom.app
            (ModuleCat.of k k)) (E.symm x) := by
  exact cmCurveSerreCohomologyAddEquiv_moduleHom k ι j n e hCM F hF 1
    (by omega) hn β x

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.isQuasicoherent_unit

/-- The standard derived-category model for modules over the coefficient ring. -/
local instance cmCurvePairingAnchorDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

variable (k : Type u) [Field k] (ι : Type u)
    {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]

variable (n : ℕ) (e : ι ≃ Fin (n + 1))
    (hCM : ∀ x : C, IsClosed ({x} : Set C) →
      ∃ b ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk x),
        IsSMulRegular (C.presheaf.stalk x) b ∧
          (Ideal.span {b}).radical = IsLocalRing.maximalIdeal (C.presheaf.stalk x))

/-- The original module-valued Serre arrow evaluates an original Ext
class by the same positive Yoneda product and the already installed
trace. This includes the native shifted composition signs. -/
theorem cmCurveSerreModuleHom_pairing (F : C.Modules) (hn : 1 ≤ n)
    {i r : ℕ} (hir : i + r = 1)
    (a : Ext.{u + 1} (C := C.Modules) (cmCurveSerreUnit C : C.Modules) F i)
    (β : Ext.{u + 1} (C := C.Modules) F (cmCurveCanonicalModule k ι j n) r) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j)
      (cmCurveCanonicalModule k ι j n) 1
    let G := moduleGlobalSectionsFunctorOfHom C (cmCurveSerreScalar k ι j)
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0
    let E := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).app
      (ModuleCat.of k k)
    let u := DerivedCategory.Plus.ι.map (moduleDerivedStructureUnit C (cmCurveSerreScalar k ι j))
    (H.shiftMap (cmCurveSerreModuleHom k ι j F ((r : ℤ) - 1)
        (cmCurveSerreDerivedLinearMap k ι j n e hCM F r hn β)) (i : ℤ) 0 (by omega) ≫ E.hom)
      (H.shiftMap (a.homPlus.map (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι))
        0 (i : ℤ) (by omega) (H.map u (E.inv (1 : k)))) =
      cmCurveSerreTrace k ι j n e hCM hn
        (moduleExtCohomologyMap C (cmCurveCanonicalModule k ι j n) 1 (a.comp β hir)) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j)
    (cmCurveCanonicalModule k ι j n) 1
  dsimp only
  let O : C.Modules := cmCurveSerreUnit C
  let G := moduleGlobalSectionsFunctorOfHom C (cmCurveSerreScalar k ι j)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0
  let E := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).app
    (ModuleCat.of k k)
  let u := DerivedCategory.Plus.ι.map (moduleDerivedStructureUnit C (cmCurveSerreScalar k ι j))
  let ψ := cmCurveSerreModuleHom k ι j F ((r : ℤ) - 1)
    (cmCurveSerreDerivedLinearMap k ι j n e hCM F r hn β)
  let ζ := a.comp β hir
  let χ := cmCurveSerreModuleHom k ι j O 0
    (cmCurveSerreDerivedLinearMap k ι j n e hCM O 1 hn ζ)
  have hχ : χ = (a.homPlus.map (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)).comp ψ
      (show ((r : ℤ) - 1) + (i : ℤ) = 0 by omega) := by
    have h := congrArg (cmCurveSerreModuleHom k ι j O 0)
      (cmCurveSerreDerivedLinearMap_comp k ι j n e hCM hn a β hir)
    exact h.trans (cmCurveSerreModuleHom_comp k ι j a
      (cmCurveSerreDerivedLinearMap k ι j n e hCM F r hn β) (by omega))
  have hH : H.shiftMap χ 0 0 (by omega) =
      H.shiftMap (a.homPlus.map (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι))
          0 (i : ℤ) (by omega) ≫ H.shiftMap ψ (i : ℤ) 0 (by omega) := by
    exact (congrArg (fun z => H.shiftMap z 0 0 (by omega)) hχ).trans
      (H.shiftMap_shiftedComp _ _ (by omega) (by omega) (by omega))
  calc
    _ = (H.shiftMap χ 0 0 (by omega) ≫ E.hom) (H.map u (E.inv (1 : k))) := by
      rw [hH]
      rfl
    _ = _ := cmCurveSerreModuleHom_one_trace k ι j n e hCM hn ζ

/-- The original additive comparison is the same positive Yoneda pairing
on every original cohomology class. There is no compatibility or
perfect-pairing assumption. -/
theorem cmCurveSerreCohomologyAddEquiv_pairing (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (r : ℕ) (hr : r ≤ 1) (hn : 1 ≤ n)
    (β : Ext.{u + 1} (C := C.Modules) F (cmCurveCanonicalModule k ι j n) r)
    (a : Ext.{u + 1} (C := C.Modules) (cmCurveSerreUnit C : C.Modules) F (1 - r)) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F (1 - r)
    let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j)
      (cmCurveCanonicalModule k ι j n) 1
    cmCurveSerreCohomologyAddEquiv k ι j n e hCM F hF r hr hn β
        (moduleExtCohomologyMap C F (1 - r) a) =
      cmCurveSerreTrace k ι j n e hCM hn
        (moduleExtCohomologyMap C (cmCurveCanonicalModule k ι j n) 1
          (a.comp β (by omega))) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F (1 - r)
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j)
    (cmCurveCanonicalModule k ι j n) 1
  dsimp only
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0
  let E₀ := (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (ModuleCat.{u} k) 0).hom.app (ModuleCat.of k k)
  let χ := cmCurveSerreModuleHom k ι j F ((r : ℤ) - 1)
    (cmCurveSerreDerivedLinearMap k ι j n e hCM F r hn β)
  have hraw := cmCurveSerreCohomologyAddEquiv_moduleHom k ι j n e hCM F hF r hr hn β
    (moduleExtCohomologyMap C F (1 - r) a)
  have hclass := cmCurveSerreDerivedClass_full k ι j F (1 - r) (by omega) a
  have hpoint := congrArg
    (fun z => (H.shiftMap χ ((1 - r : ℕ) : ℤ) 0 (by omega) ≫ E₀) z) hclass
  exact hraw.trans (hpoint.trans
    (cmCurveSerreModuleHom_pairing k ι j n e hCM F hn (by omega) a β))

/-- Functionals that agree on every class through the same surjective
equivalence agree on the whole original cohomology carrier. -/
theorem cmCurveFunctionalsEqOfOriginalClasses
    {k : Type*} [CommRing k] {X A H : Type*}
    [AddCommGroup X] [AddCommGroup H] [Module k X] [Module k H]
    (L : X → Module.Dual k H) (P : X →ₗ[k] Module.Dual k H) (E : A ≃ H)
    (h : ∀ β a, L β (E a) = P β (E a)) (β : X) : L β = P β := by
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := E.surjective x
  exact h β a

/-- Compare two functionals on an original equivalence class before
specializing its source action or codomain evaluation. -/
theorem cmCurveComparisonOnEquivClass {A H T : Type*}
    (E : A ≃ H) (L P : H → T) (t : A → T) (a : A)
    (hL : L (E a) = t a) (hP : P (E a) = t (E.symm (E a))) :
    L (E a) = P (E a) :=
  hL.trans ((hP.trans (congrArg t (E.symm_apply_apply a))).symm)

/-- The original comparison and original positive pairing have the same
value on each original Ext/cohomology class, before whole-map transport. -/
theorem cmCurveSerreCohomologyAddEquiv_onOriginalClass (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (r : ℕ) (hr : r ≤ 1) (hn : 1 ≤ n)
    (β : Ext.{u + 1} (C := C.Modules) F (cmCurveCanonicalModule k ι j n) r)
    (a : Ext.{u + 1} (C := C.Modules) (cmCurveSerreUnit C) F (1 - r)) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F (1 - r)
    let E : Ext.{u + 1} (C := C.Modules) (cmCurveSerreUnit C) F (1 - r) ≃ₗ[k]
        cmCurveSerreCohomology k ι j F (1 - r) :=
      moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) F (1 - r)
    cmCurveSerreCohomologyAddEquiv k ι j n e hCM F hF r hr hn β (E a) =
      cmCurveSerreYonedaPairing k ι j n e hCM F r hr hn β (E a) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F (1 - r)
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j)
    (cmCurveCanonicalModule k ι j n) 1
  let O : C.Modules := cmCurveSerreUnit C
  let E : Ext.{u + 1} (C := C.Modules) O F (1 - r) ≃ₗ[k]
      cmCurveSerreCohomology k ι j F (1 - r) :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) F (1 - r)
  let L : cmCurveSerreCohomology k ι j F (1 - r) → k :=
    cmCurveSerreCohomologyAddEquiv k ι j n e hCM F hF r hr hn β
  let P : cmCurveSerreCohomology k ι j F (1 - r) → k :=
    cmCurveSerreYonedaPairing k ι j n e hCM F r hr hn β
  let t : Ext.{u + 1} (C := C.Modules) O F (1 - r) → k := fun a' =>
    cmCurveSerreTrace k ι j n e hCM hn
      (moduleExtCohomologyMap C (cmCurveCanonicalModule k ι j n) 1
        (a'.comp β (by omega)))
  have hEa := moduleExtCohomologyLinearEquivOfCategory_apply C (cmCurveSerreScalar k ι j)
    F (1 - r) a
  have hL : L (E a) = t a :=
    (congrArg L hEa).trans
      (cmCurveSerreCohomologyAddEquiv_pairing k ι j n e hCM F hF r hr hn β a)
  have hP : P (E a) = t (E.symm (E a)) :=
    cmCurveSerreYonedaPairing_apply k ι j n e hCM F r hr hn β (E a)
  exact cmCurveComparisonOnEquivClass E.toEquiv L P t a hL hP

/-- The unchanged additive equivalence has precisely the existing
positive, linear Yoneda-pairing forward map. -/
theorem cmCurveSerreCohomologyAddEquiv_eq_yonedaPairing (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (r : ℕ) (hr : r ≤ 1) (hn : 1 ≤ n)
    (β : Ext.{u + 1} (C := C.Modules) F (cmCurveCanonicalModule k ι j n) r) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F (1 - r)
    cmCurveSerreCohomologyAddEquiv k ι j n e hCM F hF r hr hn β =
      cmCurveSerreYonedaPairing k ι j n e hCM F r hr hn β := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F (1 - r)
  let O : C.Modules := cmCurveSerreUnit C
  let E : Ext.{u + 1} (C := C.Modules) O F (1 - r) ≃ₗ[k]
      cmCurveSerreCohomology k ι j F (1 - r) :=
    moduleExtCohomologyLinearEquivOfCategory C (cmCurveSerreScalar k ι j) F (1 - r)
  exact cmCurveFunctionalsEqOfOriginalClasses
    (cmCurveSerreCohomologyAddEquiv k ι j n e hCM F hF r hr hn)
    (cmCurveSerreYonedaPairing k ι j n e hCM F r hr hn) E.toEquiv
    (cmCurveSerreCohomologyAddEquiv_onOriginalClass k ι j n e hCM F hF r hr hn) β

end AlgebraicGeometry.Scheme.Cohomology
