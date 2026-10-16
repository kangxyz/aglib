/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.AlgebraicGeometry.Modules.Flat.Generators
public import Aglib.Algebra.Homology.CochainComplex.BoundedAbove.ProjectiveHomotopy
public import Aglib.AlgebraicGeometry.Modules.Complex.Flat.BoundedAboveReplacement
public import Aglib.AlgebraicGeometry.Modules.Complex.Flat.BoundedPullback
public import Aglib.AlgebraicGeometry.Modules.Complex.Sheafification


/-!
# Actual flat models and homotopy-coherent chain comparisons

Projective replacements of the actual underlying presheaf complexes are
sheafified using the actual counit. Comparison triangles commute by genuine
chain homotopies. Original sheaf quasi-isomorphisms therefore give quasi-isomorphisms
of the flat models, and these remain quasi-isomorphisms after arbitrary pullback.
The forgetful functor to presheaves is never assumed exact.
-/
/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Sheaf/BoundedFlatModels.lean`.
SHA-256: `e77b85f102e65c7a29202c2987969b58fb7bcc0d24d02e1ac2bba97b0a728ecd`.
Selected source lines: 1–164.
Actual source objects, maps, hypotheses and independent universes are preserved.
-/

@[expose] public section

open CochainComplex


open AlgebraicGeometry.Scheme.Modules

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
namespace AlgebraicGeometry.Scheme.Modules

/-- Forgetting to the actual module presheaf preserves strict upper support. -/
def underlyingPresheafBoundedFunctor (X : Scheme.{u}) :
    BoundedAboveComplex X.Modules ⥤
      BoundedAboveComplex (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) where
  obj K :=
    { obj := ((SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).mapHomologicalComplex
        (.up ℤ)).obj K.obj
      property := by
        refine ⟨chosenUpperBound K, ?_⟩
        rw [CochainComplex.isStrictlyLE_iff]
        intro n hn
        exact (SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map_isZero
          (K.obj.isZero_of_isStrictlyLE (chosenUpperBound K) n hn) }
  map f := ObjectProperty.homMk
    (((SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).mapHomologicalComplex
      (.up ℤ)).map f.hom)

instance underlyingPresheafBoundedFunctor_additive (X : Scheme.{u}) :
    (underlyingPresheafBoundedFunctor X).Additive where
  map_add {K L} f g := by
    apply ObjectProperty.hom_ext
    exact ((SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).mapHomologicalComplex
      (.up ℤ)).map_add

/-- The selected actual flat model of a bounded-above sheaf complex. -/
def flatModel (X : Scheme.{u}) (K : BoundedAboveComplex X.Modules) : CochainComplex X.Modules ℤ :=
  ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapHomologicalComplex (.up ℤ)).obj
    (projectiveModel ((underlyingPresheafBoundedFunctor X).obj K))

/-- The augmentation from the sheafified projective presheaf model of a bounded-above complex `K`
to its original sheaf complex. -/
def flatModelπ (X : Scheme.{u}) (K : BoundedAboveComplex X.Modules) : flatModel X K ⟶ K.obj :=
  ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapHomologicalComplex (.up ℤ)).map
    (projectiveModelπ ((underlyingPresheafBoundedFunctor X).obj K)) ≫
    (sheafificationComplexCounitIso X K.obj).hom

instance flatModelπ_quasiIso (X : Scheme.{u}) (K : BoundedAboveComplex X.Modules) :
    QuasiIso (flatModelπ X K) := by
  let : (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).Additive :=
    SheafOfModulesOfCommRing.associatedSheaf_additive X.sheaf
  have : (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).PreservesHomology :=
    inferInstance
  have : QuasiIso (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapHomologicalComplex
    (.up ℤ)).map
      (projectiveModelπ ((underlyingPresheafBoundedFunctor X).obj K))) := inferInstance
  unfold flatModelπ
  infer_instance

theorem flatModel_flat (X : Scheme.{u}) (K : BoundedAboveComplex X.Modules) (n : ℤ) :
    stalkwiseFlat X ((flatModel X K).X n) :=
  stalkwiseFlat_sheafify_projective X _

instance flatModel_boundedAbove (X : Scheme.{u}) (K : BoundedAboveComplex X.Modules) :
    (flatModel X K).IsStrictlyLE
      (chosenUpperBound ((underlyingPresheafBoundedFunctor X).obj K)) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map_isZero
    ((projectiveModel ((underlyingPresheafBoundedFunctor X).obj K)).isZero_of_isStrictlyLE
      _ n hn)

/-- The actual sheafified projective chain comparison. -/
def flatModelMap {X : Scheme.{u}} {K L : BoundedAboveComplex X.Modules} (f : K ⟶ L) :
    flatModel X K ⟶ flatModel X L :=
  ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapHomologicalComplex (.up ℤ)).map
    (projectiveModelMap ((underlyingPresheafBoundedFunctor X).map f))

/-- The chosen flat models commute with every original chain map up to actual homotopy. -/
def flatModelMapHomotopy {X : Scheme.{u}} {K L : BoundedAboveComplex X.Modules} (f : K ⟶ L) :
    Homotopy (flatModelMap f ≫ flatModelπ X L) (flatModelπ X K ≫ f.hom) := by
  let A := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let : A.Additive := SheafOfModulesOfCommRing.associatedSheaf_additive X.sheaf
  let AH := A.mapHomologicalComplex (.up ℤ)
  let RK := (underlyingPresheafBoundedFunctor X).obj K
  let RL := (underlyingPresheafBoundedFunctor X).obj L
  let Rf := (underlyingPresheafBoundedFunctor X).map f
  have H := (A.mapHomotopy (projectiveModelMapHomotopy Rf)).compRight
    (sheafificationComplexCounitIso X L.obj).hom
  refine (Homotopy.ofEq ?_).trans (H.trans (Homotopy.ofEq ?_))
  · dsimp [flatModelMap, flatModelπ, AH, A, Rf]
    rw [Functor.map_comp, Category.assoc]
  · rw [Functor.map_comp, Category.assoc]
    exact (congrArg (fun t => AH.map (projectiveModelπ RK) ≫ t)
      (sheafificationComplexCounitIso_naturality f.hom)).trans (Category.assoc _ _ _).symm

/-- Original sheaf quasi-isomorphisms induce quasi-isomorphisms between the actual flat models.
The forgetful functor to presheaves is not assumed exact. -/
theorem flatModelMap_quasiIso {X : Scheme.{u}} {K L : BoundedAboveComplex X.Modules}
    (f : K ⟶ L) [QuasiIso f.hom] : QuasiIso (flatModelMap f) := by
  have : QuasiIso (flatModelMap f ≫ flatModelπ X L) := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap, (flatModelMapHomotopy f).homologyMap_eq n]
    infer_instance
  exact (quasiIso_iff_comp_right _ (flatModelπ X L)).mp inferInstance

variable {X Y : Scheme.{u}}

/-- Arbitrary scheme pullback now respects comparisons induced by original sheaf quasi-isomorphisms.
-/
theorem pullback_flatModelMap_quasiIso (f : X ⟶ Y) {K L : BoundedAboveComplex Y.Modules}
    (s : K ⟶ L) [QuasiIso s.hom] :
    QuasiIso ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).map (flatModelMap s)) := by
  let : QuasiIso (flatModelMap s) := flatModelMap_quasiIso s
  exact quasiIso_pullback_of_boundedAbove_stalkwiseFlat f (flatModel_flat Y K) (flatModel_flat Y L)
    (chosenUpperBound ((underlyingPresheafBoundedFunctor Y).obj K))
    (chosenUpperBound ((underlyingPresheafBoundedFunctor Y).obj L))
    (fun n hn => (flatModel Y K).isZero_of_isStrictlyLE _ n hn)
    (fun n hn => (flatModel Y L).isZero_of_isStrictlyLE _ n hn) _

end AlgebraicGeometry.Scheme.Modules
