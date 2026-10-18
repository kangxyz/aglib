/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Adjunction.InjectiveComplex
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.InjectiveResolution
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Native derived Hom through a supplied injective resolution

An additive adjunction whose left adjoint preserves monomorphisms gives a
pointwise Hom equivalence at the actual shifted injective resolution. Its
right-adjoint image is identified with the installed bounded-below right-derived
functor through the original unit and resolution inclusion, then included in
the full derived category. The source remains the original native single.

The chain-adjoint formula, both coefficient and source naturalities, the
original unit square and independence of the supplied resolution are retained.
Object, morphism and derived-model universes are independent. Enough injectives
is required only in the original target category to use its installed
right-derived right adjoint. No global adjunction of derived functors, exactness
of the left adjoint, or new instance is introduced.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u v w u' v' w'

namespace CategoryTheory.Adjunction

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Additive] [G.Additive]
  [F.PreservesMonomorphisms] [EnoughInjectives D]
  (M : C) {N : D} (I : InjectiveResolution N) (k : ℤ)

private theorem derived_map_surjective {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] (K L : CochainComplex A ℤ) [L.IsKInjective] :
    Function.Surjective (fun p : K ⟶ L => DerivedCategory.Q.map p) := by
  intro f
  obtain ⟨p, rfl⟩ := (CochainComplex.homotopyDerivedHomEquiv K L).surjective f
  obtain ⟨q, rfl⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective p
  exact ⟨q, (CochainComplex.homotopyDerivedHomEquiv_map K L q).symm⟩

omit [F.PreservesMonomorphisms] [EnoughInjectives D] in
private theorem cochainAdjunction_naturality_left
    {K K' : CochainComplex C ℤ} (L : CochainComplex D ℤ)
    [L.IsKInjective] [CochainComplex.IsKInjective ((G.mapHomologicalComplex (.up ℤ)).obj L)]
    (p : K' ⟶ K)
    (f : DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      DerivedCategory.Q.obj L) :
    adj.cochainDerivedHomEquivOfKInjective K' L
        (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map p) ≫ f) =
      DerivedCategory.Q.map p ≫ adj.cochainDerivedHomEquivOfKInjective K L f := by
  obtain ⟨q, rfl⟩ := derived_map_surjective _ L f
  rw [← Functor.map_comp, cochainDerivedHomEquivOfKInjective_map,
    (adj.mapHomologicalComplex (.up ℤ)).homEquiv_naturality_left,
    Functor.map_comp, cochainDerivedHomEquivOfKInjective_map]

omit [F.PreservesMonomorphisms] [EnoughInjectives D] in
private theorem cochainAdjunction_naturality_right
    (K : CochainComplex C ℤ) {L L' : CochainComplex D ℤ}
    [L.IsKInjective] [L'.IsKInjective]
    [CochainComplex.IsKInjective ((G.mapHomologicalComplex (.up ℤ)).obj L)]
    [CochainComplex.IsKInjective ((G.mapHomologicalComplex (.up ℤ)).obj L')]
    (p : L ⟶ L')
    (f : DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      DerivedCategory.Q.obj L) :
    adj.cochainDerivedHomEquivOfKInjective K L' (f ≫ DerivedCategory.Q.map p) =
      adj.cochainDerivedHomEquivOfKInjective K L f ≫
        DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map p) := by
  obtain ⟨q, rfl⟩ := derived_map_surjective _ L f
  rw [← Functor.map_comp, cochainDerivedHomEquivOfKInjective_map,
    (adj.mapHomologicalComplex (.up ℤ)).homEquiv_naturality_right,
    Functor.map_comp, cochainDerivedHomEquivOfKInjective_map]

/-- The original resolution inclusion identifies the shifted native single with the shifted
supplied resolution. -/
def resolutionShiftIso :
    ((DerivedCategory.singleFunctor D 0).obj N)⟦k⟧ ≅
      DerivedCategory.Q.obj (I.cochainComplex⟦k⟧) :=
  (shiftFunctor (DerivedCategory D) k).mapIso
      (asIso (DerivedCategory.Q.map I.ι')) ≪≫
    (DerivedCategory.Q.commShiftIso k).symm.app I.cochainComplex

/-- The original bounded-below model comparison, viewed in the full derived category. -/
def rightDerivedResolutionIso :
    DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) ≅
      DerivedCategory.Plus.ι.obj
        (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor D 0).obj N)) :=
  (DerivedCategory.Plus.QCompιIso C).symm.app
      (G.mapCochainComplexPlus.obj I.cochainComplexPlus) ≪≫
    DerivedCategory.Plus.ι.mapIso (I.rightDerivedFunctorPlusIso G)

/-- The shifted actual right-adjoint model retains both native shift comparisons. -/
def rightDerivedResolutionShiftIso :
    DerivedCategory.Q.obj
        ((G.mapHomologicalComplex (.up ℤ)).obj (I.cochainComplex⟦k⟧)) ≅
      (DerivedCategory.Plus.ι.obj
        (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor D 0).obj N)))⟦k⟧ :=
  DerivedCategory.Q.mapIso ((G.mapHomologicalComplex (.up ℤ)).commShiftIso k |>.app
      I.cochainComplex) ≪≫
    (DerivedCategory.Q.commShiftIso k).app
      ((G.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) ≪≫
    (shiftFunctor (DerivedCategory C) k).mapIso
      (rightDerivedResolutionIso (G := G) I)

/-- The original native comparison between the functor image of a single and the single of its
image. -/
def singleImageIso :
    DerivedCategory.Q.obj
        ((F.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor C 0).obj M)) ≅
      (DerivedCategory.singleFunctor D 0).obj (F.obj M) :=
  DerivedCategory.Q.mapIso ((F.mapCochainComplexSingleFunctor 0).app M)

omit [F.PreservesMonomorphisms] [EnoughInjectives D] [HasDerivedCategory.{w} C] in
/-- The native single comparison preserves the original source morphism. -/
theorem singleImageIso_naturality {M' : C} (p : M ⟶ M') :
    DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map
        ((CochainComplex.singleFunctor C 0).map p)) ≫
        (singleImageIso (F := F) M').hom =
      (singleImageIso (F := F) M).hom ≫
        (DerivedCategory.singleFunctor D 0).map (F.map p) := by
  have h := congrArg (DerivedCategory.Q (C := D)).map
    ((F.mapCochainComplexSingleFunctor 0).hom.naturality p)
  change DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map
      ((CochainComplex.singleFunctor C 0).map p)) ≫
      DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app M') =
    DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app M) ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor D 0).map (F.map p))
  simpa only [Functor.map_comp, Functor.comp_map] using h

/-- The forward model arrow is the original derived unit followed by the inverse derived
resolution inclusion. -/
theorem rightDerivedResolutionIso_hom :
    (rightDerivedResolutionIso (G := G) I).hom =
      (DerivedCategory.Plus.QCompιIso C).inv.app
          (G.mapCochainComplexPlus.obj I.cochainComplexPlus) ≫
        DerivedCategory.Plus.ι.map (G.rightDerivedFunctorPlusUnit.app I.cochainComplexPlus) ≫
        DerivedCategory.Plus.ι.map
          (inv (G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map I.ιPlus))) := by
  dsimp only [rightDerivedResolutionIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [InjectiveResolution.rightDerivedFunctorPlusIso_hom, Functor.map_comp]
  rfl

/-- The supplied-resolution model preserves the installed derived unit on the original
coefficient single. -/
theorem rightDerivedResolutionIso_unit :
    DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map I.ι') ≫
        (rightDerivedResolutionIso (G := G) I).hom =
      (DerivedCategory.Plus.QCompιIso C).inv.app
          (G.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus D 0).obj N)) ≫
        DerivedCategory.Plus.ι.map
          (G.rightDerivedFunctorPlusUnit.app ((CochainComplex.singleFunctorPlus D 0).obj N)) := by
  have hQ := (DerivedCategory.Plus.QCompιIso C).inv.naturality
    (G.mapCochainComplexPlus.map I.ιPlus)
  change DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map I.ι') ≫
      (DerivedCategory.Plus.QCompιIso C).inv.app
        (G.mapCochainComplexPlus.obj I.cochainComplexPlus) =
    (DerivedCategory.Plus.QCompιIso C).inv.app
        (G.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus D 0).obj N)) ≫
      DerivedCategory.Plus.ι.map
        (DerivedCategory.Plus.Q.map (G.mapCochainComplexPlus.map I.ιPlus)) at hQ
  have hR := congrArg (DerivedCategory.Plus.ι (C := C)).map
    (I.rightDerivedFunctorPlusIso_unit G)
  simp only [Functor.map_comp] at hR
  change _ ≫ ((DerivedCategory.Plus.QCompιIso C).inv.app
    (G.mapCochainComplexPlus.obj I.cochainComplexPlus) ≫
      DerivedCategory.Plus.ι.map (I.rightDerivedFunctorPlusIso G).hom) = _
  rw [← Category.assoc, hQ, Category.assoc, hR]

omit [EnoughInjectives D] in
/-- Every native resolution lift preserves the original shifted resolution inclusion. -/
theorem resolutionShiftIso_naturality {N' : D} {I' : InjectiveResolution N'}
    {f : N ⟶ N'} (φ : InjectiveResolution.Hom I I' f) :
    (shiftFunctor (DerivedCategory D) k).map ((DerivedCategory.singleFunctor D 0).map f) ≫
        (resolutionShiftIso I' k).hom =
      (resolutionShiftIso I k).hom ≫
        DerivedCategory.Q.map ((shiftFunctor (CochainComplex D ℤ) k).map φ.hom') := by
  have hι := congrArg (DerivedCategory.Q (C := D)).map φ.ι'_comp_hom'
  simp only [Functor.map_comp] at hι
  change DerivedCategory.Q.map I.ι' ≫ DerivedCategory.Q.map φ.hom' =
    (DerivedCategory.singleFunctor D 0).map f ≫ DerivedCategory.Q.map I'.ι' at hι
  change _ ≫ ((shiftFunctor (DerivedCategory D) k).map (DerivedCategory.Q.map I'.ι') ≫
    (DerivedCategory.Q.commShiftIso k).inv.app I'.cochainComplex) =
    ((shiftFunctor (DerivedCategory D) k).map (DerivedCategory.Q.map I.ι') ≫
      (DerivedCategory.Q.commShiftIso k).inv.app I.cochainComplex) ≫ _
  have hQ := (DerivedCategory.Q (C := D).commShiftIso k).inv.naturality φ.hom'
  change (shiftFunctor (DerivedCategory D) k).map (DerivedCategory.Q.map φ.hom') ≫
      (DerivedCategory.Q.commShiftIso k).inv.app I'.cochainComplex =
    (DerivedCategory.Q.commShiftIso k).inv.app I.cochainComplex ≫
      DerivedCategory.Q.map ((shiftFunctor (CochainComplex D ℤ) k).map φ.hom') at hQ
  rw [← Category.assoc, ← Functor.map_comp, ← hι, Functor.map_comp, Category.assoc,
    hQ, Category.assoc]

/-- Every native coefficient lift gives the original installed right-derived coefficient map. -/
theorem rightDerivedResolutionIso_naturality {N' : D} {I' : InjectiveResolution N'}
    {f : N ⟶ N'} (φ : InjectiveResolution.Hom I I' f) :
    DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map φ.hom') ≫
        (rightDerivedResolutionIso (G := G) I').hom =
      (rightDerivedResolutionIso (G := G) I).hom ≫
        DerivedCategory.Plus.ι.map (G.rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor D 0).map f)) := by
  have hQ := (DerivedCategory.Plus.QCompιIso C).inv.naturality
    (G.mapCochainComplexPlus.map φ.mapPlus)
  have hR := congrArg (DerivedCategory.Plus.ι (C := C)).map
    (I.rightDerivedFunctorPlusIso_naturality G φ)
  simp only [Functor.map_comp] at hR
  change DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map φ.hom') ≫
      (DerivedCategory.Plus.QCompιIso C).inv.app
        (G.mapCochainComplexPlus.obj I'.cochainComplexPlus) =
    (DerivedCategory.Plus.QCompιIso C).inv.app
        (G.mapCochainComplexPlus.obj I.cochainComplexPlus) ≫
      DerivedCategory.Plus.ι.map
        (DerivedCategory.Plus.Q.map (G.mapCochainComplexPlus.map φ.mapPlus)) at hQ
  change _ ≫ ((DerivedCategory.Plus.QCompιIso C).inv.app
    (G.mapCochainComplexPlus.obj I'.cochainComplexPlus) ≫ _) =
    ((DerivedCategory.Plus.QCompιIso C).inv.app
      (G.mapCochainComplexPlus.obj I.cochainComplexPlus) ≫ _) ≫ _
  simp only [Functor.mapIso_hom]
  rw [← Category.assoc, hQ, Category.assoc, hR, Category.assoc]

/-- The same coefficient lift commutes with the original shifted full-derived model. -/
theorem rightDerivedResolutionShiftIso_naturality {N' : D} {I' : InjectiveResolution N'}
    {f : N ⟶ N'} (φ : InjectiveResolution.Hom I I' f) :
    DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map
        ((shiftFunctor (CochainComplex D ℤ) k).map φ.hom')) ≫
        (rightDerivedResolutionShiftIso (G := G) I' k).hom =
      (rightDerivedResolutionShiftIso (G := G) I k).hom ≫
        (shiftFunctor (DerivedCategory C) k).map
          (DerivedCategory.Plus.ι.map (G.rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor D 0).map f))) := by
  have hG := congrArg (DerivedCategory.Q (C := C)).map
    (((G.mapHomologicalComplex (.up ℤ)).commShiftIso k).hom.naturality φ.hom')
  simp only [Functor.map_comp, Functor.comp_map] at hG
  have hQ := (DerivedCategory.Q (C := C).commShiftIso k).hom.naturality
    ((G.mapHomologicalComplex (.up ℤ)).map φ.hom')
  simp only [Functor.comp_map] at hQ
  have hR := congrArg (shiftFunctor (DerivedCategory C) k).map
    (rightDerivedResolutionIso_naturality (G := G) I φ)
  simp only [Functor.map_comp] at hR
  dsimp only [rightDerivedResolutionShiftIso, Iso.trans_hom, Functor.mapIso_hom]
  simp only [Iso.app_hom]
  have hG' := congrArg (fun z => z ≫
    (DerivedCategory.Q.commShiftIso k).hom.app
      ((G.mapHomologicalComplex (.up ℤ)).obj I'.cochainComplex) ≫
    (shiftFunctor (DerivedCategory C) k).map (rightDerivedResolutionIso (G := G) I').hom) hG
  have hQ' := congrArg (fun z =>
    DerivedCategory.Q.map (((G.mapHomologicalComplex (.up ℤ)).commShiftIso k).hom.app
      I.cochainComplex) ≫ z ≫
    (shiftFunctor (DerivedCategory C) k).map (rightDerivedResolutionIso (G := G) I').hom) hQ
  have hR' := congrArg (fun z =>
    DerivedCategory.Q.map (((G.mapHomologicalComplex (.up ℤ)).commShiftIso k).hom.app
      I.cochainComplex) ≫
    (DerivedCategory.Q.commShiftIso k).hom.app
      ((G.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) ≫ z) hR
  simp only [Category.assoc] at hG' hQ' hR' ⊢
  exact hG'.trans (hQ'.trans hR')

/-- The original pointwise derived adjunction at a shifted supplied injective resolution; no
K-injectivity premise is supplied. -/
def cochainDerivedHomEquivOfInjectiveResolution (K : CochainComplex C ℤ) :
    (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      DerivedCategory.Q.obj (I.cochainComplex⟦k⟧)) ≃+
    (DerivedCategory.Q.obj K ⟶
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj (I.cochainComplex⟦k⟧))) := by
  let L := I.cochainComplex⟦k⟧
  let : L.IsStrictlyGE (-k) := I.cochainComplex.isStrictlyGE_shift 0 k (-k) (by omega)
  let : ∀ n : ℤ, Injective (L.X n) := fun n => by
    change Injective (I.cochainComplex.X (n + k))
    infer_instance
  exact adj.cochainDerivedHomEquivOfInjectiveComplex K L (-k)

omit [EnoughInjectives D] in
/-- Each original chain representative is sent to its original chain adjoint. -/
theorem cochainDerivedHomEquivOfInjectiveResolution_map (K : CochainComplex C ℤ)
    (p : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ I.cochainComplex⟦k⟧) :
    adj.cochainDerivedHomEquivOfInjectiveResolution I k K (DerivedCategory.Q.map p) =
      DerivedCategory.Q.map
        ((adj.mapHomologicalComplex (.up ℤ)).homEquiv K (I.cochainComplex⟦k⟧) p) := by
  let L := I.cochainComplex⟦k⟧
  let : L.IsStrictlyGE (-k) := I.cochainComplex.isStrictlyGE_shift 0 k (-k) (by omega)
  let : ∀ n : ℤ, Injective (L.X n) := fun n => by
    change Injective (I.cochainComplex.X (n + k)); infer_instance
  exact adj.cochainDerivedHomEquivOfInjectiveComplex_map K L (-k) p

omit [EnoughInjectives D] in
/-- Original source-chain precomposition commutes with the supplied-resolution adjunction. -/
theorem cochainDerivedHomEquivOfInjectiveResolution_naturality_left
    {K K' : CochainComplex C ℤ} (p : K' ⟶ K)
    (f : DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      DerivedCategory.Q.obj (I.cochainComplex⟦k⟧)) :
    adj.cochainDerivedHomEquivOfInjectiveResolution I k K'
        (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map p) ≫ f) =
      DerivedCategory.Q.map p ≫
        adj.cochainDerivedHomEquivOfInjectiveResolution I k K f := by
  let L := I.cochainComplex⟦k⟧
  let : L.IsStrictlyGE (-k) := I.cochainComplex.isStrictlyGE_shift 0 k (-k) (by omega)
  let : ∀ n : ℤ, Injective (L.X n) := fun n => by
    change Injective (I.cochainComplex.X (n + k))
    infer_instance
  let : L.IsKInjective := CochainComplex.isKInjective_of_injective L (-k)
  let := adj.isKInjective_map_of_injectiveComplex L (-k)
  exact cochainAdjunction_naturality_left adj L p f

omit [EnoughInjectives D] in
/-- Original resolution-chain postcomposition commutes with the supplied-resolution
adjunction. -/
theorem cochainDerivedHomEquivOfInjectiveResolution_naturality_right
    (K : CochainComplex C ℤ) {N' : D} (I' : InjectiveResolution N')
    (p : I.cochainComplex ⟶ I'.cochainComplex)
    (f : DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      DerivedCategory.Q.obj (I.cochainComplex⟦k⟧)) :
    adj.cochainDerivedHomEquivOfInjectiveResolution I' k K
        (f ≫ DerivedCategory.Q.map ((shiftFunctor (CochainComplex D ℤ) k).map p)) =
      adj.cochainDerivedHomEquivOfInjectiveResolution I k K f ≫
        DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map
          ((shiftFunctor (CochainComplex D ℤ) k).map p)) := by
  let L := I.cochainComplex⟦k⟧
  let L' := I'.cochainComplex⟦k⟧
  let : L.IsStrictlyGE (-k) := I.cochainComplex.isStrictlyGE_shift 0 k (-k) (by omega)
  let : L'.IsStrictlyGE (-k) := I'.cochainComplex.isStrictlyGE_shift 0 k (-k) (by omega)
  let : ∀ n : ℤ, Injective (L.X n) := fun n => by
    change Injective (I.cochainComplex.X (n + k)); infer_instance
  let : ∀ n : ℤ, Injective (L'.X n) := fun n => by
    change Injective (I'.cochainComplex.X (n + k)); infer_instance
  let : L.IsKInjective := CochainComplex.isKInjective_of_injective L (-k)
  let : L'.IsKInjective := CochainComplex.isKInjective_of_injective L' (-k)
  let := adj.isKInjective_map_of_injectiveComplex L (-k)
  let := adj.isKInjective_map_of_injectiveComplex L' (-k)
  exact cochainAdjunction_naturality_right adj K
    ((shiftFunctor (CochainComplex D ℤ) k).map p) f

/-- The actual full-derived Hom comparison from a native image single to the installed right-
derived right adjoint. -/
def singleDerivedHomEquivOfInjectiveResolution :
    ((DerivedCategory.singleFunctor D 0).obj (F.obj M) ⟶
      ((DerivedCategory.singleFunctor D 0).obj N)⟦k⟧) ≃+
    ((DerivedCategory.singleFunctor C 0).obj M ⟶
      (DerivedCategory.Plus.ι.obj
        (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor D 0).obj N)))⟦k⟧) := by
  let K := (CochainComplex.singleFunctor C 0).obj M
  let L := I.cochainComplex⟦k⟧
  let e₁ :
      ((DerivedCategory.singleFunctor D 0).obj (F.obj M) ⟶
          ((DerivedCategory.singleFunctor D 0).obj N)⟦k⟧) ≃+
        (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶
          DerivedCategory.Q.obj L) :=
    { Iso.homCongr (singleImageIso (F := F) M).symm (resolutionShiftIso I k) with
      map_add' f g := by simp [Iso.homCongr_apply, Preadditive.comp_add, Preadditive.add_comp] }
  let e₂ := adj.cochainDerivedHomEquivOfInjectiveResolution I k K
  let e₃ :
      (DerivedCategory.Q.obj K ⟶
          DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj L)) ≃+
        ((DerivedCategory.singleFunctor C 0).obj M ⟶
          (DerivedCategory.Plus.ι.obj
            (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor D 0).obj N)))⟦k⟧) :=
    { Iso.homCongr (Iso.refl _)
        (rightDerivedResolutionShiftIso (G := G) I k) with
      map_add' f g := by simp [Iso.homCongr_apply, Preadditive.comp_add, Preadditive.add_comp] }
  exact (e₁.trans e₂).trans e₃

/-- The forward equivalence retains the native single, resolution, pointwise adjunction and
installed derived-unit factors. -/
theorem singleDerivedHomEquivOfInjectiveResolution_apply
    (f : (DerivedCategory.singleFunctor D 0).obj (F.obj M) ⟶
      ((DerivedCategory.singleFunctor D 0).obj N)⟦k⟧) :
    adj.singleDerivedHomEquivOfInjectiveResolution M I k f =
      adj.cochainDerivedHomEquivOfInjectiveResolution I k
          ((CochainComplex.singleFunctor C 0).obj M)
          ((singleImageIso (F := F) M).hom ≫ f ≫ (resolutionShiftIso I k).hom) ≫
        (rightDerivedResolutionShiftIso (G := G) I k).hom := by
  change 𝟙 _ ≫
    adj.cochainDerivedHomEquivOfInjectiveResolution I k
      ((CochainComplex.singleFunctor C 0).obj M)
      ((singleImageIso (F := F) M).hom ≫ f ≫ (resolutionShiftIso I k).hom) ≫
      (rightDerivedResolutionShiftIso (G := G) I k).hom = _
  rw [Category.id_comp]

/-- An original chain representative has exactly the original chain adjoint followed by the
installed model comparison. -/
theorem singleDerivedHomEquivOfInjectiveResolution_map
    (p : (F.mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor C 0).obj M) ⟶ I.cochainComplex⟦k⟧) :
    adj.singleDerivedHomEquivOfInjectiveResolution M I k
        ((singleImageIso (F := F) M).inv ≫ DerivedCategory.Q.map p ≫
          (resolutionShiftIso I k).inv) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv
          ((CochainComplex.singleFunctor C 0).obj M) (I.cochainComplex⟦k⟧) p) ≫
        (rightDerivedResolutionShiftIso (G := G) I k).hom := by
  rw [singleDerivedHomEquivOfInjectiveResolution_apply]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [cochainDerivedHomEquivOfInjectiveResolution_map]

/-- Every original source morphism acts by native single-functor precomposition. -/
theorem singleDerivedHomEquivOfInjectiveResolution_naturality_left
    {M' : C} (p : M ⟶ M')
    (f : (DerivedCategory.singleFunctor D 0).obj (F.obj M') ⟶
      ((DerivedCategory.singleFunctor D 0).obj N)⟦k⟧) :
    adj.singleDerivedHomEquivOfInjectiveResolution M I k
        ((DerivedCategory.singleFunctor D 0).map (F.map p) ≫ f) =
      (DerivedCategory.singleFunctor C 0).map p ≫
        adj.singleDerivedHomEquivOfInjectiveResolution M' I k f := by
  have hF := singleImageIso_naturality (F := F) M p
  have h := adj.cochainDerivedHomEquivOfInjectiveResolution_naturality_left I k
    ((CochainComplex.singleFunctor C 0).map p)
    ((singleImageIso (F := F) M').hom ≫ f ≫ (resolutionShiftIso I k).hom)
  have h' := congrArg (fun z => z ≫ (rightDerivedResolutionShiftIso (G := G) I k).hom) h
  rw [singleDerivedHomEquivOfInjectiveResolution_apply,
    singleDerivedHomEquivOfInjectiveResolution_apply]
  have hF' := congrArg (fun z => z ≫ f ≫ (resolutionShiftIso I k).hom) hF
  simp only [Category.assoc] at hF' h' ⊢
  rw [← hF']
  exact h'

/-- Every native coefficient-resolution lift acts by the original shifted right-derived
coefficient map. -/
theorem singleDerivedHomEquivOfInjectiveResolution_naturality_right
    {N' : D} {I' : InjectiveResolution N'} {p : N ⟶ N'}
    (φ : InjectiveResolution.Hom I I' p)
    (f : (DerivedCategory.singleFunctor D 0).obj (F.obj M) ⟶
      ((DerivedCategory.singleFunctor D 0).obj N)⟦k⟧) :
    adj.singleDerivedHomEquivOfInjectiveResolution M I' k
        (f ≫ (shiftFunctor (DerivedCategory D) k).map
          ((DerivedCategory.singleFunctor D 0).map p)) =
      adj.singleDerivedHomEquivOfInjectiveResolution M I k f ≫
        (shiftFunctor (DerivedCategory C) k).map
          (DerivedCategory.Plus.ι.map (G.rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor D 0).map p))) := by
  have hι := resolutionShiftIso_naturality I k φ
  have h := adj.cochainDerivedHomEquivOfInjectiveResolution_naturality_right I k
    ((CochainComplex.singleFunctor C 0).obj M) I' φ.hom'
    ((singleImageIso (F := F) M).hom ≫ f ≫ (resolutionShiftIso I k).hom)
  have h' := congrArg (fun z => z ≫ (rightDerivedResolutionShiftIso (G := G) I' k).hom) h
  rw [singleDerivedHomEquivOfInjectiveResolution_apply,
    singleDerivedHomEquivOfInjectiveResolution_apply]
  simp only [Category.assoc] at h' ⊢
  rw [hι]
  rw [h']
  rw [rightDerivedResolutionShiftIso_naturality]

/-- The original full-derived Hom equivalence is independent of the supplied injective
resolution. -/
theorem singleDerivedHomEquivOfInjectiveResolution_independent
    (I' : InjectiveResolution N) :
    adj.singleDerivedHomEquivOfInjectiveResolution M I k =
      adj.singleDerivedHomEquivOfInjectiveResolution M I' k := by
  let φ : InjectiveResolution.Hom I I' (𝟙 N) :=
    ⟨InjectiveResolution.desc (𝟙 N) I' I, by
      simpa only [CochainComplex.single₀_map_f_zero] using
        InjectiveResolution.desc_commutes_zero (𝟙 N) I' I⟩
  ext f
  have h := adj.singleDerivedHomEquivOfInjectiveResolution_naturality_right M I k φ f
  simpa only [Functor.map_id, Category.comp_id] using h.symm

end CategoryTheory.Adjunction
