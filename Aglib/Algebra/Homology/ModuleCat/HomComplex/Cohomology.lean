/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ModuleCat.HomComplex.Derived
public import Aglib.Algebra.Homology.ModuleCat.HomComplex.Coinduction
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-!
# Original module Hom cohomology and Ext

The native module-valued Hom complex computes original derived morphisms
through its original cocycles. Scalar compatibility is proved using actual
source multiplication. For a supplied coefficient quasi-isomorphism, the
comparison computes native Ext with that same augmentation and shift.

The coinduced specialization starts from intrinsic A-module homology and
restricts its scalars along the actual ring map. Its chain comparison is
the original evaluation-at-one counit, followed by the native comparison
with the restricted source single. No canonical-sheaf or trace assertion
is made here.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open CategoryTheory.Abelian

universe u v w e

attribute [local instance] CategoryTheory.Linear.opposite

private theorem compose_three_squares {C : Type*} [Category* C]
    {X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃ : C}
    (f₀ : X₀ ⟶ Y₀) (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃)
    (a₀ : X₀ ⟶ X₁) (a₁ : X₁ ⟶ X₂) (a₂ : X₂ ⟶ X₃)
    (b₀ : Y₀ ⟶ Y₁) (b₁ : Y₁ ⟶ Y₂) (b₂ : Y₂ ⟶ Y₃)
    (h₀ : f₀ ≫ b₀ = a₀ ≫ f₁) (h₁ : f₁ ≫ b₁ = a₁ ≫ f₂)
    (h₂ : f₂ ≫ b₂ = a₂ ≫ f₃) :
    f₀ ≫ b₀ ≫ b₁ ≫ b₂ = (a₀ ≫ a₁ ≫ a₂) ≫ f₃ := by
  calc
    _ = (f₀ ≫ b₀) ≫ b₁ ≫ b₂ := by simp only [Category.assoc]
    _ = a₀ ≫ (f₁ ≫ b₁) ≫ b₂ := by rw [h₀]; simp only [Category.assoc]
    _ = a₀ ≫ a₁ ≫ (f₂ ≫ b₂) := by rw [h₁]; simp only [Category.assoc]
    _ = _ := by rw [h₂]; simp only [Category.assoc]

/-- The additive comparison of complete module and additive functors at an object. -/
def ModuleCat.natIsoAddEquiv {C : Type*} [Category* C] {S : Type*} [Ring S]
    (F : C ⥤ ModuleCat.{v} S) (G : C ⥤ AddCommGrpCat.{v})
    (e : F ⋙ forget₂ (ModuleCat.{v} S) AddCommGrpCat ≅ G) (X : C) :
    F.obj X ≃+ G.obj X :=
  (e.app X).addCommGroupIsoToAddEquiv

private theorem module_natIsoAddEquiv_naturality
    {C : Type*} [Category* C] {S : Type*} [Ring S]
    (F : C ⥤ ModuleCat.{v} S) (G : C ⥤ AddCommGrpCat.{v})
    (e : F ⋙ forget₂ (ModuleCat.{v} S) AddCommGrpCat ≅ G)
    {X Y : C} (f : X ⟶ Y) (x : F.obj X) :
    ModuleCat.natIsoAddEquiv F G e Y (F.map f x) =
      G.map f (ModuleCat.natIsoAddEquiv F G e X x) :=
  ConcreteCategory.congr_hom (e.hom.naturality f) x

/-- Compose the complete functor comparison with an additive identification of its value. -/
def ModuleCat.natIsoAddEquivTrans {C : Type*} [Category* C] {S : Type*} [Ring S]
    (F : C ⥤ ModuleCat.{v} S) (G : C ⥤ AddCommGrpCat.{v})
    (e : F ⋙ forget₂ (ModuleCat.{v} S) AddCommGrpCat ≅ G) (X : C)
    {Z : Type*} [AddCommGroup Z] (d : G.obj X ≃+ Z) : F.obj X ≃+ Z :=
  (ModuleCat.natIsoAddEquiv F G e X).trans d

/-- Source scalar naturality makes the original additive comparison linear before specialization. -/
def ModuleCat.natIsoAddEquivTransLinear
    {C : Type*} [Category* C] [Preadditive C] {S : Type*} [CommRing S] [Linear S C]
    (F : C ⥤ ModuleCat.{v} S) [F.Linear S] (G : C ⥤ AddCommGrpCat.{v})
    (e : F ⋙ forget₂ (ModuleCat.{v} S) AddCommGrpCat ≅ G) (X : C)
    {Z : Type*} [AddCommGroup Z] [Module S Z] (d : G.obj X ≃+ Z)
    (hd : ∀ (r : S) (y : G.obj X), d (G.map (r • 𝟙 X) y) = r • d y) :
    F.obj X ≃ₗ[S] Z :=
  { ModuleCat.natIsoAddEquivTrans F G e X d with
    map_smul' r x := by
      have h := module_natIsoAddEquiv_naturality F G e (r • 𝟙 X) x
      rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id] at h
      change ModuleCat.natIsoAddEquiv F G e X (r • x) =
        G.map (r • 𝟙 X) (ModuleCat.natIsoAddEquiv F G e X x) at h
      exact (congrArg d h).trans (hd r (ModuleCat.natIsoAddEquiv F G e X x)) }

private theorem cancel_linear_equiv_composite
    {S : Type*} [Semiring S] {W X Y Z : Type*}
    [AddCommMonoid W] [AddCommMonoid X] [AddCommMonoid Y] [AddCommMonoid Z]
    [Module S W] [Module S X] [Module S Y] [Module S Z]
    (e₁ : W ≃ₗ[S] X) (e₂ : Y ≃ₗ[S] X) (e₃ : Z ≃ₗ[S] Y) (x : W) :
    e₃ ((e₁.trans (e₂.symm.trans e₃.symm)) x) = e₂.symm (e₁ x) := by
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

namespace CochainComplex.HomComplex

/-- The native cohomology classes with their original source-precomposition maps. -/
def cohomologyClassFunctor {C : Type u} [Category.{v} C] [Preadditive C]
    (J : CochainComplex C ℤ) (n : ℤ) : (CochainComplex C ℤ)ᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj K := AddCommGrpCat.of (CohomologyClass K.unop J n)
  map f := AddCommGrpCat.ofHom (cohomologyPrecomp f.unop J n)
  map_id K := by
    apply ConcreteCategory.hom_ext
    intro x
    let e := CohomologyClass.homAddEquiv (K := K.unop) (L := J) (n := n)
    apply e.injective
    change e (e.symm ((HomotopyCategory.quotient C (.up ℤ)).map (𝟙 K.unop) ≫ e x)) = e x
    rw [AddEquiv.apply_symm_apply, CategoryTheory.Functor.map_id, Category.id_comp]
  map_comp {K L M} f g := by
    apply ConcreteCategory.hom_ext
    intro x
    let eK := CohomologyClass.homAddEquiv (K := K.unop) (L := J) (n := n)
    let eL := CohomologyClass.homAddEquiv (K := L.unop) (L := J) (n := n)
    let eM := CohomologyClass.homAddEquiv (K := M.unop) (L := J) (n := n)
    let Q := HomotopyCategory.quotient C (.up ℤ)
    apply eM.injective
    change eM (eM.symm (Q.map (g.unop ≫ f.unop) ≫ eK x)) =
      eM (eM.symm (Q.map g.unop ≫ eL (eL.symm (Q.map f.unop ≫ eK x))))
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, CategoryTheory.Functor.map_comp, Category.assoc]

variable {R : Type u} [CommRing R]

/-- Native homology of the original fixed-coefficient module Hom functor. -/
def moduleHomologyFunctor (J : CochainComplex (ModuleCat.{max u v} R) ℤ) (n : ℤ) :
    (CochainComplex (ModuleCat.{max u v} R) ℤ)ᵒᵖ ⥤ ModuleCat.{max u v} R :=
  moduleComplexFunctor R J ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{max u v} R) (.up ℤ) n


/-- The original forgetful homology comparison, identity Hom-complex
comparison and native cohomology-class comparison, in that order. -/
def moduleHomologyClassesIso (K J : CochainComplex (ModuleCat.{max u v} R) ℤ) (n : ℤ) :
    (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat).obj
        ((moduleComplex R K J).homology n) ≅
      AddCommGrpCat.of (CohomologyClass K J n) :=
  (((moduleComplex R K J).sc n).mapHomologyIso
      (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat)).symm ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) n).mapIso
      (moduleComplexForgetIso R K J) ≪≫ (leftHomologyData K J n).homologyIso

/-- Naturality uses the actual module homology map and the existing
cochain precomposition homology data. -/
theorem moduleHomologyClassesIso_precomp
    {K L : CochainComplex (ModuleCat.{max u v} R) ℤ} (f : K ⟶ L)
    (J : CochainComplex (ModuleCat.{max u v} R) ℤ) (n : ℤ) :
    (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat).map
        (HomologicalComplex.homologyMap (precomp R f J) n) ≫
      (moduleHomologyClassesIso K J n).hom =
    (moduleHomologyClassesIso L J n).hom ≫
      AddCommGrpCat.ofHom (cohomologyPrecomp f J n) := by
  let U := forget₂ (ModuleCat.{max u v} R) AddCommGrpCat
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) n
  let g := precomp R f J
  let aK : U.obj ((moduleComplex R K J).homology n) ⟶
      H.obj ((U.mapHomologicalComplex (.up ℤ)).obj (moduleComplex R K J)) :=
    (((moduleComplex R K J).sc n).mapHomologyIso U).inv
  let aL : U.obj ((moduleComplex R L J).homology n) ⟶
      H.obj ((U.mapHomologicalComplex (.up ℤ)).obj (moduleComplex R L J)) :=
    (((moduleComplex R L J).sc n).mapHomologyIso U).inv
  let bK : H.obj ((U.mapHomologicalComplex (.up ℤ)).obj (moduleComplex R K J)) ⟶
      H.obj (HomComplex K J) := H.map (moduleComplexForgetIso R K J).hom
  let bL : H.obj ((U.mapHomologicalComplex (.up ℤ)).obj (moduleComplex R L J)) ⟶
      H.obj (HomComplex L J) := H.map (moduleComplexForgetIso R L J).hom
  let cK : H.obj (HomComplex K J) ⟶ AddCommGrpCat.of (CohomologyClass K J n) :=
    (leftHomologyData K J n).homologyIso.hom
  let cL : H.obj (HomComplex L J) ⟶ AddCommGrpCat.of (CohomologyClass L J n) :=
    (leftHomologyData L J n).homologyIso.hom
  have h₁ := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{max u v} R) (.up ℤ) n).map g) U
  change U.map (HomologicalComplex.homologyMap g n) ≫ aK =
    aL ≫ H.map ((U.mapHomologicalComplex (.up ℤ)).map g) at h₁
  have h₂ := congrArg H.map (moduleComplexForgetIso_precomp R f J)
  simp only [CategoryTheory.Functor.map_comp] at h₂
  change H.map ((U.mapHomologicalComplex (.up ℤ)).map g) ≫ bK =
    bL ≫ H.map (additivePrecomp f J) at h₂
  have h₃ := (additivePrecompHomologyMapData f J n).homologyMap_comm
  change H.map (additivePrecomp f J) ≫ cK =
    cL ≫ AddCommGrpCat.ofHom (cohomologyPrecomp f J n) at h₃
  change U.map (HomologicalComplex.homologyMap g n) ≫ aK ≫ bK ≫ cK =
    (aL ≫ bL ≫ cL) ≫ AddCommGrpCat.ofHom (cohomologyPrecomp f J n)
  exact compose_three_squares _ _ _ _ aL bL cL aK bK cK h₁ h₂ h₃

/-- The complete original homology-to-class comparison, with the three original components. -/
def moduleHomologyClassesNatIso
    (J : CochainComplex (ModuleCat.{max u v} R) ℤ) (n : ℤ) :
    moduleHomologyFunctor J n ⋙ forget₂ (ModuleCat.{max u v} R) AddCommGrpCat ≅
      cohomologyClassFunctor J n :=
  NatIso.ofComponents (fun K => moduleHomologyClassesIso K.unop J n) (by
    intro K L f
    exact moduleHomologyClassesIso_precomp f.unop J n)

/-- The original class comparison obtained from the complete natural isomorphism. -/
def moduleHomologyClassesAddEquiv
    (K J : CochainComplex (ModuleCat.{max u v} R) ℤ) (n : ℤ) :
    (moduleComplex R K J).homology n ≃+ CohomologyClass K J n :=
  ModuleCat.natIsoAddEquiv (moduleHomologyFunctor J n) (cohomologyClassFunctor J n)
    (moduleHomologyClassesNatIso J n) (op K)

/-- The typed additive comparison has exactly the original class-isomorphism value. -/
theorem moduleHomologyClassesAddEquiv_apply
    (K J : CochainComplex (ModuleCat.{max u v} R) ℤ) (n : ℤ)
    (x : (moduleComplex R K J).homology n) :
    moduleHomologyClassesAddEquiv K J n x =
      (moduleHomologyClassesIso K J n).addCommGroupIsoToAddEquiv x := rfl

/-- The actual scalar multiple of a chain map induces the same scalar
multiple on native module homology. -/
theorem moduleHomologyMap_smul {K L : CochainComplex (ModuleCat.{max u v} R) ℤ}
    (f : K ⟶ L) (r : R) (n : ℤ) :
    HomologicalComplex.homologyMap (r • f) n =
      r • HomologicalComplex.homologyMap f n := by
  have hs : (HomologicalComplex.shortComplexFunctor (ModuleCat.{max u v} R) (.up ℤ) n).map
        (r • f) =
      r • (HomologicalComplex.shortComplexFunctor (ModuleCat.{max u v} R) (.up ℤ) n).map f := by
    ext <;> rfl
  change ShortComplex.homologyMap _ = r • ShortComplex.homologyMap _
  rw [hs, ShortComplex.homologyMap_smul]
  rfl

/-- The native fixed-coefficient homology functor preserves original scalar multiples. -/
instance moduleHomologyFunctor_linear
    (J : CochainComplex (ModuleCat.{max u v} R) ℤ) (n : ℤ) :
    (moduleHomologyFunctor J n).Linear R where
  map_smul {K L} f r := by
    have h := (moduleComplexFunctor R J).map_smul r f
    change precomp R (r • f).unop J = r • precomp R f.unop J at h
    change HomologicalComplex.homologyMap (precomp R (r • f).unop J) n =
      r • HomologicalComplex.homologyMap (precomp R f.unop J) n
    rw [h, moduleHomologyMap_smul]

/-- Original scalar source multiplication acts by that scalar on the
native module-valued Hom complex. -/
theorem precomp_smul_id (K J : CochainComplex (ModuleCat.{max u v} R) ℤ) (r : R) :
    precomp R (r • 𝟙 K) J = r • 𝟙 (moduleComplex R K J) := by
  have h := (moduleComplexFunctor R J).map_smul r ((𝟙 K).op)
  change precomp R (r • 𝟙 K) J = r • precomp R (𝟙 K) J at h
  simpa only [precomp_id] using h

/-- A coefficient complex supported in nonnegative degrees gives an
actual nonnegative Hom complex from a degree-zero single. -/
theorem moduleComplex_single_isStrictlyGE_zero (M : ModuleCat.{max u v} R)
    (J : CochainComplex (ModuleCat.{max u v} R) ℤ) [J.IsStrictlyGE 0] :
    (moduleComplex R ((singleFunctor (ModuleCat.{max u v} R) 0).obj M) J).IsStrictlyGE 0 := by
  rw [isStrictlyGE_iff]
  intro n hn
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun x y => ?_⟩
  apply (Cochain.fromSingleEquiv (X := M) (K := J) (zero_add n)).injective
  exact (J.isZero_of_isStrictlyGE 0 n hn).eq_of_tgt _ _

variable [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]

/-- The original module homology class is sent to its original localized
cocycle morphism, using the existing fixed K-injective comparison. -/
def moduleHomologyDerivedAddEquiv
    (K J : CochainComplex (ModuleCat.{max u v} R) ℤ) [J.IsKInjective] (n : ℤ) :
    (moduleComplex R K J).homology n ≃+
      (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (J⟦n⟧)) :=
  ModuleCat.natIsoAddEquivTrans (moduleHomologyFunctor J n) (cohomologyClassFunctor J n)
    (moduleHomologyClassesNatIso J n) (op K) (cohomologyDerivedEquiv K J n)

/-- The forward comparison is the original class map followed by original localization. -/
theorem moduleHomologyDerivedAddEquiv_apply
    (K J : CochainComplex (ModuleCat.{max u v} R) ℤ) [J.IsKInjective] (n : ℤ)
    (x : (moduleComplex R K J).homology n) :
    moduleHomologyDerivedAddEquiv K J n x = cohomologyDerivedEquiv K J n
      (moduleHomologyClassesAddEquiv K J n x) := rfl

/-- Original scalar source multiplication becomes the original scalar on the localized arrow. -/
theorem cohomologyDerivedEquiv_precomp_smul_id
    (K J : CochainComplex (ModuleCat.{max u v} R) ℤ) [J.IsKInjective] (n : ℤ)
    (r : R) (x : CohomologyClass K J n) :
    cohomologyDerivedEquiv K J n (cohomologyPrecomp (r • 𝟙 K) J n x) =
      r • cohomologyDerivedEquiv K J n x := by
  rw [cohomologyDerivedEquiv_precomp, CategoryTheory.Functor.map_smul,
    CategoryTheory.Functor.map_id, Linear.smul_comp, Category.id_comp]

/-- The original comparison is R-linear for native module homology.
Its proof uses source multiplication; no action is transported onto cohomology. -/
def moduleHomologyDerivedLinearEquiv
    (K J : CochainComplex (ModuleCat.{max u v} R) ℤ) [J.IsKInjective] (n : ℤ) :
    (moduleComplex R K J).homology n ≃ₗ[R]
      (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (J⟦n⟧)) :=
  ModuleCat.natIsoAddEquivTransLinear
    (moduleHomologyFunctor J n) (cohomologyClassFunctor J n)
    (moduleHomologyClassesNatIso J n) (op K) (cohomologyDerivedEquiv K J n)
    (fun r x => cohomologyDerivedEquiv_precomp_smul_id K J n r x)

/-- Linearity changes only the proof fields of the original additive comparison. -/
theorem moduleHomologyDerivedLinearEquiv_apply
    (K J : CochainComplex (ModuleCat.{max u v} R) ℤ) [J.IsKInjective] (n : ℤ)
    (x : (moduleComplex R K J).homology n) :
    moduleHomologyDerivedLinearEquiv K J n x = moduleHomologyDerivedAddEquiv K J n x := rfl

omit [HasDerivedCategory.{w} (ModuleCat.{max u v} R)] in
/-- The native homology class represented by an original Hom cocycle. -/
def moduleCocycleClass (K J : CochainComplex (ModuleCat.{max u v} R) ℤ) (n : ℤ)
    (x : Cocycle K J n) : (moduleComplex R K J).homology n :=
  (moduleHomologyClassesAddEquiv K J n).symm (CohomologyClass.mk x)

omit [HasDerivedCategory.{w} (ModuleCat.{max u v} R)] in
/-- The original class comparison sends this homology representative to its given cocycle class. -/
theorem moduleCocycleClass_comparison
    (K J : CochainComplex (ModuleCat.{max u v} R) ℤ) (n : ℤ) (x : Cocycle K J n) :
    moduleHomologyClassesAddEquiv K J n (moduleCocycleClass K J n x) = CohomologyClass.mk x :=
  (moduleHomologyClassesAddEquiv K J n).apply_symm_apply _

/-- An original cocycle is sent to the localization of its native shifted chain map. -/
theorem moduleHomologyDerivedLinearEquiv_cocycle
    (K J : CochainComplex (ModuleCat.{max u v} R) ℤ) [J.IsKInjective] (n : ℤ)
    (x : Cocycle K J n) :
    moduleHomologyDerivedLinearEquiv K J n (moduleCocycleClass K J n x) =
      DerivedCategory.Q.map (Cocycle.equivHomShift.symm x) := by
  rw [moduleHomologyDerivedLinearEquiv_apply, moduleHomologyDerivedAddEquiv_apply,
    moduleCocycleClass_comparison]
  unfold cohomologyDerivedEquiv
  rw [AddEquiv.trans_apply, CohomologyClass.homAddEquiv_apply, CohomologyClass.toHom_mk]
  exact homotopyDerivedHomEquiv_map K (J⟦n⟧) (Cocycle.equivHomShift.symm x)

variable [HasExt.{e} (ModuleCat.{max u v} R)]

omit [HasExt.{e} (ModuleCat.{max u v} R)] in
/-- The actual augmentation, after the native single/localization and shift comparisons. -/
def coefficientShiftIso (N : ModuleCat.{max u v} R)
    (J : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (u : ((singleFunctor (ModuleCat.{max u v} R) 0).obj N) ⟶ J) [QuasiIso u] (n : ℤ) :
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj N)⟦n⟧ ≅
      DerivedCategory.Q.obj (J⟦n⟧) :=
  (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max u v} R)) n).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v} R) 0).app N ≪≫
        asIso (DerivedCategory.Q.map u)) ≪≫
    ((DerivedCategory.Q.commShiftIso n).app J).symm

/-- Native module Hom cohomology computes Ext through the original
coefficient augmentation, with its original R-scalar action. -/
def singleHomologyExtLinearEquiv (M N : ModuleCat.{max u v} R)
    (J : CochainComplex (ModuleCat.{max u v} R) ℤ) [J.IsKInjective]
    (u : ((singleFunctor (ModuleCat.{max u v} R) 0).obj N) ⟶ J) [QuasiIso u] (n : ℕ) :
    (moduleComplex R ((singleFunctor (ModuleCat.{max u v} R) 0).obj M) J).homology (n : ℤ) ≃ₗ[R]
      Ext.{e} M N n :=
  (moduleHomologyDerivedLinearEquiv
    ((singleFunctor (ModuleCat.{max u v} R) 0).obj M) J n).trans
      ((Linear.homCongr R
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v} R) 0).app M)
        (coefficientShiftIso N J u n)).symm.trans
          (Ext.homLinearEquiv (R := R) (X := M) (Y := N) (n := n)).symm)

/-- The original coefficient comparison has its explicit forward arrow on every homology class. -/
theorem singleHomologyExtLinearEquiv_hom (M N : ModuleCat.{max u v} R)
    (J : CochainComplex (ModuleCat.{max u v} R) ℤ) [J.IsKInjective]
    (u : ((singleFunctor (ModuleCat.{max u v} R) 0).obj N) ⟶ J) [QuasiIso u] (n : ℕ)
    (x : (moduleComplex R ((singleFunctor (ModuleCat.{max u v} R) 0).obj M) J).homology
      (n : ℤ)) :
    Ext.homLinearEquiv (R := R) (singleHomologyExtLinearEquiv M N J u n x) =
      (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v} R) 0).hom.app M ≫
        moduleHomologyDerivedLinearEquiv
          ((singleFunctor (ModuleCat.{max u v} R) 0).obj M) J n x ≫
            (coefficientShiftIso N J u n).inv := by
  let e₁ := moduleHomologyDerivedLinearEquiv
    ((singleFunctor (ModuleCat.{max u v} R) 0).obj M) J n
  let s := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v} R) 0).app M
  let t := coefficientShiftIso N J u n
  let e₃ : Ext.{e} M N n ≃ₗ[R]
      (((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M) ⟶
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj N)⟦(n : ℤ)⟧) :=
    Ext.homLinearEquiv (R := R)
  exact (cancel_linear_equiv_composite e₁ (Linear.homCongr R s t) e₃ x).trans
    (Linear.homCongr_symm_apply R s t (e₁ x))

/-- The comparison retains the original cocycle-to-Ext arrow, not just an
abstract module equivalence. The only coefficient identification is the actual u. -/
theorem singleHomologyExtLinearEquiv_cocycle (M N : ModuleCat.{max u v} R)
    (J : CochainComplex (ModuleCat.{max u v} R) ℤ) [J.IsKInjective]
    (u : ((singleFunctor (ModuleCat.{max u v} R) 0).obj N) ⟶ J) [QuasiIso u] (n : ℕ)
    (x : Cocycle ((singleFunctor (ModuleCat.{max u v} R) 0).obj M) J n) :
    Ext.homLinearEquiv (R := R)
        (singleHomologyExtLinearEquiv M N J u n
          (moduleCocycleClass ((singleFunctor (ModuleCat.{max u v} R) 0).obj M) J n x)) =
      (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v} R) 0).hom.app M ≫
        DerivedCategory.Q.map (Cocycle.equivHomShift.symm x) ≫
          (coefficientShiftIso N J u n).inv := by
  rw [singleHomologyExtLinearEquiv_hom, moduleHomologyDerivedLinearEquiv_cocycle]

end CochainComplex.HomComplex

universe r a c d t

namespace CochainComplex.HomComplex

variable {R : Type r} {A : Type a} [CommRing R] [CommRing A] (σ : R →+* A)

/-- Original coinduction, followed by the inverse source-single comparison. -/
def coinducedSingleComplexIso (M : ModuleCat.{max r a c} A)
    (I : CochainComplex (ModuleCat.{max r a c} R) ℤ) :
    ((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj
      (moduleComplex A ((singleFunctor (ModuleCat.{max r a c} A) 0).obj M)
        (((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I)) ≅
    moduleComplex R
      ((singleFunctor (ModuleCat.{max r a c} R) 0).obj ((ModuleCat.restrictScalars σ).obj M)) I :=
  coinductionComplexIso.{r, a, max r c} σ _ I ≪≫
    (moduleComplexFunctor R I).mapIso
      (((ModuleCat.restrictScalars σ).mapCochainComplexSingleFunctor 0).app M).symm.op

/-- Scalar restriction compares homology through the original exact-functor
comparison. The A-module on the left already has its intrinsic action. -/
def coinducedSingleHomologyIso (M : ModuleCat.{max r a c} A)
    (I : CochainComplex (ModuleCat.{max r a c} R) ℤ) (n : ℤ) :
    (ModuleCat.restrictScalars σ).obj
      ((moduleComplex A ((singleFunctor (ModuleCat.{max r a c} A) 0).obj M)
        (((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I)).homology n) ≅
    (moduleComplex R
      ((singleFunctor (ModuleCat.{max r a c} R) 0).obj ((ModuleCat.restrictScalars σ).obj M))
        I).homology n :=
  (((moduleComplex A ((singleFunctor (ModuleCat.{max r a c} A) 0).obj M)
      (((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I)).sc n).mapHomologyIso
        (ModuleCat.restrictScalars σ)).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{max r a c} R) (.up ℤ) n).mapIso
      (coinducedSingleComplexIso.{r, a, c} σ M I)

variable [HasDerivedCategory.{d} (ModuleCat.{max r a c} R)]
  [HasExt.{t} (ModuleCat.{max r a c} R)]

/-- The original intrinsic A-homology, restricted to R, computes the
original R-Ext through the actual augmentation and counit comparisons. -/
def coinducedSingleHomologyExtLinearEquiv (M : ModuleCat.{max r a c} A)
    (N : ModuleCat.{max r a c} R) (I : CochainComplex (ModuleCat.{max r a c} R) ℤ)
    [I.IsKInjective]
    (u : ((singleFunctor (ModuleCat.{max r a c} R) 0).obj N) ⟶ I) [QuasiIso u] (n : ℕ) :
    (ModuleCat.restrictScalars σ).obj
      ((moduleComplex A ((singleFunctor (ModuleCat.{max r a c} A) 0).obj M)
        (((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I)).homology
          (n : ℤ)) ≃ₗ[R]
      Ext.{t} ((ModuleCat.restrictScalars σ).obj M) N n :=
  (coinducedSingleHomologyIso.{r, a, c} σ M I n).toLinearEquiv.trans
    (singleHomologyExtLinearEquiv.{r, max a c, d, t}
      ((ModuleCat.restrictScalars σ).obj M) N I u n)

end CochainComplex.HomComplex
