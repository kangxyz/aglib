/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Hom
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Localization.Opposite
public import Mathlib.CategoryTheory.Localization.Preadditive

/-!
# The native Hom cochains as a module-valued complex

The terms and differential are the original HomComplex cochains and linear
differential. Original precomposition is a quasi-isomorphism at a K-injective
target whenever its source map is a quasi-isomorphism. The cohomology proof
retains the actual map on cycles and the original homotopy-to-derived map.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite

universe t u v w

namespace CochainComplex.HomComplex

section Linear

variable (R : Type t) [Ring R] {C : Type u} [Category.{v} C] [Preadditive C]
  [Linear R C]

/-- The original Hom cochains and differential, with their existing R-module structure. -/
def moduleComplex (K L : CochainComplex C ℤ) : CochainComplex (ModuleCat.{v} R) ℤ where
  X n := ModuleCat.of R (Cochain K L n)
  d i j := ModuleCat.ofHom (δ_hom R K L i j)
  shape i j hij := by
    apply ConcreteCategory.hom_ext
    intro x
    exact δ_shape i j hij x
  d_comp_d' i j k hij hjk := by
    apply ConcreteCategory.hom_ext
    intro x
    exact δ_δ i j k x

/-- Forgetting the module structure gives the original native additive Hom complex,
through the identity map on every original cochain. -/
def moduleComplexForgetIso (K L : CochainComplex C ℤ) :
    ((forget₂ (ModuleCat.{v} R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).obj
        (moduleComplex R K L) ≅ HomComplex K L :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    rfl)

/-- Original precomposition, as a linear map on native cochains. -/
def precompLinear {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (J : CochainComplex C ℤ) (n : ℤ) : Cochain L J n →ₗ[R] Cochain K J n where
  toFun x := (Cochain.ofHom f).comp x (zero_add n)
  map_add' x y := Cochain.comp_add _ x y _
  map_smul' r x := Cochain.comp_smul _ r x _

/-- Original postcomposition, as a linear map on native cochains. -/
def postcompLinear (K : CochainComplex C ℤ) {J L : CochainComplex C ℤ}
    (f : J ⟶ L) (n : ℤ) : Cochain K J n →ₗ[R] Cochain K L n where
  toFun x := x.comp (Cochain.ofHom f) (add_zero n)
  map_add' x y := Cochain.add_comp x y _ _
  map_smul' r x := Cochain.smul_comp r x _ _

/-- Precomposition with the actual source chain map on the module-valued Hom complex. -/
def precomp {K L : CochainComplex C ℤ} (f : K ⟶ L) (J : CochainComplex C ℤ) :
    moduleComplex R L J ⟶ moduleComplex R K J where
  f n := ModuleCat.ofHom (precompLinear R f J n)
  comm' i j hij := by
    apply ConcreteCategory.hom_ext
    intro x
    exact δ_ofHom_comp f x j

/-- Postcomposition with the actual coefficient chain map on the module-valued Hom complex. -/
def postcomp (K : CochainComplex C ℤ) {J L : CochainComplex C ℤ} (f : J ⟶ L) :
    moduleComplex R K J ⟶ moduleComplex R K L where
  f n := ModuleCat.ofHom (postcompLinear R K f n)
  comm' i j hij := by
    apply ConcreteCategory.hom_ext
    intro x
    exact δ_comp_ofHom x f j

@[simp]
theorem precomp_f_apply {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (J : CochainComplex C ℤ) (n : ℤ) (x : Cochain L J n) :
    (precomp R f J).f n x = (Cochain.ofHom f).comp x (zero_add n) := rfl

@[simp]
theorem postcomp_f_apply (K : CochainComplex C ℤ) {J L : CochainComplex C ℤ}
    (f : J ⟶ L) (n : ℤ) (x : Cochain K J n) :
    (postcomp R K f).f n x = x.comp (Cochain.ofHom f) (add_zero n) := rfl

@[simp]
theorem precomp_id (K J : CochainComplex C ℤ) : precomp R (𝟙 K) J = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  exact Cochain.id_comp x

theorem precomp_comp {K L M : CochainComplex C ℤ} (f : K ⟶ L) (g : L ⟶ M)
    (J : CochainComplex C ℤ) :
    precomp R (f ≫ g) J = precomp R g J ≫ precomp R f J := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  exact (congrArg (fun z => z.comp x (zero_add n)) (Cochain.ofHom_comp f g)).trans
    (Cochain.comp_assoc_of_first_is_zero_cochain _ _ _ (zero_add n))

@[simp]
theorem precomp_zero (K L J : CochainComplex C ℤ) :
    precomp R (0 : K ⟶ L) J = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  change (Cochain.ofHom (0 : K ⟶ L)).comp x (zero_add n) = 0
  rw [Cochain.ofHom_zero, Cochain.zero_comp]

theorem precomp_add {K L : CochainComplex C ℤ} (f g : K ⟶ L)
    (J : CochainComplex C ℤ) :
    precomp R (f + g) J = precomp R f J + precomp R g J := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  exact (congrArg (fun z => z.comp x (zero_add n)) (Cochain.ofHom_add f g)).trans
    (Cochain.add_comp _ _ _ _)

/-- The fixed-coefficient contravariant Hom functor uses original precomposition. -/
def moduleComplexFunctor (J : CochainComplex C ℤ) :
    (CochainComplex C ℤ)ᵒᵖ ⥤ CochainComplex (ModuleCat.{v} R) ℤ where
  obj K := moduleComplex R K.unop J
  map f := precomp R f.unop J
  map_id K := precomp_id R K.unop J
  map_comp f g := precomp_comp R g.unop f.unop J

instance moduleComplexFunctor_additive (J : CochainComplex C ℤ) :
    (moduleComplexFunctor R J).Additive where
  map_add {X Y f g} := precomp_add R (K := Y.unop) (L := X.unop) f.unop g.unop J

end Linear

section AdditiveCohomology

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Precomposition on the original additive Hom complex. -/
def additivePrecomp {K L : CochainComplex C ℤ} (f : K ⟶ L) (J : CochainComplex C ℤ) :
    HomComplex L J ⟶ HomComplex K J where
  f n := AddCommGrpCat.ofHom
    { toFun := fun x => (Cochain.ofHom f).comp x (zero_add n)
      map_zero' := Cochain.comp_zero _ _
      map_add' := fun x y => Cochain.comp_add _ x y _ }
  comm' i j hij := by
    apply ConcreteCategory.hom_ext
    intro x
    exact δ_ofHom_comp f x j

/-- The induced map on native cocycles is the original cocycle precomposition. -/
def cocyclePrecomp {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (J : CochainComplex C ℤ) (n : ℤ) : Cocycle L J n →+ Cocycle K J n where
  toFun x := x.precomp f
  map_zero' := by
    apply Subtype.ext
    change (Cochain.ofHom f).comp (0 : Cochain L J n) (zero_add n) = 0
    exact Cochain.comp_zero _ (zero_add n)
  map_add' x y := by
    apply Subtype.ext
    change (Cochain.ofHom f).comp (x.1 + y.1) (zero_add n) =
      (Cochain.ofHom f).comp x.1 (zero_add n) + (Cochain.ofHom f).comp y.1 (zero_add n)
    exact Cochain.comp_add _ x.1 y.1 _

/-- Original source precomposition on homotopy classes, transported through
the native cohomology-class equivalences. -/
def cohomologyPrecomp {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (J : CochainComplex C ℤ) (n : ℤ) :
    CohomologyClass L J n →+ CohomologyClass K J n where
  toFun x := (CohomologyClass.homAddEquiv (K := K) (L := J) (n := n)).symm
    ((HomotopyCategory.quotient C (.up ℤ)).map f ≫
      CohomologyClass.homAddEquiv (K := L) (L := J) (n := n) x)
  map_zero' := by simp
  map_add' x y := by simp

@[simp]
theorem cohomologyPrecomp_mk {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (J : CochainComplex C ℤ) (n : ℤ) (x : Cocycle L J n) :
    cohomologyPrecomp f J n (CohomologyClass.mk x) = CohomologyClass.mk (x.precomp f) := by
  apply (CohomologyClass.homAddEquiv (K := K) (L := J) (n := n)).injective
  change (CohomologyClass.homAddEquiv (K := K) (L := J) (n := n))
      ((CohomologyClass.homAddEquiv (K := K) (L := J) (n := n)).symm _) = _
  rw [AddEquiv.apply_symm_apply]
  change (HomotopyCategory.quotient C (.up ℤ)).map f ≫
      (HomotopyCategory.quotient C (.up ℤ)).map (Cocycle.equivHomShift.symm x) =
    (HomotopyCategory.quotient C (.up ℤ)).map (Cocycle.equivHomShift.symm (x.precomp f))
  rw [Cocycle.equivHomShift_symm_precomp, Functor.map_comp]

/-- The actual map of additive Hom complexes induces the specified original
precomposition on cocycles and cohomology classes. -/
def additivePrecompHomologyMapData {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (J : CochainComplex C ℤ) (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (.up ℤ) n).map
        (additivePrecomp f J))
      (leftHomologyData L J n) (leftHomologyData K J n) where
  φK := AddCommGrpCat.ofHom (cocyclePrecomp f J n)
  φH := AddCommGrpCat.ofHom (cohomologyPrecomp f J n)
  commi := by ext x; rfl
  commf' := by
    apply (cancel_mono (leftHomologyData K J n).i).mp
    simp only [Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    erw [show AddCommGrpCat.ofHom (cocyclePrecomp f J n) ≫
        (leftHomologyData K J n).i =
      (leftHomologyData L J n).i ≫ (additivePrecomp f J).f n by ext x; rfl]
    rw [← Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    exact ((additivePrecomp f J).comm _ _).symm
  commπ := by
    ext x
    exact cohomologyPrecomp_mk f J n x

end AdditiveCohomology

section KInjective

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The original cohomology class followed by the native homotopy-to-derived comparison. -/
def cohomologyDerivedEquiv (K J : CochainComplex C ℤ) [J.IsKInjective] (n : ℤ) :
    CohomologyClass K J n ≃+
      (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (J⟦n⟧)) :=
  (CohomologyClass.homAddEquiv (K := K) (L := J) (n := n)).trans
    (homotopyDerivedHomEquiv K (J⟦n⟧))

/-- The comparison retains precomposition by the original localized chain map. -/
theorem cohomologyDerivedEquiv_precomp {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (J : CochainComplex C ℤ) [J.IsKInjective] (n : ℤ) (x : CohomologyClass L J n) :
    cohomologyDerivedEquiv K J n (cohomologyPrecomp f J n x) =
      DerivedCategory.Q.map f ≫ cohomologyDerivedEquiv L J n x := by
  obtain ⟨z, rfl⟩ := x.mk_surjective
  rw [cohomologyPrecomp_mk]
  change homotopyDerivedHomEquiv K (J⟦n⟧)
      ((HomotopyCategory.quotient C (.up ℤ)).map
        (Cocycle.equivHomShift.symm (z.precomp f))) =
    DerivedCategory.Q.map f ≫ homotopyDerivedHomEquiv L (J⟦n⟧)
      ((HomotopyCategory.quotient C (.up ℤ)).map (Cocycle.equivHomShift.symm z))
  rw [homotopyDerivedHomEquiv_map, homotopyDerivedHomEquiv_map,
    Cocycle.equivHomShift_symm_precomp, Functor.map_comp]

/-- An actual quasi-isomorphism induces a bijection on the original Hom
cohomology classes with K-injective coefficient. -/
theorem cohomologyPrecomp_bijective {K L : CochainComplex C ℤ} (f : K ⟶ L)
    [QuasiIso f] (J : CochainComplex C ℤ) [J.IsKInjective] (n : ℤ) :
    Function.Bijective (cohomologyPrecomp f J n) := by
  constructor
  · intro x y h
    apply (cohomologyDerivedEquiv L J n).injective
    apply (cancel_epi (DerivedCategory.Q.map f)).mp
    rw [← cohomologyDerivedEquiv_precomp, ← cohomologyDerivedEquiv_precomp, h]
  · intro z
    obtain ⟨x, hx⟩ := (cohomologyDerivedEquiv L J n).surjective
      (inv (DerivedCategory.Q.map f) ≫ cohomologyDerivedEquiv K J n z)
    refine ⟨x, (cohomologyDerivedEquiv K J n).injective ?_⟩
    rw [cohomologyDerivedEquiv_precomp, hx]
    simp

/-- Original additive Hom precomposition is a quasi-isomorphism at a K-injective target. -/
theorem additivePrecomp_quasiIso {K L : CochainComplex C ℤ} (f : K ⟶ L)
    [QuasiIso f] (J : CochainComplex C ℤ) [J.IsKInjective] :
    QuasiIso (additivePrecomp f J) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let h := additivePrecompHomologyMapData f J n
  let E := AddEquiv.ofBijective (cohomologyPrecomp f J n)
    (cohomologyPrecomp_bijective f J n)
  let e := AddEquiv.toAddCommGrpIso
    (X := AddCommGrpCat.of (CohomologyClass L J n))
    (Y := AddCommGrpCat.of (CohomologyClass K J n)) E
  have : IsIso h.φH := by
    change IsIso e.hom
    infer_instance
  change IsIso (ShortComplex.homologyMap _)
  rw [h.homologyMap_eq]
  infer_instance

end KInjective

section ModuleKInjective

variable (R : Type t) [Ring R] {C : Type u} [Category.{v} C] [Abelian C]
  [Linear R C]

/-- The forgetful identity retains the original precomposition chain map. -/
@[reassoc]
theorem moduleComplexForgetIso_precomp {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (J : CochainComplex C ℤ) :
    ((forget₂ (ModuleCat.{v} R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map
        (precomp R f J) ≫ (moduleComplexForgetIso R K J).hom =
      (moduleComplexForgetIso R L J).hom ≫ additivePrecomp f J := by
  ext n x
  rfl

variable [HasDerivedCategory.{w} C]

/-- Quasi-isomorphism invariance is proved for the actual R-module-valued Hom map.
Forgetting the module structure is used only to reflect its quasi-isomorphism. -/
theorem precomp_quasiIso {K L : CochainComplex C ℤ} (f : K ⟶ L)
    [QuasiIso f] (J : CochainComplex C ℤ) [J.IsKInjective] :
    QuasiIso (precomp R f J) := by
  let U := forget₂ (ModuleCat.{v} R) AddCommGrpCat
  let : QuasiIso (additivePrecomp f J) := additivePrecomp_quasiIso f J
  have hcomp : QuasiIso
      ((U.mapHomologicalComplex (.up ℤ)).map (precomp R f J) ≫
        (moduleComplexForgetIso R K J).hom) := by
    rw [moduleComplexForgetIso_precomp]
    infer_instance
  let : QuasiIso ((U.mapHomologicalComplex (.up ℤ)).map (precomp R f J)) :=
    (quasiIso_iff_comp_right _ _).mp hcomp
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology (precomp R f J) U).mp
    inferInstance

end ModuleKInjective

end CochainComplex.HomComplex
