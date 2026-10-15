/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Stalk.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.Topology.Sheaves.Flasque

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/GodementFirst.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 472]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# The exact first Godement term on arbitrary scheme module sheaves

A concrete product of module skyscrapers has sections given by independent
stalk values at the points of an open. Its restriction maps discard coordinates.
This special product presentation, rather than exactness of arbitrary products
of sheaves, gives an exact functor with flasque values and a natural monic germ map.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

attribute [local instance] Abelian.hasFiniteBiproducts

open CategoryTheory.ExactCategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Godement

/-- The concrete product presheaf of module skyscrapers. -/
abbrev pointProductPresheaf (X : Scheme.{u})
    (N : ∀ x : X, ModuleCat.{u} (X.presheaf.stalk x)) :
    TopCat.Presheaf AddCommGrpCat.{u} (X : TopCat.{u}) where
  obj U := AddCommGrpCat.of (∀ x : X, PLift (x ∈ U.unop) → N x)
  map {U V} i := AddCommGrpCat.ofHom
    { toFun := fun s x hx => s x ⟨i.unop.le hx.down⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

instance instModulePointProductPresheafObj (X : Scheme.{u})
    (N : ∀ x : X, ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) ((pointProductPresheaf X N).obj U) := by
  change Module (X.ringCatSheaf.obj.obj U) (∀ x : X, (pointPresheaf X x (N x)).obj U)
  infer_instance

/-- Coordinatewise restriction is semilinear for the actual structure sheaf. -/
theorem pointProductPresheaf_map_smul (X : Scheme.{u})
    (N : ∀ x : X, ModuleCat.{u} (X.presheaf.stalk x)) {U V : X.Opensᵒᵖ}
    (i : U ⟶ V) (r : Γ(X, U.unop)) (s : (pointProductPresheaf X N).obj U) :
    (pointProductPresheaf X N).map i (r • s) =
      X.presheaf.map i r • (pointProductPresheaf X N).map i s := by
  funext x
  exact pointPresheaf_map_smul X x (N x) i r (s x)

/-- Arbitrary independent point values glue uniquely. -/
theorem pointProductPresheaf_isSheaf (X : Scheme.{u})
    (N : ∀ x : X, ModuleCat.{u} (X.presheaf.stalk x)) :
    (pointProductPresheaf X N).IsSheaf := by
  classical
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro ι U sf hs
  let idx : ∀ x : X, x ∈ iSup U → ι :=
    fun _ hx => Classical.choose (Opens.mem_iSup.mp hx)
  have hi : ∀ (x : X) (hx : x ∈ iSup U), x ∈ U (idx x hx) :=
    fun _ hx => Classical.choose_spec (Opens.mem_iSup.mp hx)
  let s : ∀ x : X, PLift (x ∈ iSup U) → N x :=
    fun x hx => sf (idx x hx.down) x ⟨hi x hx.down⟩
  refine ⟨s, ?_, ?_⟩
  · intro i
    funext x hx
    exact congrFun (congrFun (hs (idx x ((Opens.leSupr U i).le hx.down)) i) x)
      ⟨⟨hi x ((Opens.leSupr U i).le hx.down), hx.down⟩⟩
  · intro t ht
    funext x hx
    exact congrFun (congrFun (ht (idx x hx.down)) x) ⟨hi x hx.down⟩

/-- The actual sheaf product, with its sections retained as a coordinate family. -/
abbrev pointProductObj (X : Scheme.{u})
    (N : ∀ x : X, ModuleCat.{u} (X.presheaf.stalk x)) : X.Modules where
  val := PresheafOfModules.ofPresheaf (R := X.ringCatSheaf.obj) (pointProductPresheaf X N)
    (fun {_ _} i r s => pointProductPresheaf_map_smul X N i r s)
  isSheaf := pointProductPresheaf_isSheaf X N

/-- Projection onto one actual module skyscraper. -/
def pointProductProjection (X : Scheme.{u})
    (N : ∀ x : X, ModuleCat.{u} (X.presheaf.stalk x)) (x : X) :
    pointProductObj X N ⟶ (moduleSkyscraper X x).obj (N x) :=
  ⟨PresheafOfModules.homMk
    { app := fun _ => AddCommGrpCat.ofHom
        { toFun := fun s => s x
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      naturality := by intros; ext s; funext hx; rfl }
    (by intros; rfl)⟩

/-- A family of skyscraper morphisms lifts by its actual section coordinates. -/
def pointProductLift {X : Scheme.{u}}
    (N : ∀ x : X, ModuleCat.{u} (X.presheaf.stalk x)) (M : X.Modules)
    (q : ∀ x : X, M ⟶ (moduleSkyscraper X x).obj (N x)) :
    M ⟶ pointProductObj X N :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun s x => (q x).app U.unop s
          map_zero' := by funext x; exact map_zero ((q x).app U.unop).hom
          map_add' := by intros; funext x; exact map_add ((q x).app U.unop).hom _ _ }
      naturality := by
        intro U V i
        ext s
        funext x
        exact PresheafOfModules.naturality_apply (q x).val i s }
    (by intros U r s; funext x; exact (q x).app_smul r s)⟩

/-- The concrete point product satisfies the categorical product universal property. -/
def pointProductIsLimit (X : Scheme.{u})
    (N : ∀ x : X, ModuleCat.{u} (X.presheaf.stalk x)) :
    IsLimit (Fan.mk (pointProductObj X N) (pointProductProjection X N)) :=
  Fan.IsLimit.mk _ (fun s => pointProductLift N s.pt s.proj)
    (by intros; ext U t; funext hx; rfl)
    (by
      intro s m hm
      ext U t
      funext x hx
      exact congrFun (congrArg (fun f => f.app U t) (hm x)) hx)

/-- Identification with the original categorical product of actual skyscraper sheaves. -/
def pointProductIso (X : Scheme.{u})
    (N : ∀ x : X, ModuleCat.{u} (X.presheaf.stalk x)) :
    pointProductObj X N ≅ ∏ᶜ fun x : X => (moduleSkyscraper X x).obj (N x) :=
  (pointProductIsLimit X N).conePointUniqueUpToIso (productIsProduct _)

@[reassoc (attr := simp)]
theorem pointProductIso_hom_π (X : Scheme.{u})
    (N : ∀ x : X, ModuleCat.{u} (X.presheaf.stalk x)) (x : X) :
    (pointProductIso X N).hom ≫
      Pi.π (fun x : X => (moduleSkyscraper X x).obj (N x)) x =
        pointProductProjection X N x :=
  (pointProductIsLimit X N).conePointUniqueUpToIso_hom_comp
    (productIsProduct _) (Discrete.mk x)

/-- Pointwise maps of actual stalk modules induce maps of the special sheaf products. -/
def pointProductMap {X : Scheme.{u}}
    {N P : ∀ x : X, ModuleCat.{u} (X.presheaf.stalk x)}
    (q : ∀ x : X, N x ⟶ P x) : pointProductObj X N ⟶ pointProductObj X P :=
  ⟨PresheafOfModules.homMk
    { app := fun _ => AddCommGrpCat.ofHom
        { toFun := fun s x hx => q x (s x hx)
          map_zero' := by funext x hx; exact (q x).hom.map_zero
          map_add' := by intros; funext x hx; exact (q x).hom.map_add _ _ }
      naturality := by intros; ext s; funext x hx; rfl }
    (by intros; funext x hx; exact (q x).hom.map_smul _ _)⟩

/-- The first Godement functor on all module sheaves on an arbitrary scheme. -/
def godementFirst (X : Scheme.{u}) : X.Modules ⥤ X.Modules where
  obj M := pointProductObj X (fun x => (moduleStalk X x).obj M)
  map f := pointProductMap (fun x => (moduleStalk X x).map f)
  map_id M := by
    ext U s
    funext x hx
    change ((moduleStalk X x).map (𝟙 M)) (s x hx) = s x hx
    exact ConcreteCategory.congr_hom ((moduleStalk X x).map_id M) (s x hx)
  map_comp f g := by
    ext U s
    funext x hx
    change ((moduleStalk X x).map (f ≫ g)) (s x hx) =
      ((moduleStalk X x).map g) (((moduleStalk X x).map f) (s x hx))
    exact ConcreteCategory.congr_hom ((moduleStalk X x).map_comp f g) (s x hx)

/-- The actual product object underlying the first Godement term. -/
def godementFirstProductIso (X : Scheme.{u}) (M : X.Modules) :
    (godementFirst X).obj M ≅
      ∏ᶜ fun x : X => (moduleSkyscraper X x).obj ((moduleStalk X x).obj M) :=
  pointProductIso X _

instance godementFirst_additive (X : Scheme.{u}) : (godementFirst X).Additive where
  map_add {M N} f g := by
    ext U s
    funext x hx
    change ((moduleStalk X x).map (f + g)) (s x hx) =
      ((moduleStalk X x).map f) (s x hx) + ((moduleStalk X x).map g) (s x hx)
    exact ConcreteCategory.congr_hom ((moduleStalk X x).map_add (f := f) (g := g)) (s x hx)

/-- The original categorical-product version of the Godement functor. -/
def godementFirstProduct (X : Scheme.{u}) : X.Modules ⥤ X.Modules :=
  CategoryTheory.Functor.pi' (fun x => moduleStalk X x ⋙ moduleSkyscraper X x) ⋙
    Pi.functor X

/-- The coordinate presentation is naturally the original product functor. -/
def godementFirstProductNatIso (X : Scheme.{u}) :
    godementFirst X ≅ godementFirstProduct X :=
  NatIso.ofComponents (godementFirstProductIso X) (by
    intro M N f
    apply Pi.hom_ext
    intro x
    change (godementFirst X).map f ≫
        (pointProductIso X (fun x => (moduleStalk X x).obj N)).hom ≫ Pi.π _ x =
      (pointProductIso X (fun x => (moduleStalk X x).obj M)).hom ≫
        CategoryTheory.Limits.Pi.map
          (fun x => (moduleSkyscraper X x).map ((moduleStalk X x).map f)) ≫ Pi.π _ x
    rw [pointProductIso_hom_π, CategoryTheory.Limits.Pi.map_π, ← Category.assoc,
      pointProductIso_hom_π]
    ext U s
    funext hx
    rfl)

/-- The simultaneous actual germ map into the first Godement term. -/
def godementFirstUnit (X : Scheme.{u}) : 𝟭 X.Modules ⟶ godementFirst X where
  app M := pointProductLift _ M
    (fun x => moduleStalkToSkyscraper x M ((moduleStalk X x).obj M) (𝟙 _))
  naturality {M N} f := by
    ext U s
    funext x hx
    change N.presheaf.germ U x hx.down (f.app U s) =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (X := (X : TopCat.{u})) x).map
        f.mapPresheaf (M.presheaf.germ U x hx.down s)
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    rfl

/-- Godement sections are precisely independent actual module-stalk values on the open. -/
theorem godementFirst_sections (X : Scheme.{u}) (M : X.Modules) (U : X.Opens) :
    (Γ((godementFirst X).obj M, U) : Type u) =
      (∀ x : X, PLift (x ∈ U) → M.presheaf.stalk x) := rfl

@[simp]
theorem godementFirst_map_apply {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (U : X.Opens) (s : Γ((godementFirst X).obj M, U)) (x : X) (hx : PLift (x ∈ U)) :
    (((godementFirst X).map f).app U s) x hx = (moduleStalk X x).map f (s x hx) := rfl

/-- The first Godement unit sends a section to its actual germ at each point of the open. -/
@[simp]
theorem godementFirstUnit_apply (X : Scheme.{u}) (M : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) (x : X) (hx : PLift (x ∈ U)) :
    (Scheme.Modules.Hom.app (M := M) ((godementFirstUnit X).app M) U s) x hx =
      M.presheaf.germ U x hx.down s := rfl

@[simp]
theorem godementFirst_restrict_apply (X : Scheme.{u}) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) (s : Γ((godementFirst X).obj M, U))
    (x : X) (hx : PLift (x ∈ V)) :
    (((godementFirst X).obj M).presheaf.map i.op s) x hx = s x ⟨i.le hx.down⟩ := rfl

@[simp]
theorem godementFirst_smul_apply (X : Scheme.{u}) (M : X.Modules) (U : X.Opens)
    (r : Γ(X, U)) (s : Γ((godementFirst X).obj M, U)) (x : X) (hx : PLift (x ∈ U)) :
    (r • s) x hx = X.presheaf.germ U x hx.down r • s x hx := rfl

/-- Every restriction of the special point product is surjective, by zero extension. -/
theorem pointProduct_restriction_surjective (X : Scheme.{u})
    (N : ∀ x : X, ModuleCat.{u} (X.presheaf.stalk x)) {U V : X.Opensᵒᵖ}
    (i : U ⟶ V) : Function.Surjective ((pointProductObj X N).presheaf.map i) := by
  classical
  intro t
  let s : ∀ x : X, PLift (x ∈ U.unop) → N x :=
    fun x _ => if hx : x ∈ V.unop then t x ⟨hx⟩ else 0
  refine ⟨s, ?_⟩
  funext x hx
  change (if hv : x ∈ V.unop then t x ⟨hv⟩ else 0) = t x hx
  simp only [dite_eq_left hx.down]

instance pointProduct_isFlasque (X : Scheme.{u})
    (N : ∀ x : X, ModuleCat.{u} (X.presheaf.stalk x)) :
    TopCat.Presheaf.IsFlasque (pointProductObj X N).presheaf where
  epi i := (AddCommGrpCat.epi_iff_surjective _).mpr
    (pointProduct_restriction_surjective X N i)

instance godementFirst_isFlasque (X : Scheme.{u}) (M : X.Modules) :
    TopCat.Presheaf.IsFlasque ((godementFirst X).obj M).presheaf :=
  pointProduct_isFlasque X _

/-- The natural germ map is injective on every open, including the empty open. -/
theorem godementFirstUnit_sections_injective (X : Scheme.{u}) (M : X.Modules)
    (U : X.Opens) : Function.Injective (((godementFirstUnit X).app M).app U) := by
  intro s t h
  apply TopCat.Presheaf.section_ext ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) U s t
  intro x hx
  exact congrFun (congrFun h x) ⟨hx⟩

instance godementFirstUnit_mono (X : Scheme.{u}) (M : X.Modules) :
    Mono ((godementFirstUnit X).app M) := by
  apply (Scheme.Modules.toPresheaf X).mono_of_mono_map
  change Mono (((godementFirstUnit X).app M).mapPresheaf)
  have : ∀ U : X.Opensᵒᵖ, Mono (((godementFirstUnit X).app M).mapPresheaf.app U) :=
    fun U => (AddCommGrpCat.mono_iff_injective _).mpr
      (godementFirstUnit_sections_injective X M U.unop)
  exact NatTrans.mono_of_mono_app (((godementFirstUnit X).app M).mapPresheaf)

/-- An epi of module sheaves induces a sectionwise surjection on the special Godement terms.
The chosen lifts are independent actual stalk lifts; no sheaf-product exactness is used. -/
theorem godementFirst_map_sections_surjective {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) [Epi f] (U : X.Opens) :
    Function.Surjective (((godementFirst X).map f).app U) := by
  classical
  intro t
  have hpre : ∀ (x : X) (hx : PLift (x ∈ U)),
      ∃ s : M.presheaf.stalk x, (moduleStalk X x).map f s = t x hx := by
    intro x hx
    exact (ModuleCat.epi_iff_surjective _).mp
      (inferInstance : Epi ((moduleStalk X x).map f)) (t x hx)
  choose s hs using hpre
  exact ⟨s, funext fun x => funext fun hx => hs x hx⟩

/-- Evaluation on the actual underlying additive presheaf, with its source category fixed. -/
abbrev additiveSectionEvaluation (X : Scheme.{u}) (U : X.Opensᵒᵖ) :
    TopCat.Presheaf AddCommGrpCat.{u} (X : TopCat.{u}) ⥤ AddCommGrpCat.{u} :=
  (evaluation _ _).obj U

instance additiveSectionEvaluation_additive (X : Scheme.{u}) (U : X.Opensᵒᵖ) :
    (additiveSectionEvaluation X U).Additive where
  map_add := by intros; rfl

instance additiveSectionEvaluation_preservesFiniteLimits (X : Scheme.{u}) (U : X.Opensᵒᵖ) :
    PreservesFiniteLimits (additiveSectionEvaluation X U) := by
  change PreservesFiniteLimits ((evaluation _ AddCommGrpCat.{u}).obj U)
  infer_instance

instance additiveSectionEvaluation_preservesFiniteColimits (X : Scheme.{u}) (U : X.Opensᵒᵖ) :
    PreservesFiniteColimits (additiveSectionEvaluation X U) := by
  change PreservesFiniteColimits ((evaluation _ AddCommGrpCat.{u}).obj U)
  infer_instance

/-- Sectionwise exactness implies sheaf exactness through the faithful additive presheaf functor. -/
theorem exact_of_additive_sections {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hS : ∀ U : X.Opensᵒᵖ, ((S.map (Scheme.Modules.toPresheaf X)).map
      (additiveSectionEvaluation X U)).Exact) : S.Exact := by
  let F := Scheme.Modules.toPresheaf X
  let : F.Additive := by
    change (SheafOfModules.forget.{u} X.ringCatSheaf ⋙
      PresheafOfModules.toPresheaf.{u} X.ringCatSheaf.obj).Additive
    infer_instance
  apply F.reflects_exact_of_faithful S
  rw [ShortComplex.exact_iff_isZero_homology]
  apply (IsZero.iff_id_eq_zero _).mpr
  apply NatTrans.ext
  funext U
  have hz : IsZero (((S.map F).homology).obj U) :=
    ((ShortComplex.exact_iff_isZero_homology _).mp (hS U)).of_iso
      ((S.map F).mapHomologyIso (additiveSectionEvaluation X U)).symm
  exact (IsZero.iff_id_eq_zero _).mp hz

/-- Actual stalk exactness gives exactness on every Godement section module. -/
theorem godementFirst_exact_sections {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hS : S.Exact) (U : X.Opensᵒᵖ) :
    (((S.map (godementFirst X)).map (Scheme.Modules.toPresheaf X)).map
      (additiveSectionEvaluation X U)).Exact := by
  classical
  apply (ShortComplex.ab_exact_iff _).mpr
  intro t ht
  have hpre : ∀ (x : X) (hx : PLift (x ∈ U.unop)),
      ∃ s : S.X₁.presheaf.stalk x, (moduleStalk X x).map S.f s = t x hx := by
    intro x hx
    apply ((S.map (moduleStalk X x)).moduleCat_exact_iff).mp (hS.map _) (t x hx)
    exact congrFun (congrFun ht x) hx
  choose s hs using hpre
  exact ⟨s, funext fun x => funext fun hx => hs x hx⟩

/-- The actual module section evaluation, with source fixed to scheme module sheaves. -/
abbrev moduleSectionEvaluation (X : Scheme.{u}) (U : X.Opens) :
    X.Modules ⥤ ModuleCat.{u} (X.ringCatSheaf.obj.obj (op U)) :=
  SheafOfModules.evaluation X.ringCatSheaf (op U)

instance moduleSectionEvaluation_additive (X : Scheme.{u}) (U : X.Opens) :
    (moduleSectionEvaluation X U).Additive where
  map_add := by intros; rfl

/-- The sectionwise exactness also retains the actual structure-sheaf section module action. -/
theorem godementFirst_exact_moduleSections {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hS : S.Exact) (U : X.Opens) :
    ((S.map (godementFirst X)).map (moduleSectionEvaluation X U)).Exact := by
  let F := forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (op U))) AddCommGrpCat.{u}
  exact F.reflects_exact_of_faithful _ (godementFirst_exact_sections S hS (op U))

/-- The first Godement functor is exact on all module sheaves. -/
theorem godementFirst_map_exact {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hS : S.Exact) : (S.map (godementFirst X)).Exact :=
  exact_of_additive_sections _ (godementFirst_exact_sections S hS)

instance godementFirst_preservesHomology (X : Scheme.{u}) :
    (godementFirst X).PreservesHomology :=
  CategoryTheory.Functor.preservesHomology_of_map_exact _ godementFirst_map_exact

instance godementFirst_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (godementFirst X) :=
  CategoryTheory.Functor.preservesFiniteLimits_of_preservesHomology _

instance godementFirst_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (godementFirst X) :=
  CategoryTheory.Functor.preservesFiniteColimits_of_preservesHomology _

/-- Every original sheaf short exact sequence remains short exact under the first Godement term. -/
theorem godementFirst_shortExact {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) : (S.map (godementFirst X)).ShortExact := hS.map_of_exact _

/-- The actual exact first Godement term in the standard sheaf exact structure. -/
def godementFirstExactFunctor (X : Scheme.{u}) :
    ExactFunctor (sheafExactStructure X) (sheafExactStructure X) where
  toFunctor := godementFirst X
  map_conflation _ hS := godementFirst_shortExact hS

instance godementFirstProduct_additive (X : Scheme.{u}) :
    (godementFirstProduct X).Additive :=
  CategoryTheory.Functor.additive_of_iso (godementFirstProductNatIso X)

/-- Exactness for the original categorical-product Godement functor. -/
theorem godementFirstProduct_map_exact {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hS : S.Exact) : (S.map (godementFirstProduct X)).Exact :=
  ShortComplex.exact_of_iso (S.mapNatIso (godementFirstProductNatIso X))
    (godementFirst_map_exact S hS)

instance godementFirstProduct_preservesHomology (X : Scheme.{u}) :
    (godementFirstProduct X).PreservesHomology :=
  CategoryTheory.Functor.preservesHomology_of_map_exact _ godementFirstProduct_map_exact

instance godementFirstProduct_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (godementFirstProduct X) :=
  CategoryTheory.Functor.preservesFiniteLimits_of_preservesHomology _

instance godementFirstProduct_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (godementFirstProduct X) :=
  CategoryTheory.Functor.preservesFiniteColimits_of_preservesHomology _

/-- Actual short exactness for the categorical product of actual module skyscrapers. -/
theorem godementFirstProduct_shortExact {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) : (S.map (godementFirstProduct X)).ShortExact := hS.map_of_exact _

/-- The exact first Godement functor with objects given by the original categorical product. -/
def godementFirstProductExactFunctor (X : Scheme.{u}) :
    ExactFunctor (sheafExactStructure X) (sheafExactStructure X) where
  toFunctor := godementFirstProduct X
  map_conflation _ hS := godementFirstProduct_shortExact hS

/-- The canonical germ unit into the original product of actual module skyscrapers. -/
def godementFirstProductUnit (X : Scheme.{u}) : 𝟭 X.Modules ⟶ godementFirstProduct X :=
  godementFirstUnit X ≫ (godementFirstProductNatIso X).hom

instance godementFirstProductUnit_mono (X : Scheme.{u}) (M : X.Modules) :
    Mono ((godementFirstProductUnit X).app M) := by
  change Mono ((godementFirstUnit X).app M ≫ (godementFirstProductNatIso X).hom.app M)
  infer_instance

@[reassoc (attr := simp)]
theorem godementFirstProductUnit_π (X : Scheme.{u}) (M : X.Modules) (x : X) :
    (godementFirstProductUnit X).app M ≫
      Pi.π (fun x => (moduleSkyscraper X x).obj ((moduleStalk X x).obj M)) x =
        moduleStalkToSkyscraper x M ((moduleStalk X x).obj M) (𝟙 _) := by
  change (godementFirstUnit X).app M ≫ (pointProductIso X _).hom ≫ Pi.π _ x = _
  rw [pointProductIso_hom_π]
  ext U s
  funext hx
  rfl

/-- The original categorical-product Godement sheaf is flasque on every scheme. -/
instance godementFirstProduct_isFlasque (X : Scheme.{u}) (M : X.Modules) :
    TopCat.Presheaf.IsFlasque ((godementFirstProduct X).obj M).presheaf where
  epi {U V} i := (AddCommGrpCat.epi_iff_surjective _).mpr (by
    intro t
    let e := (godementFirstProductNatIso X).app M
    obtain ⟨s, hs⟩ := pointProduct_restriction_surjective X
      (fun x => (moduleStalk X x).obj M) i (e.inv.app V.unop t)
    refine ⟨e.hom.app U.unop s, ?_⟩
    calc
      ((godementFirstProduct X).obj M).presheaf.map i (e.hom.app U.unop s) =
          e.hom.app V.unop (((godementFirst X).obj M).presheaf.map i s) :=
        (PresheafOfModules.naturality_apply e.hom.val i s).symm
      _ = e.hom.app V.unop (e.inv.app V.unop t) :=
        congrArg (fun z => e.hom.app V.unop z) hs
      _ = t := congrArg (fun f : (godementFirstProduct X).obj M ⟶
        (godementFirstProduct X).obj M => f.app V.unop t) e.inv_hom_id)

end AlgebraicGeometry.Scheme.Modules.Godement
