/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteConstantCharts
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Underlying
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureKernels
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.InternalHomPresentationComplex
public import Aglib.Algebra.Category.ModuleCat.Sheaf.FinitePresentationLifting
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantPresentation
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.ZMod

/-!
# Finite local constancy of the original native internal Hom

Finite presentation of the actual constant source value makes Hom preserve
the original locally bijective chart presentation. The whole original slice
comparison then supplies finite constant values for the same native internal
Hom object. No local freeness or projectivity of the source is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe c h r w u

namespace ModuleCat.Presheaf

/-- Hom from a finitely generated module preserves local injectivity, by
one common refinement for its actual finite generating set. -/
theorem locallyInjective_coyoneda_of_finite
    {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    {R : Type r} [Ring R] {F G : Cᵒᵖ ⥤ ModuleCat.{w} R} (η : F ⟶ G)
    [CategoryTheory.Presheaf.IsLocallyInjective J η]
    (M : ModuleCat.{w} R) [Module.Finite R M] :
    CategoryTheory.Presheaf.IsLocallyInjective J
      (Functor.whiskerRight η (coyoneda.obj (op M))) where
  equalizerSieve_mem {U} a b hab := by
    classical
    change M ⟶ F.obj U at a b
    change a ≫ η.app U = b ≫ η.app U at hab
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
    let T : J.Cover U.unop := Finset.univ.inf (fun i : s =>
      ⟨CategoryTheory.Presheaf.equalizerSieve (a i) (b i),
        CategoryTheory.Presheaf.equalizerSieve_mem J η (a i) (b i)
          (ConcreteCategory.congr_hom hab i)⟩)
    refine J.superset_covering ?_ T.2
    intro V f hf
    change a ≫ F.map f.op = b ≫ F.map f.op
    have hi (i : s) : F.map f.op (a i) = F.map f.op (b i) :=
      (show T ≤ (⟨_, CategoryTheory.Presheaf.equalizerSieve_mem J η (a i) (b i)
        (ConcreteCategory.congr_hom hab i)⟩ : J.Cover U.unop)
        from Finset.inf_le (Finset.mem_univ i)) f hf
    let d := (F.map f.op).hom ∘ₗ (a.hom - b.hom)
    have hd : (⊤ : Submodule R M) ≤ LinearMap.ker d := by
      rw [← hs]
      apply Submodule.span_le.mpr
      intro x hx
      change F.map f.op (a x - b x) = 0
      rw [map_sub, hi ⟨x, hx⟩, sub_self]
    ext x
    have hx := hd (Submodule.mem_top (R := R) (x := x))
    change F.map f.op (a x - b x) = 0 at hx
    rw [map_sub] at hx
    exact sub_eq_zero.mp hx

/-- The original additive Hom functor preserves local surjectivity of a
locally bijective presentation when the source is finitely presented. -/
theorem locallySurjective_preadditiveCoyoneda_of_finitePresentation
    {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    {R : Type r} [Ring R] {F G : Cᵒᵖ ⥤ ModuleCat.{w} R} (η : F ⟶ G)
    [CategoryTheory.Presheaf.IsLocallySurjective J η]
    [CategoryTheory.Presheaf.IsLocallyInjective J η]
    (M : ModuleCat.{w} R) [Module.FinitePresentation R M] :
    CategoryTheory.Presheaf.IsLocallySurjective J
      (Functor.whiskerRight η (preadditiveCoyoneda.obj (op M))) := by
  apply (CategoryTheory.Presheaf.isLocallySurjective_iff_whisker_forget J _).mpr
  exact locallySurjective_coyoneda_of_finitePresentation J η M

/-- The original additive Hom functor preserves local injectivity when
its source module is finitely generated. -/
theorem locallyInjective_preadditiveCoyoneda_of_finite
    {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    {R : Type r} [Ring R] {F G : Cᵒᵖ ⥤ ModuleCat.{w} R} (η : F ⟶ G)
    [CategoryTheory.Presheaf.IsLocallyInjective J η]
    (M : ModuleCat.{w} R) [Module.Finite R M] :
    CategoryTheory.Presheaf.IsLocallyInjective J
      (Functor.whiskerRight η (preadditiveCoyoneda.obj (op M))) := by
  apply (CategoryTheory.Presheaf.isLocallyInjective_forget_iff J _).mp
  exact locallyInjective_coyoneda_of_finite J η M

end ModuleCat.Presheaf

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

open Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {X : Scheme.{u}} (R : Type (u + 1)) [CommRing R]

private def constantSliceIsoOfPullback
    (F : ModuleSheaf R X) (U : X.Etale) (M : ModuleCat.{u + 1} R)
    (eF : (moduleInverseImage R U.hom).obj F ≅
      (constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) :
    (constantSheaf (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)).obj M ≅
      (X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} R) U).obj F := by
  let E := moduleEtaleSliceSheafEquivalence U.hom R
  let e : X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} R) U ⋙ E.inverse ≅
      moduleInverseImage R U.hom :=
    AlgebraicGeometry.Scheme.EtaleCohomology.moduleEtaleSliceRestrictionIso U.hom R ≪≫
      (Coefficients.moduleValuedInverseImageEtaleIso U.hom R).symm
  exact E.inverse.preimageIso
    (E.inverse.mapIso (ModuleCat.Sheaf.constantOverIso X.smallEtaleTopology U M) ≪≫
      e.app ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) ≪≫
      (moduleInverseImageConstantIso R U.hom).app M ≪≫ eF.symm ≪≫ (e.app F).symm)

private def pullbackConstantIsoOfSlice
    (F : ModuleSheaf R X) (U : X.Etale) (M : ModuleCat.{u + 1} R)
    (eF : (constantSheaf (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)).obj M ≅
      (X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} R) U).obj F) :
    (moduleInverseImage R U.hom).obj F ≅
      (constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M := by
  let E := moduleEtaleSliceSheafEquivalence U.hom R
  let e : X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} R) U ⋙ E.inverse ≅
      moduleInverseImage R U.hom :=
    AlgebraicGeometry.Scheme.EtaleCohomology.moduleEtaleSliceRestrictionIso U.hom R ≪≫
      (Coefficients.moduleValuedInverseImageEtaleIso U.hom R).symm
  exact (e.app F).symm ≪≫ E.inverse.mapIso eF.symm ≪≫
    E.inverse.mapIso (ModuleCat.Sheaf.constantOverIso X.smallEtaleTopology U M) ≪≫
      e.app ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) ≪≫
      (moduleInverseImageConstantIso R U.hom).app M

variable [(forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).Full]

set_option backward.isDefEq.respectTransparency false in
/-- On joint actual constant charts the same native internal Hom is constant
with its original module-Hom value. Finite presentation is used exactly at
the local-surjectivity boundary, not replaced by source local freeness. -/
def nativeInternalHomConstantSliceIso
    (F G : Coefficients.ModuleSheaf X R) (U : X.Etale)
    (M N : ModuleCat.{u + 1} R) [Module.FinitePresentation R M]
    (eF : (constantSheaf (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)).obj M ≅
      (X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} R) U).obj
        ((moduleSheafEquivalence X R).inverse.obj F))
    (eG : (constantSheaf (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)).obj N ≅
      (X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} R) U).obj
        ((moduleSheafEquivalence X R).inverse.obj G)) :
    (constantSheaf (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)).obj
        (ModuleCat.of R (M ⟶ N)) ≅
      (X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} R) U).obj
        ((moduleSheafEquivalence X R).inverse.obj
          (SheafOfModules.InternalHom.sheaf
            (ModuleCat.Sheaf.ConstantRing.commutativeSheaf X.smallEtaleTopology R) F G)) := by
  let J := X.smallEtaleTopology
  let P := J.overPullback (ModuleCat.{u + 1} R) U
  let H := SheafOfModules.InternalHom.sheaf
    (ModuleCat.Sheaf.ConstantRing.commutativeSheaf J R) F G
  let H₀ := (moduleSheafEquivalence X R).inverse.obj H
  let ηF := ModuleCat.Sheaf.constantUnit (J.over U) M ≫ eF.hom.hom
  let ηG := ModuleCat.Sheaf.constantUnit (J.over U) N ≫ eG.hom.hom
  let : IsIso eF.hom.hom := by
    change IsIso ((sheafToPresheaf (J.over U) (ModuleCat.{u + 1} R)).map eF.hom)
    infer_instance
  let : IsIso eG.hom.hom := by
    change IsIso ((sheafToPresheaf (J.over U) (ModuleCat.{u + 1} R)).map eG.hom)
    infer_instance
  let : CategoryTheory.Presheaf.IsLocallySurjective (J.over U) ηF := by
    dsimp only [ηF]
    infer_instance
  let : CategoryTheory.Presheaf.IsLocallyInjective (J.over U) ηF := by
    dsimp only [ηF]
    infer_instance
  let : CategoryTheory.Presheaf.IsLocallySurjective (J.over U) ηG := by
    dsimp only [ηG]
    infer_instance
  let : CategoryTheory.Presheaf.IsLocallyInjective (J.over U) ηG := by
    dsimp only [ηG]
    infer_instance
  let Q := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}
  let K := (Functor.whiskeringRight (Over U)ᵒᵖ
    (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).obj Q
  let eUnder : K.obj (P.obj H₀).obj ≅
      (ModuleCat.Sheaf.ConstantRing.internalHomOverPresheafFunctor J R U F).obj G :=
    (sheafToPresheaf (J.over U) AddCommGrpCat.{u + 1}).mapIso
      ((J.overPullback AddCommGrpCat.{u + 1} U).mapIso
        ((Coefficients.moduleSheafInverseUnderlyingIso X R).app H))
  let eHom := eUnder ≪≫
    (ModuleCat.Sheaf.ConstantRing.presentationPresheafNatIso J R U F M ηF).app G
  let θ := Functor.whiskerRight ηG (preadditiveCoyoneda.obj (op M))
  let : CategoryTheory.Presheaf.IsLocallySurjective (J.over U) θ :=
    ModuleCat.Presheaf.locallySurjective_preadditiveCoyoneda_of_finitePresentation
      (J.over U) ηG M
  let : CategoryTheory.Presheaf.IsLocallyInjective (J.over U) θ :=
    ModuleCat.Presheaf.locallyInjective_preadditiveCoyoneda_of_finite (J.over U) ηG M
  let V := ModuleCat.of R (M ⟶ N)
  let C₀ := (Functor.const (Over U)ᵒᵖ).obj V
  let eConst : K.obj C₀ ≅
      (Functor.const (Over U)ᵒᵖ).obj N ⋙ preadditiveCoyoneda.obj (op M) :=
    Functor.constComp (Over U)ᵒᵖ V Q ≪≫
      (Functor.constComp (Over U)ᵒᵖ N (preadditiveCoyoneda.obj (op M))).symm
  let θA : K.obj C₀ ⟶ K.obj (P.obj H₀).obj := eConst.hom ≫ θ ≫ eHom.inv
  let : CategoryTheory.Presheaf.IsLocallySurjective (J.over U) θA := by
    dsimp only [θA]
    infer_instance
  let : CategoryTheory.Presheaf.IsLocallyInjective (J.over U) θA := by
    dsimp only [θA]
    infer_instance
  let θM : (Functor.const (Over U)ᵒᵖ).obj (ModuleCat.of R (M ⟶ N)) ⟶ (P.obj H₀).obj :=
    K.preimage θA
  have hθ : Functor.whiskerRight θM Q = θA := K.map_preimage θA
  let : CategoryTheory.Presheaf.IsLocallySurjective (J.over U) θM := by
    apply (CategoryTheory.Presheaf.isLocallySurjective_iff_whisker_forget (J.over U) _).mpr
    change CategoryTheory.Presheaf.IsLocallySurjective (J.over U)
      (Functor.whiskerRight (Functor.whiskerRight θM Q)
        (CategoryTheory.forget AddCommGrpCat.{u + 1}))
    rw [hθ]
    infer_instance
  let : CategoryTheory.Presheaf.IsLocallyInjective (J.over U) θM := by
    apply (CategoryTheory.Presheaf.isLocallyInjective_forget_iff (J.over U) _).mp
    change CategoryTheory.Presheaf.IsLocallyInjective (J.over U)
      (Functor.whiskerRight (Functor.whiskerRight θM Q)
        (CategoryTheory.forget AddCommGrpCat.{u + 1}))
    rw [hθ]
    infer_instance
  exact ModuleCat.Sheaf.constantPresentationIso (J.over U)
    (ModuleCat.of R (M ⟶ N)) (P.obj H₀) θM

set_option backward.isDefEq.respectTransparency false in
/-- Over a finite coefficient ring with full additive forgetting, the SAME
native internal Hom of finite locally constant coefficients is finite locally
constant. Finite presentation on actual joint charts supplies the comparison;
no local freeness, curve or cohomological hypothesis is used. -/
theorem isFiniteTypeLocallyConstant_nativeInternalHom [Finite R]
    (F G : Coefficients.ModuleSheaf X R)
    (hF : IsFiniteTypeLocallyConstant ((moduleSheafEquivalence X R).inverse.obj F))
    (hG : IsFiniteTypeLocallyConstant ((moduleSheafEquivalence X R).inverse.obj G)) :
    IsFiniteTypeLocallyConstant ((moduleSheafEquivalence X R).inverse.obj
      (SheafOfModules.InternalHom.sheaf
        (ModuleCat.Sheaf.ConstantRing.commutativeSheaf X.smallEtaleTopology R) F G)) := by
  classical
  let : IsNoetherianRing R := inferInstance
  let F₀ := (moduleSheafEquivalence X R).inverse.obj F
  let G₀ := (moduleSheafEquivalence X R).inverse.obj G
  let H := SheafOfModules.InternalHom.sheaf
    (ModuleCat.Sheaf.ConstantRing.commutativeSheaf X.smallEtaleTopology R) F G
  let H₀ := (moduleSheafEquivalence X R).inverse.obj H
  obtain ⟨t⟩ := hF
  apply isFiniteTypeLocallyConstant_of_etaleCover t.chart t.covers H₀
  intro i
  obtain ⟨s⟩ := isFiniteTypeLocallyConstant_pullback (t.chart i).hom hG
  apply isFiniteTypeLocallyConstant_of_etaleCover s.chart s.covers
    ((moduleInverseImage R (t.chart i).hom).obj H₀)
  intro j
  let f := (t.chart i).hom
  let g := (s.chart j).hom
  let U : X.Etale := Scheme.Etale.mk (g ≫ f)
  let M := t.value i
  let N := s.value j
  let : Module.Finite R M := t.finite_value i
  let : Module.Finite R N := s.finite_value j
  let : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  let : Finite M := Module.finite_of_finite R
  let : Finite N := Module.finite_of_finite R
  let : Finite (M ⟶ N) := Finite.of_injective
    (fun a : M ⟶ N => (a.hom : M → N))
    (fun a b hab => ModuleCat.hom_ext (LinearMap.ext (fun x => congrFun hab x)))
  let V := ModuleCat.of R (M ⟶ N)
  let : Module.Finite R V := Module.Finite.of_finite
  let eF : (moduleInverseImage R U.hom).obj F₀ ≅
      (constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M :=
    (moduleInverseImageComp R f g).app F₀ ≪≫
      (moduleInverseImage R g).mapIso (t.trivialization i) ≪≫
        (moduleInverseImageConstantIso R g).app M
  let eG : (moduleInverseImage R U.hom).obj G₀ ≅
      (constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj N :=
    (moduleInverseImageComp R f g).app G₀ ≪≫ s.trivialization j
  let eSlice := nativeInternalHomConstantSliceIso R F G U M N
    (constantSliceIsoOfPullback R F₀ U M eF) (constantSliceIsoOfPullback R G₀ U N eG)
  let eH := pullbackConstantIsoOfSlice R H₀ U V eSlice
  let e : (moduleInverseImage R g).obj ((moduleInverseImage R f).obj H₀) ≅
      (constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj V :=
    ((moduleInverseImageComp R f g).app H₀).symm ≪≫ eH
  exact (isFiniteTypeLocallyConstant_iff_of_iso e).mpr
    (isFiniteTypeLocallyConstant_constant U.left V)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
