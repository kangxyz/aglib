/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Adjunction.Exact
public import Aglib.AlgebraicGeometry.Modules.InternalHom.HomSection
public import Aglib.AlgebraicGeometry.Modules.Invertible.Affine
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorFaithful
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Tensor.Exact
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.StructureQuotient
public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.ClosedImmersion
public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Symmetric
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# The original Cartier section and positive extension adapters

The dual-ideal section is the actual transpose of the original ideal inclusion.
Its tensor transformation vanishes on every actual closed pushforward, by the
original pullback unit, projection formula and evaluation. Tensoring by a line
preserves regularity of this transformation.

The separate categorical adapter sends the positive extension class of a given
short exact row through the original derived adjunction. Its isomorphism theorem
uses concentration to an arbitrary heart object, not a prescribed quotient.
These are lower producers for global Cartier adjunction. This module does not
yet construct the global coefficient row or prove global right-adjoint
concentration, and does not assert a global Cartier purity theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory

private theorem sectionExtension_hom_eq_zero
    {D : Type*} [Category* D] [HasZeroMorphisms D]
    (K : D ⥤ D) (τ : 𝟭 D ⟶ K) (M T : D)
    (hT : τ.app T = 0) [Mono (τ.app (K.obj M))] (f : T ⟶ K.obj M) : f = 0 := by
  apply (cancel_mono (τ.app (K.obj M))).mp
  have h := τ.naturality f
  change f ≫ τ.app (K.obj M) = τ.app T ≫ K.map f at h
  exact h.trans (by rw [hT, zero_comp, zero_comp])

namespace CategoryTheory

section SectionExtension

variable {D : Type*} [Category* D] [Abelian D] [HasExt D]
  (K : D ⥤ D) (τ : 𝟭 D ⟶ K) (M T : D)

/-- Exact-functor naturality moves the original section to a source where it is zero. -/
public theorem sectionExtension_ext_post_eq_zero
    [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    (hT : τ.app T = 0) (n : ℕ) (x : Ext T M n) :
    x.comp (Ext.mk₀ (τ.app M)) (add_zero n) = 0 := by
  have h := Ext.mapExactFunctor_comp_mk₀_natTransApp x τ
  rw [Ext.id_mapExactFunctor, hT, Ext.mk₀_zero, Ext.zero_comp] at h
  exact h

variable (Q : D) (g : K.obj M ⟶ Q) (hg : τ.app M ≫ g = 0)
  (hS : (ShortComplex.mk (τ.app M) g hg).ShortExact)

/-- Positive composition with the actual extension class of the specified row. -/
public def sectionExtensionHomExtMap : (T ⟶ Q) →+ Ext T M 1 where
  toFun f := (Ext.mk₀ f).comp hS.extClass (zero_add 1)
  map_zero' := by simp
  map_add' f g := by rw [Ext.mk₀_add, Ext.add_comp]

/-- An exact tensor section killed on the source gives the original degree-one
Hom--Ext bijection. Regularity is required on the twisted middle coefficient. -/
public theorem sectionExtensionHomExtMap_bijective
    [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    (hT : τ.app T = 0) [Mono (τ.app (K.obj M))] :
    Function.Bijective (sectionExtensionHomExtMap K τ M T Q g hg hS) := by
  constructor
  · intro f f' h
    have hz : sectionExtensionHomExtMap K τ M T Q g hg hS (f - f') = 0 := by
      rw [map_sub, h, sub_self]
    obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃ T hS (Ext.mk₀ (f - f')) rfl hz
    have hz0 : z = 0 := by
      rw [← Ext.mk₀_addEquiv₀_apply z]
      rw [sectionExtension_hom_eq_zero K τ M T hT (Ext.addEquiv₀ z), Ext.mk₀_zero]
    rw [hz0, Ext.zero_comp] at hz
    exact sub_eq_zero.mp ((Ext.mk₀_eq_zero_iff (f - f')).mp hz.symm)
  · intro x
    obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ T hS x
      (sectionExtension_ext_post_eq_zero K τ M T hT 1 x) rfl
    exact ⟨Ext.addEquiv₀ z, by
      simpa only [sectionExtensionHomExtMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
        Ext.mk₀_addEquiv₀_apply] using hz⟩

end SectionExtension

namespace Adjunction

section SectionMate

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
  [HasExt D] [EnoughInjectives D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
  [F.PreservesMonomorphisms]
  (adj : F ⊣ G) (K : D ⥤ D) (τ : 𝟭 D ⟶ K) (M : D) (Q : C)
  (g : K.obj M ⟶ F.obj Q) (hg : τ.app M ≫ g = 0)
  (hS : (ShortComplex.mk (τ.app M) g hg).ShortExact)

/-- The actual derived adjoint of the original positive tensor-section row. -/
public def sectionExtensionMate :
    (DerivedCategory.singleFunctor C 0).obj Q ⟶
      (DerivedCategory.Plus.ι.obj
        (G.rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor D 0).obj M)))⟦(1 : ℤ)⟧ :=
  adj.singleDerivedHomEquivOfInjectiveResolution Q (injectiveResolution M) 1 hS.extClass.hom

/-- The original positive mate is invertible once its target lies in the heart.
The heart object is arbitrary; its identification with the quotient is a conclusion. -/
public theorem sectionExtensionMate_isIso
    [F.Full] [F.Faithful]
    [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    (hkill : ∀ T : C, τ.app (F.obj T) = 0)
    [Mono (τ.app (K.obj M))] (H : C)
    (e : (DerivedCategory.Plus.ι.obj
      (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor D 0).obj M)))⟦(1 : ℤ)⟧ ≅
        (DerivedCategory.singleFunctor C 0).obj H) :
    IsIso (sectionExtensionMate adj K τ M Q g hg hS) := by
  let η := sectionExtensionMate adj K τ M Q g hg hS
  let S := DerivedCategory.singleFunctor C 0
  let u : Q ⟶ H := S.preimage (η ≫ e.hom)
  have hu : S.map u = η ≫ e.hom := S.map_preimage _
  have hbij (T : C) : Function.Bijective (fun f : T ⟶ Q => S.map f ≫ η) := by
    let eF : (T ⟶ Q) ≃ (F.obj T ⟶ F.obj Q) :=
      (Functor.FullyFaithful.ofFullyFaithful F).homEquiv
    let E₁ := AddEquiv.ofBijective
      (sectionExtensionHomExtMap K τ M (F.obj T) (F.obj Q) g hg hS)
      (sectionExtensionHomExtMap_bijective K τ M (F.obj T) (F.obj Q) g hg hS (hkill T))
    let E₂ := adj.singleDerivedHomEquivOfInjectiveResolution T (injectiveResolution M) 1
    let E := eF.trans (E₁.toEquiv.trans (Ext.homEquiv.trans E₂.toEquiv))
    have hE (f : T ⟶ Q) : E f = S.map f ≫ η := by
      change adj.singleDerivedHomEquivOfInjectiveResolution T (injectiveResolution M) 1
        (((Ext.mk₀ (F.map f)).comp hS.extClass (zero_add 1)).hom) = _
      rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp]
      change adj.singleDerivedHomEquivOfInjectiveResolution T (injectiveResolution M) 1
        ((DerivedCategory.singleFunctor D 0).map (F.map f) ≫ hS.extClass.hom) =
          (DerivedCategory.singleFunctor C 0).map f ≫
            adj.singleDerivedHomEquivOfInjectiveResolution Q (injectiveResolution M) 1
              hS.extClass.hom
      exact adj.singleDerivedHomEquivOfInjectiveResolution_naturality_left
        T (injectiveResolution M) 1 f hS.extClass.hom
    have heq : (fun f : T ⟶ Q => S.map f ≫ η) = E := by
      funext f
      exact (hE f).symm
    rw [heq]
    exact E.bijective
  have huIso : IsIso u := by
    apply isIso_of_yoneda_map_bijective u
    intro T
    constructor
    · intro f f' h
      apply (hbij T).1
      apply (cancel_mono e.hom).mp
      have h' := congrArg S.map h
      simpa only [Functor.map_comp, hu, Category.assoc] using h'
    · intro f
      obtain ⟨g', hg'⟩ := (hbij T).2 (S.map f ≫ e.inv)
      change S.map g' ≫ η = S.map f ≫ e.inv at hg'
      refine ⟨g', S.map_injective ?_⟩
      rw [Functor.map_comp, hu, ← Category.assoc, hg']
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let := huIso
  have : IsIso (η ≫ e.hom) := by rw [← hu]; infer_instance
  exact IsIso.of_isIso_comp_right η e.hom

/-- The actual adjunction inverse of the chosen mate is the positive original row class. -/
public theorem sectionExtensionMate_counit :
    (adj.singleDerivedHomEquivOfInjectiveResolution Q (injectiveResolution M) 1).symm
      (sectionExtensionMate adj K τ M Q g hg hS) = hS.extClass.hom :=
  (adj.singleDerivedHomEquivOfInjectiveResolution Q (injectiveResolution M) 1).symm_apply_apply _

/-- A map with this original counit is the same positive mate. -/
public theorem sectionExtensionMate_unique
    (η : (DerivedCategory.singleFunctor C 0).obj Q ⟶
      (DerivedCategory.Plus.ι.obj
        (G.rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor D 0).obj M)))⟦(1 : ℤ)⟧)
    (hη : (adj.singleDerivedHomEquivOfInjectiveResolution Q (injectiveResolution M) 1).symm η =
      hS.extClass.hom) : η = sectionExtensionMate adj K τ M Q g hg hS := by
  apply (adj.singleDerivedHomEquivOfInjectiveResolution Q (injectiveResolution M) 1).symm.injective
  exact hη.trans (sectionExtensionMate_counit adj K τ M Q g hg hS).symm

end SectionMate

end Adjunction
end CategoryTheory

private theorem sectionTensorWhisker
    {C : Type*} [Category* C] [MonoidalCategory C]
    {L : C} (s : 𝟙_ C ⟶ L) (M N : C) :
    ((λ_ (M ⊗ N)).inv ≫ s ▷ (M ⊗ N)) ≫ (α_ L M N).inv =
      ((λ_ M).inv ≫ s ▷ M) ▷ N := by
  calc
    _ = (λ_ (M ⊗ N)).inv ≫ (α_ (𝟙_ C) M N).inv ≫ s ▷ M ▷ N := by
      rw [Category.assoc, associator_inv_naturality_left]
    _ = (λ_ M).inv ▷ N ≫ s ▷ M ▷ N := by
      rw [leftUnitor_tensor_inv]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := (comp_whiskerRight _ _ _).symm

private theorem sectionTensorTwistMono
    {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]
    (L M : C) (τ : 𝟭 C ⟶ CategoryTheory.MonoidalCategory.tensorLeft L)
    (htensor : ∀ A B : C, τ.app (A ⊗ B) ≫ (α_ L A B).inv = τ.app A ▷ B)
    [(CategoryTheory.MonoidalCategory.tensorRight L).PreservesMonomorphisms]
    [Mono (τ.app M)] : Mono (τ.app (L ⊗ M)) := by
  let K := CategoryTheory.MonoidalCategory.tensorLeft L
  have hmap : Mono (τ.app M ▷ L) :=
    inferInstanceAs (Mono ((CategoryTheory.MonoidalCategory.tensorRight L).map (τ.app M)))
  let := hmap
  have hright : Mono (τ.app (M ⊗ L)) := by
    constructor
    intro Z f g h
    apply (cancel_mono (τ.app M ▷ L)).mp
    rw [← htensor M L]
    simpa only [Category.assoc] using
      congrArg (fun k : Z ⟶ L ⊗ (M ⊗ L) => k ≫ (α_ L M L).inv) h
  let := hright
  constructor
  intro Z f g h
  apply (cancel_mono (β_ L M).hom).mp
  apply (cancel_mono (τ.app (M ⊗ L))).mp
  have hn := τ.naturality (β_ L M).hom
  change (β_ L M).hom ≫ τ.app (M ⊗ L) = τ.app (L ⊗ M) ≫ K.map (β_ L M).hom at hn
  calc
    (f ≫ (β_ L M).hom) ≫ τ.app (M ⊗ L) =
        (f ≫ τ.app (L ⊗ M)) ≫ K.map (β_ L M).hom := by
      rw [Category.assoc, hn, ← Category.assoc]
    _ = (g ≫ τ.app (L ⊗ M)) ≫ K.map (β_ L M).hom := by rw [h]
    _ = (g ≫ (β_ L M).hom) ≫ τ.app (M ⊗ L) := by
      rw [Category.assoc, ← hn, ← Category.assoc]

private theorem sectionEvaluationCancel
    {C : Type*} [Category* C] {A B D E : C}
    (l : A ≅ B) (f : A ⟶ D) (g : D ⟶ E) (i : B ⟶ E)
    (h : f ≫ g = l.hom ≫ i) : (l.inv ≫ f) ≫ g = i := by
  rw [Category.assoc, h, Iso.inv_hom_id_assoc]

private theorem sectionPullbackIdealZero
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] (adj : F ⊣ G)
    {I O : C} {P : D} (φ : I ⟶ O) (s : O ⟶ G.obj P) (e : F.obj O ≅ P)
    (he : adj.homEquiv O P e.hom = s) (hzero : φ ≫ s = 0) : F.map φ = 0 := by
  apply (cancel_mono e.hom).mp
  rw [zero_comp]
  apply (adj.homEquiv I P).injective
  rw [Adjunction.homEquiv_naturality_left, he, Adjunction.homAddEquiv_zero]
  exact hzero

private theorem sectionTensorKilled
    {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]
    [HasZeroMorphisms C] (I L P : C)
    (τ : 𝟭 C ⟶ CategoryTheory.MonoidalCategory.tensorLeft L)
    (htensor : ∀ A B : C, τ.app (A ⊗ B) ≫ (α_ L A B).inv = τ.app A ▷ B)
    (e : L ⊗ I ≅ 𝟙_ C) (i : I ⟶ 𝟙_ C) (hev : τ.app I ≫ e.hom = i)
    (hi : i ▷ P = 0)
    (hfaithful : ∀ {A B : C} (f : A ⟶ B), I ◁ f = 0 → f = 0) : τ.app P = 0 := by
  let K := CategoryTheory.MonoidalCategory.tensorLeft L
  let E : L ⊗ (I ⊗ P) ≅ (𝟙_ C) ⊗ P :=
    (α_ L I P).symm ≪≫ (CategoryTheory.MonoidalCategory.tensorRight P).mapIso e
  have hleft : τ.app (I ⊗ P) = 0 := by
    apply (cancel_mono E.hom).mp
    rw [zero_comp]
    change τ.app (I ⊗ P) ≫ (α_ L I P).inv ≫ e.hom ▷ P = 0
    rw [← Category.assoc, htensor I P, ← CategoryTheory.MonoidalCategory.comp_whiskerRight,
      hev]
    exact hi
  have hright : τ.app (P ⊗ I) = 0 := by
    apply (cancel_mono (K.map (β_ P I).hom)).mp
    rw [zero_comp, ← τ.naturality (β_ P I).hom, hleft, comp_zero]
  have hwhisker : τ.app P ▷ I = 0 := by rw [← htensor P I, hright, zero_comp]
  apply hfaithful (τ.app P)
  apply (cancel_mono (β_ I (L ⊗ P)).hom).mp
  rw [zero_comp]
  calc
    _ = (β_ I P).hom ≫ τ.app P ▷ I :=
      CategoryTheory.BraidedCategory.braiding_naturality_right I (τ.app P)
    _ = 0 := by rw [hwhisker, comp_zero]

namespace AlgebraicGeometry.Scheme.Modules

universe u

open AlgebraicGeometry CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules.Invertible

/-- The original tensor-unit inverse followed by the supplied section coefficient map. -/
public def positiveCartierTensorSection (X : Scheme.{u}) (L : X.Modules)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ L) :
    𝟭 X.Modules ⟶ moduleTensorLeftFunctor X L :=
  (SheafOfModulesOfCommRing.tensorLeftUnitIso X.sheaf).inv ≫ moduleTensorCoefficientMap X s

/-- Every component retains the original tensor-unit inverse and original coefficient map. -/
public theorem positiveCartierTensorSection_app (X : Scheme.{u}) (L M : X.Modules)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ L) :
    (positiveCartierTensorSection X L s).app M =
      (tensorSheafLeftUnit X M).inv ≫ (moduleTensorCoefficientMap X s).app M := rfl

/-- The actual associator compares insertion of the section before a tensor product. -/
public theorem positiveCartierTensorSection_tensor (X : Scheme.{u}) (L M N : X.Modules)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ L) :
    (positiveCartierTensorSection X L s).app (M ⊗ N) ≫ (α_ L M N).inv =
      (positiveCartierTensorSection X L s).app M ▷ N :=
  sectionTensorWhisker (C := X.Modules) s M N

/-- Tensoring by an actual line bundle preserves regularity of the original section. -/
public theorem positiveCartierTensorSection_twist_mono (X : Scheme.{u})
    (L : LineBundle X) (s : SheafOfModules.unit X.ringCatSheaf ⟶ L.val)
    (M : X.Modules) [Mono ((positiveCartierTensorSection X L.val s).app M)] :
    Mono ((positiveCartierTensorSection X L.val s).app (L.val ⊗ M)) := by
  let τ : 𝟭 X.Modules ⟶ tensorLeft (C := X.Modules) L.val :=
    positiveCartierTensorSection X L.val s
  let : Mono (τ.app M) :=
    inferInstanceAs (Mono ((positiveCartierTensorSection X L.val s).app M))
  let : IsFiniteLocallyFree X L.val := isFiniteLocallyFree_of_isLocallyRankOne L.property
  let : (moduleTensorRightFunctor X L.val).Additive :=
    moduleTensorRightFunctor_additive X L.val
  let : (moduleTensorRightFunctor X L.val).PreservesHomology :=
    moduleTensorRight_preservesHomology L.val
  let : PreservesFiniteLimits (moduleTensorRightFunctor X L.val) :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  let : (tensorRight (C := X.Modules) L.val).PreservesMonomorphisms :=
    inferInstanceAs (moduleTensorRightFunctor X L.val).PreservesMonomorphisms
  exact sectionTensorTwistMono (C := X.Modules) L.val M τ
    (fun A B => positiveCartierTensorSection_tensor X L.val A B s)

/-- The section of the actual dual ideal obtained by transposing its original inclusion. -/
public def cartierDualIdealSection {D X : Scheme.{u}} (i : D ⟶ X) :
    SheafOfModules.unit X.ringCatSheaf ⟶ dualSheaf X (idealModule i) :=
  InternalHom.transpose X (idealInclusion i)

/-- The canonical tensor transformation attached to the original ideal inclusion. -/
public def cartierTensorSection {D X : Scheme.{u}} (i : D ⟶ X) :
    𝟭 X.Modules ⟶ moduleTensorLeftFunctor X (dualSheaf X (idealModule i)) :=
  positiveCartierTensorSection X (dualSheaf X (idealModule i)) (cartierDualIdealSection i)

/-- The original evaluation recovers the original ideal inclusion, with positive sign. -/
public theorem cartierTensorSection_evaluation {D X : Scheme.{u}} (i : D ⟶ X)
    (hI : IsLocallyRankOne X (idealModule i)) :
    (cartierTensorSection i).app (idealModule i) ≫
      (dualEvaluationIso X ⟨idealModule i, hI⟩).hom = idealInclusion i :=
  sectionEvaluationCancel (C := X.Modules) (tensorSheafLeftUnit X (idealModule i))
    (tensorSheafMap X (InternalHom.transpose X (idealInclusion i)) (𝟙 (idealModule i)))
    (dualEvaluationIso X ⟨idealModule i, hI⟩).hom (idealInclusion i)
    (InternalHom.transpose_dualEvaluation X ⟨idealModule i, hI⟩ (idealInclusion i))

/-- The original ideal inclusion pulls back to zero, by the original structure-map unit. -/
public theorem pullback_idealInclusion_eq_zero {D X : Scheme.{u}} (i : D ⟶ X) :
    (pullback i).map (idealInclusion i) = 0 :=
  sectionPullbackIdealZero (C := X.Modules) (D := D.Modules)
    (pullbackPushforwardAdjunction i) (idealInclusion i) (structureModuleMap i)
    (pullbackUnitIso i) (pullbackUnitIso_homEquiv i) (idealInclusion_structureMap i)

/-- The original ideal coefficient map vanishes on every actual closed pushforward. -/
public theorem idealInclusion_tensor_pushforward_eq_zero {D X : Scheme.{u}} (i : D ⟶ X)
    [IsClosedImmersion i] (T : D.Modules) :
    (moduleTensorCoefficientMap X (idealInclusion i)).app ((pushforward i).obj T) = 0 := by
  apply (cancel_mono
    (closedImmersionProjectionFormulaIso i (SheafOfModules.unit X.ringCatSheaf) T).hom).mp
  rw [zero_comp, closedImmersionProjectionFormulaIso_naturality_left,
    pullback_idealInclusion_eq_zero]
  change _ ≫ (pushforward i).map
    ((moduleTensorRightFunctor D T).map
      (0 : (pullback i).obj (idealModule i) ⟶
        (pullback i).obj (SheafOfModules.unit X.ringCatSheaf))) = 0
  rw [Functor.map_zero, Functor.map_zero]
  exact comp_zero

/-- The canonical Cartier tensor section kills every actual closed pushforward.
No freeness or quasicoherence assumption is made on the pushed coefficient. -/
public theorem cartierTensorSection_pushforward_eq_zero {D X : Scheme.{u}} (i : D ⟶ X)
    [IsClosedImmersion i] (hI : IsLocallyRankOne X (idealModule i)) (T : D.Modules) :
    (cartierTensorSection i).app ((pushforward i).obj T) = 0 :=
  sectionTensorKilled (C := X.Modules) (idealModule i) (dualSheaf X (idealModule i))
    ((pushforward i).obj T) (cartierTensorSection i)
    (fun A B => positiveCartierTensorSection_tensor X (dualSheaf X (idealModule i)) A B
      (cartierDualIdealSection i))
    (dualEvaluationIso X ⟨idealModule i, hI⟩) (idealInclusion i)
    (cartierTensorSection_evaluation i hI) (idealInclusion_tensor_pushforward_eq_zero i T)
    (fun f h => tensorSheafMap_lineBundle_detects_zero X ⟨idealModule i, hI⟩ f h)

/-- Actual Cartier section regularity survives the actual dual-ideal twist. -/
public theorem cartierTensorSection_twist_mono {D X : Scheme.{u}} (i : D ⟶ X)
    (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules)
    [Mono ((cartierTensorSection i).app M)] :
    Mono ((cartierTensorSection i).app
      ((moduleTensorLeftFunctor X (dualSheaf X (idealModule i))).obj M)) := by
  let L := dualLineBundle X ⟨idealModule i, hI⟩
  let : Mono ((positiveCartierTensorSection X L.val (cartierDualIdealSection i)).app M) :=
    inferInstanceAs (Mono ((cartierTensorSection i).app M))
  exact positiveCartierTensorSection_twist_mono X L
    (cartierDualIdealSection i) M

/-- The original Cartier section induces zero on Ext from every actual closed pushforward. -/
public theorem cartierTensorSection_ext_post_eq_zero {D X : Scheme.{u}}
    [HasExt X.Modules] (i : D ⟶ X) [IsClosedImmersion i]
    (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules) (T : D.Modules)
    (n : ℕ) (x : Ext ((pushforward i).obj T) M n) :
    x.comp (Ext.mk₀ ((cartierTensorSection i).app M)) (add_zero n) = 0 := by
  let L : LineBundle X := dualLineBundle X ⟨idealModule i, hI⟩
  let K := moduleTensorLeftFunctor X L.val
  let : IsFiniteLocallyFree X L.val := isFiniteLocallyFree_of_isLocallyRankOne L.property
  let : K.Additive := moduleTensorLeftFunctor_additive X L.val
  let : K.PreservesHomology := moduleTensorLeft_preservesHomology L.val
  let : PreservesFiniteLimits K := Functor.preservesFiniteLimits_of_preservesHomology K
  let : PreservesFiniteColimits K := Functor.preservesFiniteColimits_of_preservesHomology K
  exact sectionExtension_ext_post_eq_zero K (cartierTensorSection i) M
    ((pushforward i).obj T) (cartierTensorSection_pushforward_eq_zero i hI T) n x

end AlgebraicGeometry.Scheme.Modules
