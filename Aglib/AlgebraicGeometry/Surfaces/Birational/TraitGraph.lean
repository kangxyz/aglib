/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.GraphClosure.Comparison
public import Aglib.AlgebraicGeometry.Morphisms.Flat.DVRBaseChange
public import Aglib.AlgebraicGeometry.Morphisms.Flat.DedekindBase
public import Aglib.AlgebraicGeometry.Morphisms.Flat.GenericFiberCriteria
public import Aglib.AlgebraicGeometry.SchemeTheoreticImage.Integral
public import Aglib.AlgebraicGeometry.FunctionField.DedekindGenericFiberIntegral
public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The actual common graph model over a trait

The native schematic closure of the graph of a specified generic-fibre
isomorphism gives a common proper model with the original projections.
The generic comparisons and compatible section lifts use the literal
fraction-field base change. Integrality, Noetherianity and flatness are
proved for this graph model; regularity is not asserted.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry.Scheme.LocalRing.GenericFiber (baseMap)

universe u

namespace AlgebraicGeometry.Scheme.TraitGraph

variable (R F : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F] [IsFractionRing R F]
  {X Y : Scheme.{u}} (f : X ⟶ Spec (.of R)) (g : Y ⟶ Spec (.of R))

/-- The image of the original literal generic-fibre projection as an open. -/
def sourceOpen : X.Opens := (pullback.fst f (baseMap R F)).opensRange

/-- The original generic fibre identified with its actual open image. -/
def sourceOpenIso : pullback f (baseMap R F) ≅ (sourceOpen R F f).toScheme :=
  (pullback.fst f (baseMap R F)).isoOpensRange

/-- The original structural map of the generic open to the supplied fraction field. -/
def sourceOpenBase : (sourceOpen R F f).toScheme ⟶ Spec (.of F) :=
  (sourceOpenIso R F f).inv ≫ pullback.snd f (baseMap R F)

/-- The chosen open is the actual pullback along the supplied fraction map. -/
lemma sourceSquare : IsPullback (sourceOpen R F f).ι (sourceOpenBase R F f)
    f (baseMap R F) := by
  refine (IsPullback.of_hasPullback f (baseMap R F)).of_iso
    (sourceOpenIso R F f) (.refl _) (.refl _) (.refl _) ?_ ?_ ?_ ?_
  · simp [sourceOpenIso, sourceOpen]
  · simp [sourceOpenBase]
  · simp
  · simp

lemma sourceSquare_isoPullback_hom :
    (sourceSquare R F f).isoPullback.hom = (sourceOpenIso R F f).inv := by
  apply pullback.hom_ext (f := f) (g := baseMap R F)
  · simp [sourceOpenIso, sourceOpen]
  · simp [sourceOpenBase]

variable (e : (Over.pullback (baseMap R F)).obj (Over.mk f) ≅
  (Over.pullback (baseMap R F)).obj (Over.mk g))

/-- The specified generic isomorphism regarded as a map from the original
source open into the original target scheme. -/
def openToTarget : (sourceOpen R F f).toScheme ⟶ Y :=
  (sourceOpenIso R F f).inv ≫ e.hom.left ≫ pullback.fst g (baseMap R F)

instance openToTarget_isOpenImmersion : IsOpenImmersion (openToTarget R F f g e) := by
  unfold openToTarget
  infer_instance

/-- The original structural maps agree on the actual partial graph. -/
lemma openToTarget_comp : (sourceOpen R F f).ι ≫ f = openToTarget R F f g e ≫ g := by
  have he : e.hom.left ≫ pullback.snd g (baseMap R F) = pullback.snd f (baseMap R F) :=
    Over.w e.hom
  apply (cancel_epi (sourceOpenIso R F f).hom).mp
  simp [sourceOpenIso, sourceOpen, openToTarget, Category.assoc,
    pullback.condition, reassoc_of% he]

/-- The common model is the native image of the original partial graph. -/
abbrev model : Scheme.{u} :=
  GraphClosure.closure f g (sourceOpen R F f) (openToTarget R F f g e) (openToTarget_comp R F f g e)

/-- The original graph-closure projection to the first trait scheme. -/
abbrev toSource : model R F f g e ⟶ X :=
  GraphClosure.toSource f g (sourceOpen R F f) (openToTarget R F f g e)
    (openToTarget_comp R F f g e)

/-- The original graph-closure projection to the second trait scheme. -/
abbrev toTarget : model R F f g e ⟶ Y :=
  GraphClosure.toTarget f g (sourceOpen R F f) (openToTarget R F f g e)
    (openToTarget_comp R F f g e)

/-- The common model's original structural map to the trait. -/
def toBase : model R F f g e ⟶ Spec (.of R) := toSource R F f g e ≫ f

@[reassoc]
lemma toSource_comp : toSource R F f g e ≫ f = toTarget R F f g e ≫ g :=
  GraphClosure.toSource_comp ..

/-- The original literal generic source mapped into the actual closed graph. -/
def fromGeneric : pullback f (baseMap R F) ⟶ model R F f g e :=
  (sourceOpenIso R F f).hom ≫
    GraphClosure.fromOpen f g (sourceOpen R F f) (openToTarget R F f g e)
      (openToTarget_comp R F f g e)

@[reassoc (attr := simp)]
lemma fromGeneric_toSource : fromGeneric R F f g e ≫ toSource R F f g e =
    pullback.fst f (baseMap R F) := by
  simp [fromGeneric, toSource, sourceOpenIso, sourceOpen]

@[reassoc (attr := simp)]
lemma fromGeneric_toTarget : fromGeneric R F f g e ≫ toTarget R F f g e =
    e.hom.left ≫ pullback.fst g (baseMap R F) := by
  simp [fromGeneric, toTarget, openToTarget, Category.assoc]

/-- The original projections are proper over their original targets. -/
instance toSource_isProper [IsProper g] : IsProper (toSource R F f g e) := inferInstance

instance toTarget_isProper [IsProper f] : IsProper (toTarget R F f g e) := inferInstance

instance toBase_isProper [IsProper f] [IsProper g] : IsProper (toBase R F f g e) := by
  unfold toBase
  infer_instance

instance sourceOpen_quasiCompact [IsNoetherian X] : QuasiCompact (sourceOpen R F f).ι :=
  inferInstance

/-- The first literal generic comparison has the original projection as its forward map. -/
def sourceGenericIso [IsNoetherian X] [IsProper g] :
    (Over.pullback (baseMap R F)).obj (Over.mk (toBase R F f g e)) ≅
      (Over.pullback (baseMap R F)).obj (Over.mk f) :=
  GraphClosure.baseChangeSourceIso f g (sourceOpen R F f) (openToTarget R F f g e)
    (openToTarget_comp R F f g e) (baseMap R F) (sourceOpenBase R F f) (sourceSquare R F f)

/-- The second literal generic comparison retains the specified original isomorphism. -/
def targetGenericIso [IsNoetherian X] [IsProper g] :
    (Over.pullback (baseMap R F)).obj (Over.mk (toBase R F f g e)) ≅
      (Over.pullback (baseMap R F)).obj (Over.mk g) := sourceGenericIso R F f g e ≪≫ e

lemma sourceGenericIso_hom [IsNoetherian X] [IsProper g] :
    (sourceGenericIso R F f g e).hom =
      (Over.pullback (baseMap R F)).map (Over.homMk (toSource R F f g e) rfl) :=
  GraphClosure.baseChangeSourceIso_hom ..

lemma targetGenericIso_hom [IsNoetherian X] [IsProper g] :
    (targetGenericIso R F f g e).hom =
      (Over.pullback (baseMap R F)).map
        (Over.homMk (toTarget R F f g e) (toSource_comp R F f g e).symm) := by
  symm
  apply GraphClosure.baseChange_overTarget_eq
  simp only [openToTarget, sourceSquare_isoPullback_hom]

/-- The supplied generic isomorphism is retained between the two comparisons. -/
lemma genericIso_compat [IsNoetherian X] [IsProper g] :
    sourceGenericIso R F f g e ≪≫ e = targetGenericIso R F f g e := rfl

private lemma source_dominant [IsIntegral X] [IsProper f] [Flat f] : IsDominant f :=
  ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace f f.isOpenMap⟩

instance sourceOpen_integral [IsIntegral X] [IsProper f] [Flat f] :
    IsIntegral (sourceOpen R F f).toScheme := by
  have : IsDominant f := source_dominant R f
  have : IsIntegral (pullback f (baseMap R F)) :=
    Scheme.FunctionField.DedekindGenericFiber.integral_genericFiber R F f
  have : Nonempty (sourceOpen R F f).toScheme :=
    ⟨(sourceOpenIso R F f).hom (Classical.choice (inferInstanceAs
      (Nonempty (pullback (C := Scheme.{u}) f (baseMap R F)))))⟩
  exact isIntegral_of_isOpenImmersion (sourceOpen R F f).ι

instance model_integral [IsIntegral X] [IsNoetherian X]
    [IsProper f] [Flat f] [IsProper g] : IsIntegral (model R F f g e) :=
  Scheme.schemeImage_isIntegral (GraphClosure.graph f g (sourceOpen R F f)
    (openToTarget R F f g e) (openToTarget_comp R F f g e))

instance model_noetherian [IsNoetherian X] [IsProper g] : IsNoetherian (model R F f g e) := by
  have : IsLocallyNoetherian (model R F f g e) :=
    LocallyOfFiniteType.isLocallyNoetherian (toSource R F f g e)
  have : CompactSpace (model R F f g e) :=
    QuasiCompact.compactSpace_of_compactSpace (toSource R F f g e)
  exact ⟨⟩

instance toSource_surjective [IsIntegral X]
    [IsProper f] [Flat f] [IsProper g] : Surjective (toSource R F f g e) := by
  have hne : Nonempty (sourceOpen R F f).toScheme := inferInstance
  exact GraphClosure.toSource_surjective f g (sourceOpen R F f) (openToTarget R F f g e)
    (openToTarget_comp R F f g e)
    ((sourceOpen R F f).isOpen.dense (Set.nonempty_coe_sort.mp hne))

instance toTarget_dominant [IsIntegral X] [IsIntegral Y]
    [IsProper f] [Flat f] : IsDominant (toTarget R F f g e) := by
  have : IsDominant (openToTarget R F f g e) :=
    Scheme.isDominant_of_isOpenImmersion (openToTarget R F f g e)
  have : IsDominant
      (GraphClosure.fromOpen f g (sourceOpen R F f) (openToTarget R F f g e)
        (openToTarget_comp R F f g e) ≫ toTarget R F f g e) := by
    rw [GraphClosure.fromOpen_toTarget]
    infer_instance
  exact IsDominant.of_comp
    (GraphClosure.fromOpen f g (sourceOpen R F f) (openToTarget R F f g e)
      (openToTarget_comp R F f g e)) (toTarget R F f g e)

instance toTarget_surjective [IsIntegral X] [IsIntegral Y]
    [IsProper f] [Flat f] : Surjective (toTarget R F f g e) :=
  surjective_of_isDominant_of_isClosed_range _ (toTarget R F f g e).isClosedMap.isClosed_range

/-- The actual integral graph model is flat over the DVR. -/
instance toBase_flat [IsIntegral X] [IsNoetherian X]
    [IsProper f] [Flat f] [IsProper g] : Flat (toBase R F f g e) := by
  have : IsDominant f := source_dominant R f
  have : IsDominant (toBase R F f g e) := by unfold toBase; infer_instance
  exact Scheme.Hom.flat_of_isIntegral_of_isDominant (toBase R F f g e)

private lemma fieldMap_isIso_of_open_comp {U C Z : Scheme.{u}}
    [IsIntegral U] [IsIntegral C] [IsIntegral Z]
    (i : U ⟶ C) (p : C ⟶ Z) [IsOpenImmersion i] [IsDominant p]
    [IsOpenImmersion (i ≫ p)] : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap p)) := by
  have : IsDominant i := Scheme.isDominant_of_isOpenImmersion i
  have : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap i)) :=
    Scheme.FunctionField.fieldMap_isIso i
  have : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap p) ≫
      CommRingCat.ofHom (Scheme.functionFieldMap i)) := by
    rw [← CommRingCat.ofHom_comp, ← Scheme.functionFieldMap_comp]
    exact Scheme.FunctionField.fieldMap_isIso (i ≫ p)
  exact IsIso.of_isIso_comp_right (CommRingCat.ofHom (Scheme.functionFieldMap p))
    (CommRingCat.ofHom (Scheme.functionFieldMap i))

/-- The actual source projection induces an isomorphism on function fields. -/
lemma sourceFunctionFieldMap_isIso [IsIntegral X] [IsNoetherian X]
    [IsProper f] [Flat f] [IsProper g] :
    IsIso (CommRingCat.ofHom (Scheme.functionFieldMap (toSource R F f g e))) := by
  let i := GraphClosure.fromOpen f g (sourceOpen R F f) (openToTarget R F f g e)
    (openToTarget_comp R F f g e)
  have : IsOpenImmersion (i ≫ toSource R F f g e) := by
    rw [GraphClosure.fromOpen_toSource]
    infer_instance
  exact fieldMap_isIso_of_open_comp i (toSource R F f g e)

/-- The actual target projection induces an isomorphism on function fields. -/
lemma targetFunctionFieldMap_isIso [IsIntegral X] [IsIntegral Y] [IsNoetherian X]
    [IsProper f] [Flat f] [IsProper g] :
    IsIso (CommRingCat.ofHom (Scheme.functionFieldMap (toTarget R F f g e))) := by
  let i := GraphClosure.fromOpen f g (sourceOpen R F f) (openToTarget R F f g e)
    (openToTarget_comp R F f g e)
  have : IsOpenImmersion (i ≫ toTarget R F f g e) := by
    rw [GraphClosure.fromOpen_toTarget]
    infer_instance
  exact fieldMap_isIso_of_open_comp i (toTarget R F f g e)

/-- The function-field equivalence whose forward map is the original source
projection's function-field homomorphism. -/
def sourceFunctionFieldEquiv [IsIntegral X] [IsNoetherian X]
    [IsProper f] [Flat f] [IsProper g] :
    X.functionField ≃+* (model R F f g e).functionField := by
  let := sourceFunctionFieldMap_isIso R F f g e
  exact (asIso (CommRingCat.ofHom
    (Scheme.functionFieldMap (toSource R F f g e)))).commRingCatIsoToRingEquiv

/-- The function-field equivalence whose forward map is the original target
projection's function-field homomorphism. -/
def targetFunctionFieldEquiv [IsIntegral X] [IsIntegral Y] [IsNoetherian X]
    [IsProper f] [Flat f] [IsProper g] :
    Y.functionField ≃+* (model R F f g e).functionField := by
  let := targetFunctionFieldMap_isIso R F f g e
  exact (asIso (CommRingCat.ofHom
    (Scheme.functionFieldMap (toTarget R F f g e)))).commRingCatIsoToRingEquiv

@[simp]
lemma sourceFunctionFieldEquiv_apply [IsIntegral X] [IsNoetherian X]
    [IsProper f] [Flat f] [IsProper g] (a : X.functionField) :
    sourceFunctionFieldEquiv R F f g e a = Scheme.functionFieldMap (toSource R F f g e) a := rfl

@[simp]
lemma targetFunctionFieldEquiv_apply [IsIntegral X] [IsIntegral Y] [IsNoetherian X]
    [IsProper f] [Flat f] [IsProper g] (a : Y.functionField) :
    targetFunctionFieldEquiv R F f g e a = Scheme.functionFieldMap (toTarget R F f g e) a := rfl

/-- The literal generic fibre of an original section. -/
def genericSection (s : Spec (.of R) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    Spec (.of F) ⟶ pullback f (baseMap R F) :=
  pullback.lift (baseMap R F ≫ s) (𝟙 _) (by simp [Category.assoc, hs])

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] in
@[reassoc (attr := simp)]
lemma genericSection_fst (s : Spec (.of R) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    genericSection R F f s hs ≫ pullback.fst f (baseMap R F) = baseMap R F ≫ s :=
  pullback.lift_fst _ _ _

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] in
@[reassoc (attr := simp)]
lemma genericSection_snd (s : Spec (.of R) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    genericSection R F f s hs ≫ pullback.snd f (baseMap R F) = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- Compatible supplied sections lift to the actual common graph model. -/
def liftSection (s : Spec (.of R) ⟶ X) (hs : s ≫ f = 𝟙 _)
    (t : Spec (.of R) ⟶ Y) (ht : t ≫ g = 𝟙 _)
    (he : genericSection R F f s hs ≫ e.hom.left = genericSection R F g t ht) :
    Spec (.of R) ⟶ model R F f g e := by
  have : IsDominant (baseMap R F) := LocalRing.GenericFiber.fraction_base_dominant R F
  have : IsSchemeTheoreticallyDominant (baseMap R F) :=
    IsSchemeTheoreticallyDominant.of_isDominant (baseMap R F)
  let δ : Spec (.of R) ⟶ pullback f g := pullback.lift s t (by rw [hs, ht])
  let σ := genericSection R F f s hs ≫ (sourceOpenIso R F f).hom
  refine GraphClosure.liftFromDense f g (sourceOpen R F f) (openToTarget R F f g e)
    (openToTarget_comp R F f g e) (baseMap R F) δ σ ?_
  apply pullback.hom_ext (f := f) (g := g)
  · simp [σ, δ, sourceOpenIso, sourceOpen, Category.assoc]
  · simp [σ, δ, openToTarget, Category.assoc, reassoc_of% he]

@[reassoc (attr := simp)]
lemma liftSection_toSource (s : Spec (.of R) ⟶ X) (hs : s ≫ f = 𝟙 _)
    (t : Spec (.of R) ⟶ Y) (ht : t ≫ g = 𝟙 _)
    (he : genericSection R F f s hs ≫ e.hom.left = genericSection R F g t ht) :
    liftSection R F f g e s hs t ht he ≫ toSource R F f g e = s := by
  simp [liftSection]

@[reassoc (attr := simp)]
lemma liftSection_toTarget (s : Spec (.of R) ⟶ X) (hs : s ≫ f = 𝟙 _)
    (t : Spec (.of R) ⟶ Y) (ht : t ≫ g = 𝟙 _)
    (he : genericSection R F f s hs ≫ e.hom.left = genericSection R F g t ht) :
    liftSection R F f g e s hs t ht he ≫ toTarget R F f g e = t := by
  simp [liftSection]

@[reassoc (attr := simp)]
lemma liftSection_toBase (s : Spec (.of R) ⟶ X) (hs : s ≫ f = 𝟙 _)
    (t : Spec (.of R) ⟶ Y) (ht : t ≫ g = 𝟙 _)
    (he : genericSection R F f s hs ≫ e.hom.left = genericSection R F g t ht) :
    liftSection R F f g e s hs t ht he ≫ toBase R F f g e = 𝟙 _ := by
  simp [toBase, ← Category.assoc, hs]

end AlgebraicGeometry.Scheme.TraitGraph
