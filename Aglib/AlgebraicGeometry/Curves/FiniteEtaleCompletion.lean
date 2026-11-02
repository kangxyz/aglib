/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Core
public import Aglib.AlgebraicGeometry.Curves.Regular
public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts
public import Aglib.AlgebraicGeometry.FunctionField.GenericFiber
public import Aglib.AlgebraicGeometry.FunctionField.Normalization
public import Aglib.AlgebraicGeometry.Geometrically.Connected.FieldExtension
public import Aglib.AlgebraicGeometry.Geometrically.Integral.SmoothCurve
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Dimension
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Normality
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.Dimension
public import Aglib.AlgebraicGeometry.Normalization.Relative
public import Aglib.AlgebraicGeometry.Stalk.CodimensionOne

/-!
# Completion of the original finite étale cover of an open curve

The completion is the native relative normalization of the actual generic
pullback. Its restriction recovers the given cover through a proved cartesian
square. Over an algebraically closed field a connected cover gives a smooth
proper geometrically connected curve, finite over the original curve.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

section Construction

variable {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
  (j : U ⟶ X) [IsOpenImmersion j] (Y : FiniteEtale U)

/-- The actual generic pullback, viewed over the original base function field
through the canonical open function-field equivalence. -/
def genericCover : FiniteEtale (Spec X.functionField) := by
  let : IsIso (CommRingCat.ofHom (FunctionField.fieldEquiv j).toRingHom) :=
    FunctionField.fieldMap_isIso j
  exact mk (pullback.snd Y.obj.hom (U.fromSpecStalk (genericPoint U)) ≫
    Spec.map (CommRingCat.ofHom (FunctionField.fieldEquiv j).toRingHom))

/-- The single completion model: native relative normalization of the actual
generic cover over the original base. -/
def completion : Scheme.{u} :=
  ((genericCover j Y).obj.hom ≫ X.fromSpecStalk (genericPoint X)).normalization

/-- The native relative-normalization structural map. -/
def completionMap : completion j Y ⟶ X :=
  ((genericCover j Y).obj.hom ≫ X.fromSpecStalk (genericPoint X)).fromNormalization

private theorem genericCover_over :
    (genericCover j Y).obj.hom ≫ X.fromSpecStalk (genericPoint X) =
      (pullback.fst Y.obj.hom (U.fromSpecStalk (genericPoint U)) ≫ Y.obj.hom) ≫ j := by
  change (pullback.snd _ _ ≫ _) ≫ _ = _
  rw [Category.assoc, ← FunctionField.fieldEquiv_generic_triangle j,
    ← Category.assoc, ← pullback.condition, Category.assoc]

section NormalOpen

variable [∀ x : U, IsIntegrallyClosed (U.presheaf.stalk x)]

/-- Normalization and smooth base change identify the restriction with the
original cover over its original open base. -/
def completionOverIso :
    Y.obj ≅ Over.mk (pullback.snd (completionMap j Y) j) := by
  let a := pullback.fst Y.obj.hom (U.fromSpecStalk (genericPoint U))
  let b := a ≫ Y.obj.hom
  let h := (genericCover j Y).obj.hom ≫ X.fromSpecStalk (genericPoint X)
  have : IsIso a.fromNormalization :=
    Hom.normalizationFrom_isIso_of_smooth_pullback
      (U.fromSpecStalk (genericPoint U)) Y.obj.hom
      (pullback.snd Y.obj.hom (U.fromSpecStalk (genericPoint U))) a
      (IsPullback.of_hasPullback _ _).flip
  let d := b.normalizationDesc a Y.obj.hom rfl
  have : IsIso d := Hom.normalizationDesc_isIso b a Y.obj.hom rfl
  have hp : IsPullback (𝟙 _) b h j :=
    IsPullback.of_horiz_isIso_mono ⟨by simpa only [Category.id_comp] using genericCover_over j Y⟩
  let e := (asIso d).symm ≪≫
    Hom.normalizationSourceIso hp.isoPullback b (pullback.snd h j)
      hp.isoPullback_hom_snd ≪≫ asIso (h.normalizationPullback j)
  refine Over.isoMk e ?_
  change e.hom ≫ pullback.snd h.fromNormalization j = Y.obj.hom
  dsimp only [e, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom]
  simp only [Category.assoc, Hom.normalizationPullback_snd,
    Hom.normalizationSourceIso_hom_over]
  rw [← b.normalizationDesc_comp a Y.obj.hom rfl]
  exact IsIso.inv_hom_id_assoc d Y.obj.hom

/-- The underlying scheme comparison is the forgetful image of the same
comparison over the original open base. -/
def completionOpenIso : Y.obj.left ≅ pullback (completionMap j Y) j :=
  (Over.forget U).mapIso (completionOverIso j Y)

@[reassoc (attr := simp)]
theorem completionOpenIso_hom_snd :
    (completionOpenIso j Y).hom ≫ pullback.snd (completionMap j Y) j = Y.obj.hom :=
  (completionOverIso j Y).hom.w

/-- The original cover embeds openly into its single normalization completion. -/
def completionOpen : Y.obj.left ⟶ completion j Y :=
  (completionOpenIso j Y).hom ≫ pullback.fst (completionMap j Y) j

@[reassoc (attr := simp)]
theorem completionOpen_over :
    completionOpen j Y ≫ completionMap j Y = Y.obj.hom ≫ j := by
  simp only [completionOpen, Category.assoc, pullback.condition,
    completionOpenIso_hom_snd_assoc]

/-- The cartesian square retains the given cover and the given open immersion. -/
theorem completion_isPullback :
    IsPullback (completionOpen j Y) Y.obj.hom (completionMap j Y) j :=
  IsPullback.of_iso_pullback ⟨completionOpen_over j Y⟩ (completionOpenIso j Y)
    rfl (completionOpenIso_hom_snd j Y)

instance completionOpen_isOpenImmersion : IsOpenImmersion (completionOpen j Y) := by
  dsimp only [completionOpen]
  infer_instance

/-- The same cartesian square identifies the entire boundary, including the
case of an empty boundary. -/
theorem completionOpen_range :
    Set.range (completionOpen j Y) = completionMap j Y ⁻¹' Set.range j := by
  change Set.range (pullback.fst (completionMap j Y) j ∘ (completionOpenIso j Y).hom) = _
  rw [Set.range_comp, (completionOpenIso j Y).hom.surjective.range_eq,
    Set.image_univ, Scheme.Pullback.range_fst]

end NormalOpen

section Finite

variable [IsLocallyNoetherian X] [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]

instance completionMap_isFinite : IsFinite (completionMap j Y) := by
  dsimp only [completionMap]
  infer_instance

instance completion_isLocallyNoetherian : IsLocallyNoetherian (completion j Y) :=
  LocallyOfFiniteType.isLocallyNoetherian (completionMap j Y)

instance completion_stalk_isIntegrallyClosed (x : completion j Y) :
    IsIntegrallyClosed ((completion j Y).presheaf.stalk x) :=
  GenericNormalization.instIsIntegrallyClosedStalk X (genericCover j Y) x

instance completion_stalk_isDomain (x : completion j Y) :
    IsDomain ((completion j Y).presheaf.stalk x) :=
  GenericNormalization.instIsDomainStalk X (genericCover j Y) x

/-- Normalization preserves the dimension of the actual image stalk. -/
theorem completion_stalk_dimension (x : completion j Y) :
    ringKrullDim ((completion j Y).presheaf.stalk x) =
      ringKrullDim (X.presheaf.stalk (completionMap j Y x)) :=
  GenericNormalization.stalk_ringKrullDim X (genericCover j Y) x

/-- A supplied finite closed boundary pulls back to the full finite closed
boundary of the original cover in its completion. -/
theorem completion_boundary [∀ x : U, IsIntegrallyClosed (U.presheaf.stalk x)]
    (D : Set X) (hDfinite : D.Finite) (hDclosed : IsClosed D)
    (hj : Set.range j = Dᶜ) :
    (completionMap j Y ⁻¹' D).Finite ∧ IsClosed (completionMap j Y ⁻¹' D) ∧
      Set.range (completionOpen j Y) = (completionMap j Y ⁻¹' D)ᶜ := by
  refine ⟨(completionMap j Y).finite_preimage hDfinite,
    hDclosed.preimage (completionMap j Y).continuous, ?_⟩
  rw [completionOpen_range, hj, Set.preimage_compl]

end Finite

instance completionMap_isDominant [Surjective Y.obj.hom] :
    IsDominant (completionMap j Y) := by
  let : IsIso (CommRingCat.ofHom (FunctionField.fieldEquiv j).toRingHom) :=
    FunctionField.fieldMap_isIso j
  have : Surjective (genericCover j Y).obj.hom := by
    change Surjective (pullback.snd Y.obj.hom (U.fromSpecStalk (genericPoint U)) ≫
      Spec.map (CommRingCat.ofHom (FunctionField.fieldEquiv j).toRingHom))
    infer_instance
  have : IsDominant ((genericCover j Y).obj.hom ≫ X.fromSpecStalk (genericPoint X)) := by
    infer_instance
  have : IsDominant
      (((genericCover j Y).obj.hom ≫ X.fromSpecStalk (genericPoint X)).toNormalization ≫
        completionMap j Y) := by
    change IsDominant
      (((genericCover j Y).obj.hom ≫ X.fromSpecStalk (genericPoint X)).toNormalization ≫
        ((genericCover j Y).obj.hom ≫ X.fromSpecStalk (genericPoint X)).fromNormalization)
    rw [Hom.toNormalization_fromNormalization]
    infer_instance
  exact IsDominant.of_comp
    ((genericCover j Y).obj.hom ≫ X.fromSpecStalk (genericPoint X)).toNormalization
    (completionMap j Y)

instance completion_isIntegral [IsIntegral Y.obj.left] [IsDominant Y.obj.hom] :
    IsIntegral (completion j Y) := by
  let : IsIso (genericFibreMap Y.obj.hom) := genericFibreMap_isIso Y.obj.hom
  let : IsIntegral (pullback Y.obj.hom (U.fromSpecStalk (genericPoint U))) :=
    IsIntegral.of_isIso (genericFibreMap Y.obj.hom)
  change IsIntegral ((genericCover j Y).obj.hom ≫
    X.fromSpecStalk (genericPoint X)).normalization
  let : IsIntegral (genericCover j Y).obj.left := by
    change IsIntegral (pullback Y.obj.hom (U.fromSpecStalk (genericPoint U)))
    infer_instance
  infer_instance

end Construction

end AlgebraicGeometry.Scheme.FiniteEtale

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Scheme.FiniteEtale

/-- Every original connected surjective finite étale cover of a nonempty open
in a smooth proper geometrically connected curve over an algebraically closed
field extends to a finite dominant map of such curves. The displayed square
uses the original cover and the original open immersion. -/
theorem exists_finiteEtaleCompletion
    {k : Type u} [Field k] [IsAlgClosed k] (C : FScheme k) (hC : Properties C)
    {U : Scheme.{u}} [Nonempty U] (j : U ⟶ C.left) [IsOpenImmersion j]
    (Y : FiniteEtale U) [ConnectedSpace Y.obj.left] [Surjective Y.obj.hom] :
    ∃ (D : FScheme k) (p : D ⟶ C) (i : Y.obj.left ⟶ D.left),
      Properties D ∧ IsFinite p.left ∧ IsDominant p.left ∧ IsOpenImmersion i ∧
        IsPullback i Y.obj.hom p.left j := by
  let : SmoothOfRelativeDimension 1 C.hom := hC.smooth
  let : Smooth C.hom := SmoothOfRelativeDimension.smooth 1 C.hom
  let : IsProper C.hom := hC.proper
  let : GeometricallyConnected C.hom := hC.connected
  let : ConnectedSpace C.left := GeometricallyConnected.connectedSpace_of_subsingleton C.hom
  let : IsIntegral C.left := isIntegral_of_connected_of_smoothOfRelativeDimension_one C.hom
  let : IsLocallyNoetherian C.left := LocallyOfFiniteType.isLocallyNoetherian C.hom
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let : SmoothOfRelativeDimension 1 (j ≫ C.hom) := by
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 1 j C.hom
  let : Smooth (j ≫ C.hom) := SmoothOfRelativeDimension.smooth 1 (j ≫ C.hom)
  let : SmoothOfRelativeDimension 1 (Y.obj.hom ≫ j ≫ C.hom) := by
    simpa only [Nat.zero_add] using
      smoothOfRelativeDimension_comp 0 1 Y.obj.hom (j ≫ C.hom)
  let : IsIntegral Y.obj.left :=
    isIntegral_of_connected_of_smoothOfRelativeDimension_one (Y.obj.hom ≫ j ≫ C.hom)
  let (x : C.left) : IsIntegrallyClosed (C.left.presheaf.stalk x) :=
    (smoothFieldNormality k C.left C.hom inferInstance x).2
  let (x : U) : IsIntegrallyClosed (U.presheaf.stalk x) :=
    (smoothFieldNormality k U (j ≫ C.hom) inferInstance x).2
  let N := completion j Y
  let p := completionMap j Y
  let q := p ≫ C.hom
  let : IsIntegral N := inferInstanceAs (IsIntegral (completion j Y))
  let : IsProper q := inferInstanceAs (IsProper (completionMap j Y ≫ C.hom))
  let : CompactSpace N := QuasiCompact.compactSpace_of_compactSpace q
  let : IsNoetherian N := ⟨⟩
  have hdim : topologicalKrullDim N ≤ 1 := by
    rw [topologicalKrullDim_eq_iSup_stalk]
    apply iSup_le
    intro x
    rw [completion_stalk_dimension j Y x]
    exact smoothOfRelativeDimension_stalk_dimension_le k C.left C.hom 1 (p x)
  have hclosed (x : ClosedPoint N) : IsClosed ({p x.val} : Set C.left) := by
    simpa only [Set.image_singleton] using p.isClosedMap {x.val} x.property
  let (x : ClosedPoint N) : IsDiscreteValuationRing (N.presheaf.stalk x.val) := by
    let z : CodimensionOnePoint N := ⟨x.val, by
      rw [completion_stalk_dimension j Y x.val]
      exact smoothClosedPointDimension k C.left C.hom 1 inferInstance (p x.val) (hclosed x)⟩
    exact CodimensionOnePoint.localRing_isDiscreteValuationRing z
  let : Smooth q := Smooth.of_regularStalks_of_perfectField k q
    (regularStalks_of_closedDVR N hdim)
  have hs : SmoothOfRelativeDimension 1 q :=
    smoothOfRelativeDimension_one_of_closedDVR k N q
  have hc : GeometricallyConnected q := by
    constructor
    apply (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
      (P := fun Z : Scheme.{u} => ConnectedSpace Z) (R := k) (f := q)).mpr
    intro K _ _
    exact Scheme.Geometrically.connectedSpace_fieldBaseChange k K q
  refine ⟨Over.mk q, Over.homMk p rfl, completionOpen j Y,
    ⟨hs, ?_, hc⟩, ?_, ?_, ?_, completion_isPullback j Y⟩
  · exact inferInstanceAs (IsProper q)
  · exact inferInstanceAs (IsFinite (completionMap j Y))
  · exact inferInstanceAs (IsDominant (completionMap j Y))
  · exact inferInstanceAs (IsOpenImmersion (completionOpen j Y))

/-- The finite closed boundary of the original open curve gives the exact
finite closed boundary of its completed cover, on the same cartesian square. -/
theorem exists_finiteEtaleCompletion_with_boundary
    {k : Type u} [Field k] [IsAlgClosed k] (C : FScheme k) (hC : Properties C)
    {U : Scheme.{u}} [Nonempty U] (j : U ⟶ C.left) [IsOpenImmersion j]
    (Y : FiniteEtale U) [ConnectedSpace Y.obj.left] [Surjective Y.obj.hom]
    (B : Set C.left) (hBfinite : B.Finite) (hBclosed : IsClosed B)
    (hj : Set.range j = Bᶜ) :
    ∃ (D : FScheme k) (p : D ⟶ C) (i : Y.obj.left ⟶ D.left),
      Properties D ∧ IsFinite p.left ∧ IsDominant p.left ∧ IsOpenImmersion i ∧
        IsPullback i Y.obj.hom p.left j ∧ (p.left ⁻¹' B).Finite ∧
          IsClosed (p.left ⁻¹' B) ∧ Set.range i = (p.left ⁻¹' B)ᶜ := by
  obtain ⟨D, p, i, hD, hp, hd, hi, hs⟩ := exists_finiteEtaleCompletion C hC j Y
  let := hp
  let := hi
  have hr : Set.range i = p.left ⁻¹' Set.range j := by
    rw [← hs.isoPullback_hom_fst]
    change Set.range (pullback.fst p.left j ∘ hs.isoPullback.hom) = _
    rw [Set.range_comp, hs.isoPullback.hom.surjective.range_eq, Set.image_univ,
      Scheme.Pullback.range_fst]
  exact ⟨D, p, i, hD, hp, hd, hi, hs, p.left.finite_preimage hBfinite,
    hBclosed.preimage p.left.continuous, by rw [hr, hj, Set.preimage_compl]⟩

end AlgebraicGeometry.Scheme.OverField.Curve
