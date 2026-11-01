/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.OpenRecovery
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.Dimension
public import Aglib.AlgebraicGeometry.FunctionField.GenericFiber
public import Aglib.AlgebraicGeometry.Curves.Core
public import Aglib.AlgebraicGeometry.Curves.Regular
public import Aglib.AlgebraicGeometry.Curves.SmoothGeometry
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Normality
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Dimension
public import Aglib.AlgebraicGeometry.Properties.Normal.Components
public import Aglib.AlgebraicGeometry.Stalk.Dimension
public import Aglib.AlgebraicGeometry.Stalk.CodimensionOne
public import Aglib.AlgebraicGeometry.Geometrically.Connected.FieldExtension

/-! # The native proper normalization of a connected finite-etale open cover

For a connected finite-etale cover of a nonempty open in a smooth proper
geometrically connected curve over an algebraically closed field, the native
relative normalization already constructed by `OpenRecovery` is a smooth
proper geometrically connected curve. Its original open inclusion and
structural equation remain those of `OpenRecovery`; no compactification
structure, genus, Nagata hypothesis, or component choice is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.FiniteEtaleCompactification

variable (k : Type u) [Field k] [IsAlgClosed k]
  (X : FScheme k) (hX : Properties X)
  {U E : Scheme.{u}} [Nonempty U] (j : U ⟶ X.left) [IsOpenImmersion j]
  (p : E ⟶ U) [IsFinite p] [Etale p] [ConnectedSpace E]

/-- The unchanged relative normalization is a smooth proper geometrically
connected curve. The source cover need only be connected, not geometrically
connected by assumption. All finite-normalization and smoothness guards are
produced from the stated geometry. -/
theorem normalization_properties :
    letI : IsIntegral X.left := hX.isIntegral
    Properties (Over.mk ((OpenRecovery.genericMap j p).fromNormalization ≫ X.hom)) := by
  let : IsIntegral X.left := hX.isIntegral
  let : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  let : IsProper X.hom := hX.proper
  let : IsNoetherian X.left := curveProperties_isNoetherian hX
  let : ∀ x : X.left, IsIntegrallyClosed (X.left.presheaf.stalk x) := fun x =>
    (Scheme.smoothFieldNormality k X.left X.hom (curveProperties_smooth hX) x).2
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let : SmoothOfRelativeDimension 1 (j ≫ X.hom) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (j ≫ X.hom))
  let : SmoothOfRelativeDimension 1 (p ≫ j ≫ X.hom) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (p ≫ j ≫ X.hom))
  let : Smooth (p ≫ j ≫ X.hom) := SmoothOfRelativeDimension.smooth 1 _
  let : IsLocallyNoetherian E := LocallyOfFiniteType.isLocallyNoetherian (p ≫ j ≫ X.hom)
  let : IsIntegral E := Scheme.isIntegral_of_connected_normalStalks_actual E
    (Scheme.smoothFieldNormality k E (p ≫ j ≫ X.hom) inferInstance)
  let : IsDominant p := ⟨p.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  let : IsIso (genericFibreMap p) := genericFibreMap_isIso p
  let e := asIso (genericFibreMap p) ≪≫
    pullbackSymmetry p (U.fromSpecStalk (genericPoint U))
  have hIntegral : IsIntegral (pullback (U.fromSpecStalk (genericPoint U)) p) :=
    @IsIntegral.of_isIso (Spec E.functionField)
      (pullback (U.fromSpecStalk (genericPoint U)) p) inferInstance e.hom e.isIso_hom
  let : IsIntegral (OpenRecovery.genericCover j p).obj.left := hIntegral
  let C := OpenRecovery.genericCover j p
  let f := OpenRecovery.genericMap j p
  let : IsIntegral f.normalization := inferInstance
  let : IsFinite f.fromNormalization := OpenRecovery.fromNormalization_isFinite j p
  let : IsProper (f.fromNormalization ≫ X.hom) := inferInstance
  let : IsLocallyNoetherian f.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian f.fromNormalization
  let : CompactSpace f.normalization :=
    QuasiCompact.compactSpace_of_compactSpace (f.fromNormalization ≫ X.hom)
  let : IsNoetherian f.normalization := ⟨⟩
  let : ∀ y : f.normalization, IsIntegrallyClosed (f.normalization.presheaf.stalk y) :=
    fun y => (stalk_normal_domain X.left C y).1
  have hd (y : f.normalization) :
      ringKrullDim (f.normalization.presheaf.stalk y) =
        ringKrullDim (X.left.presheaf.stalk (f.fromNormalization y)) :=
    stalk_ringKrullDim X.left C y
  let : ∀ y : ClosedPoint f.normalization,
      IsDiscreteValuationRing (f.normalization.presheaf.stalk y.val) := fun y => by
    have hx : IsClosed ({f.fromNormalization y.val} : Set X.left) := by
      simpa only [Set.image_singleton] using f.fromNormalization.isClosedMap _ y.property
    have hy : ringKrullDim (f.normalization.presheaf.stalk y.val) = 1 :=
      (hd y.val).trans (Scheme.smoothClosedPointDimension k X.left X.hom 1
        hX.smooth (f.fromNormalization y.val) hx)
    exact CodimensionOnePoint.localRing_isDiscreteValuationRing ⟨y.val, hy⟩
  have hdim : topologicalKrullDim f.normalization ≤ 1 := by
    rw [Scheme.topologicalKrullDim_eq_iSup_stalk]
    apply iSup_le
    intro y
    rw [hd y]
    exact Scheme.smoothOfRelativeDimension_stalk_dimension_le k X.left X.hom 1
      (f.fromNormalization y)
  let : Smooth (f.fromNormalization ≫ X.hom) :=
    Smooth.of_regularStalks_of_perfectField k (f.fromNormalization ≫ X.hom)
      (regularStalks_of_closedDVR f.normalization hdim)
  refine ⟨smoothOfRelativeDimension_one_of_closedDVR k f.normalization
    (f.fromNormalization ≫ X.hom),
    (inferInstance : IsProper (f.fromNormalization ≫ X.hom)), ?_⟩
  exact Scheme.Geometrically.geometricallyConnected_of_connected_algebraicClosure k
    (f.fromNormalization ≫ X.hom)
    (Scheme.Geometrically.connectedSpace_fieldBaseChange k (AlgebraicClosure k)
      (f.fromNormalization ≫ X.hom))

end AlgebraicGeometry.Scheme.OverField.Curve.FiniteEtaleCompactification
