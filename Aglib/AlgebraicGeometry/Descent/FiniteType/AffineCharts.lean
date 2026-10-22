/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Diagrams
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Fixed affine target charts in base-change systems

A target open chart and its actual inverse image define schemes over the
original stage. Their later models are the native `baseChangeDiagram`, with
index category exactly `Over i`. The base schemes need not be affine, and no
finite-presentation hypothesis is imposed.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.BaseChangeChart

variable {I : Type u} [Category.{u} I]
  (D : I ⥤ Scheme.{u}) (i : I)
  {A B : Over (D.obj i)} (a : A ⟶ B) (V : B.left.Opens)

/-- The actual inverse-image chart with its original structural map. -/
def source : Over (D.obj i) := Over.mk ((a.left ⁻¹ᵁ V).ι ≫ A.hom)

/-- The chosen target chart with its original structural map. -/
def target : Over (D.obj i) := Over.mk (V.ι ≫ B.hom)

/-- The restriction of the specified original arrow to the target chart. -/
def map : source D i a V ⟶ target D i V :=
  Over.homMk (a.left ∣_ V) (by
    change (a.left ∣_ V) ≫ (V.ι ≫ B.hom) = (a.left ⁻¹ᵁ V).ι ≫ A.hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, a.w])

/-- The actual source-chart system; no replacement of its index category is made. -/
abbrev sourceDiagram : Over i ⥤ Scheme.{u} :=
  baseChangeDiagram D i (source D i a V).hom

/-- The actual target-chart system. -/
abbrev targetDiagram : Over i ⥤ Scheme.{u} :=
  baseChangeDiagram D i (target D i V).hom

/-- The canonical source-chart cone over the supplied base cone. -/
abbrev sourceCone (c : Cone D) : Cone (sourceDiagram D i a V) :=
  baseChangeCone D c i (source D i a V).hom

/-- The canonical target-chart cone over the supplied base cone. -/
abbrev targetCone (c : Cone D) : Cone (targetDiagram D i V) :=
  baseChangeCone D c i (target D i V).hom

/-- Source-chart base change preserves the supplied cofiltered limit. -/
def isLimitSourceCone [IsCofiltered I] (c : Cone D) (hc : IsLimit c) :
    IsLimit (sourceCone D i a V c) :=
  isLimitBaseChangeCone D c hc i (source D i a V).hom

/-- Target-chart base change preserves the supplied cofiltered limit. -/
def isLimitTargetCone [IsCofiltered I] (c : Cone D) (hc : IsLimit c) :
    IsLimit (targetCone D i V c) :=
  isLimitBaseChangeCone D c hc i (target D i V).hom

instance source_isAffineHom_map
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    {j k : Over i} (q : j ⟶ k) :
    IsAffineHom ((sourceDiagram D i a V).map q) :=
  inferInstanceAs (IsAffineHom ((baseChangeDiagram D i (source D i a V).hom).map q))

instance target_isAffineHom_map
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    {j k : Over i} (q : j ⟶ k) :
    IsAffineHom ((targetDiagram D i V).map q) :=
  inferInstanceAs (IsAffineHom ((baseChangeDiagram D i (target D i V).hom).map q))

/-- The inverse image of an affine target chart is compact for a map from a
compact scheme into a quasi-separated scheme. -/
lemma compactSpace_source [CompactSpace A.left] [QuasiSeparatedSpace B.left]
    [IsAffine V.toScheme] : CompactSpace (source D i a V).left := by
  have : QuasiCompact a.left := inferInstance
  have hV : IsCompact (V : Set B.left) :=
    (show IsAffineOpen V from (inferInstance : IsAffine V.toScheme)).isCompact
  exact isCompact_iff_compactSpace.mp (a.left.isCompact_preimage hV)

/-- The inverse-image open inherits quasi-separatedness from its source. -/
lemma quasiSeparatedSpace_source [QuasiSeparatedSpace A.left] :
    QuasiSeparatedSpace (source D i a V).left := by
  change QuasiSeparatedSpace (a.left ⁻¹ᵁ V).toScheme
  exact (isQuasiSeparated_iff_quasiSeparatedSpace _ (a.left ⁻¹ᵁ V).isOpen).mp
    (.of_quasiSeparatedSpace _)

/-- Every target-chart stage is affine because its projection to the original
affine chart is affine. The base stages themselves need not be affine. -/
instance target_isAffine_obj
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    [IsAffine V.toScheme] (j : Over i) :
    IsAffine ((targetDiagram D i V).obj j) := by
  change IsAffine (pullback (D.map j.hom) (V.ι ≫ B.hom))
  infer_instance

/-- Source-chart stages are compact by their affine projections to the
original compact source chart; no compactness hypothesis on the bases is needed. -/
lemma compactSpace_source_obj
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    [CompactSpace A.left] [QuasiSeparatedSpace B.left]
    [IsAffine V.toScheme] (j : Over i) :
    CompactSpace ((sourceDiagram D i a V).obj j) := by
  let := compactSpace_source D i a V
  have : IsAffineHom (pullback.snd (D.map j.hom) (source D i a V).hom) :=
    @MorphismProperty.IsStableUnderBaseChange.of_isPullback
      Scheme.{u} _ (@IsAffineHom) isAffineHom_isStableUnderBaseChange
      (source D i a V).left (D.obj j.left)
      (pullback (D.map j.hom) (source D i a V).hom) (D.obj i)
      (source D i a V).hom (D.map j.hom)
      (pullback.fst (D.map j.hom) (source D i a V).hom)
      (pullback.snd (D.map j.hom) (source D i a V).hom)
      (IsPullback.of_hasPullback (D.map j.hom) (source D i a V).hom)
      (inferInstance : IsAffineHom (D.map j.hom))
  exact @QuasiCompact.compactSpace_of_compactSpace
    (pullback (D.map j.hom) (source D i a V).hom) (source D i a V).left
    (pullback.snd (D.map j.hom) (source D i a V).hom) inferInstance
    (compactSpace_source D i a V)

/-- Source-chart stages are quasi-separated by their affine projections to
the original quasi-separated source chart. -/
lemma quasiSeparatedSpace_source_obj
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    [QuasiSeparatedSpace A.left] (j : Over i) :
    QuasiSeparatedSpace ((sourceDiagram D i a V).obj j) := by
  let := quasiSeparatedSpace_source D i a V
  have : IsAffineHom (pullback.snd (D.map j.hom) (source D i a V).hom) :=
    @MorphismProperty.IsStableUnderBaseChange.of_isPullback
      Scheme.{u} _ (@IsAffineHom) isAffineHom_isStableUnderBaseChange
      (source D i a V).left (D.obj j.left)
      (pullback (D.map j.hom) (source D i a V).hom) (D.obj i)
      (source D i a V).hom (D.map j.hom)
      (pullback.fst (D.map j.hom) (source D i a V).hom)
      (pullback.snd (D.map j.hom) (source D i a V).hom)
      (IsPullback.of_hasPullback (D.map j.hom) (source D i a V).hom)
      (inferInstance : IsAffineHom (D.map j.hom))
  exact @quasiSeparatedSpace_of_quasiSeparated
    (pullback (D.map j.hom) (source D i a V).hom) (source D i a V).left
    (pullback.snd (D.map j.hom) (source D i a V).hom)
    (quasiSeparatedSpace_source D i a V) inferInstance

end AlgebraicGeometry.Scheme.BaseChangeChart
