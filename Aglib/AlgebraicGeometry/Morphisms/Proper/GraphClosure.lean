/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# The original scheme-theoretic closure of a partial graph

For a morphism from an open subscheme into a proper target over the same base, take the
native scheme-theoretic image of its graph in the native fiber product. Its original
projection to the source is proper. If the open immersion is quasi-compact, the original
projection restricted to that open is an isomorphism. Density of the open makes the
proper projection surjective. These are geometric prerequisites for Chow modifications;
no projectivity or cohomological finiteness statement is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.GraphClosure

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (U : X.Opens)
  (h : U.toScheme ⟶ Y) (w : U.ι ≫ f = h ≫ g)

/-- The original graph morphism into the native fiber product. -/
def graph : U.toScheme ⟶ pullback f g := pullback.lift U.ι h w

@[reassoc (attr := simp)]
theorem graph_fst : graph f g U h w ≫ pullback.fst f g = U.ι := by
  simp [graph]

@[reassoc (attr := simp)]
theorem graph_snd : graph f g U h w ≫ pullback.snd f g = h := by
  simp [graph]

/-- The graph closure is exactly the native scheme-theoretic image. -/
abbrev closure : Scheme.{u} := (graph f g U h w).image

/-- The original open-source map into its graph closure. -/
abbrev fromOpen : U.toScheme ⟶ closure f g U h w := (graph f g U h w).toImage

/-- The original first projection from the graph closure. -/
def toSource : closure f g U h w ⟶ X :=
  (graph f g U h w).imageι ≫ pullback.fst f g

/-- The original second projection from the graph closure. -/
def toTarget : closure f g U h w ⟶ Y :=
  (graph f g U h w).imageι ≫ pullback.snd f g

@[reassoc (attr := simp)]
theorem fromOpen_toSource : fromOpen f g U h w ≫ toSource f g U h w = U.ι := by
  simp [toSource]

@[reassoc (attr := simp)]
theorem fromOpen_toTarget : fromOpen f g U h w ≫ toTarget f g U h w = h := by
  simp [toTarget]

/-- Both original projections agree over the original base scheme. -/
@[reassoc]
theorem toSource_comp : toSource f g U h w ≫ f = toTarget f g U h w ≫ g := by
  simp only [toSource, toTarget, Category.assoc, pullback.condition]

/-- Pairing the original projections recovers exactly the native image inclusion. -/
theorem pair_projections :
    pullback.lift (toSource f g U h w) (toTarget f g U h w) (toSource_comp f g U h w) =
      (graph f g U h w).imageι := by
  apply pullback.hom_ext <;> simp [toSource, toTarget]

/-- The original pair of projections is a closed immersion into the original fiber product. -/
instance pair_projections_isClosedImmersion :
    IsClosedImmersion (pullback.lift (toSource f g U h w) (toTarget f g U h w)
      (toSource_comp f g U h w)) := by
  rw [pair_projections]
  infer_instance

instance graph_isImmersion : IsImmersion (graph f g U h w) := by
  have : IsImmersion (graph f g U h w ≫ pullback.fst f g) := by
    rw [graph_fst]
    infer_instance
  exact IsImmersion.of_comp _ (pullback.fst f g)

instance graph_quasiCompact [QuasiSeparated g] [QuasiCompact U.ι] :
    QuasiCompact (graph f g U h w) := by
  have : QuasiCompact (graph f g U h w ≫ pullback.fst f g) := by
    rw [graph_fst]
    infer_instance
  exact QuasiCompact.of_comp _ (pullback.fst f g)

instance fromOpen_isOpenImmersion [QuasiSeparated g] [QuasiCompact U.ι] :
    IsOpenImmersion (fromOpen f g U h w) :=
  inferInstanceAs (IsOpenImmersion (graph f g U h w).toImage)

instance fromOpen_isDominant [QuasiSeparated g] [QuasiCompact U.ι] :
    IsDominant (fromOpen f g U h w) :=
  inferInstanceAs (IsDominant (graph f g U h w).toImage)

instance toSource_isProper [IsProper g] : IsProper (toSource f g U h w) := by
  unfold toSource
  infer_instance

instance toTarget_isProper [IsProper f] : IsProper (toTarget f g U h w) := by
  unfold toTarget
  infer_instance

/-- The original source map lands in the original inverse image of its open domain. -/
def fromOpenToPreimage : U.toScheme ⟶ ((toSource f g U h w) ⁻¹ᵁ U).toScheme :=
  IsOpenImmersion.lift ((toSource f g U h w) ⁻¹ᵁ U).ι (fromOpen f g U h w) (by
    rw [Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change (fromOpen f g U h w ≫ toSource f g U h w) x ∈ U
    rw [fromOpen_toSource]
    exact x.property)

@[reassoc (attr := simp)]
theorem fromOpenToPreimage_ι :
    fromOpenToPreimage f g U h w ≫ ((toSource f g U h w) ⁻¹ᵁ U).ι =
      fromOpen f g U h w := IsOpenImmersion.lift_fac _ _ _

/-- The original open lift is a section of the original restricted projection. -/
@[reassoc (attr := simp)]
theorem fromOpenToPreimage_restrict :
    fromOpenToPreimage f g U h w ≫ ((toSource f g U h w) ∣_ U) = 𝟙 U.toScheme := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc,
    fromOpenToPreimage_ι, fromOpen_toSource, Category.id_comp]

instance fromOpenToPreimage_isOpenImmersion [QuasiSeparated g] [QuasiCompact U.ι] :
    IsOpenImmersion (fromOpenToPreimage f g U h w) := by
  have : IsOpenImmersion
      (fromOpenToPreimage f g U h w ≫ ((toSource f g U h w) ⁻¹ᵁ U).ι) := by
    rw [fromOpenToPreimage_ι]
    infer_instance
  exact IsOpenImmersion.of_comp _ ((toSource f g U h w) ⁻¹ᵁ U).ι

instance fromOpenToPreimage_isDominant [QuasiSeparated g] [QuasiCompact U.ι] :
    IsDominant (fromOpenToPreimage f g U h w) := by
  have : IsDominant
      (fromOpenToPreimage f g U h w ≫ ((toSource f g U h w) ⁻¹ᵁ U).ι) := by
    rw [fromOpenToPreimage_ι]
    infer_instance
  exact IsDominant.of_comp_of_isOpenImmersion _ ((toSource f g U h w) ⁻¹ᵁ U).ι

instance fromOpenToPreimage_isProper [IsProper g] :
    IsProper (fromOpenToPreimage f g U h w) := by
  have : IsProper (fromOpenToPreimage f g U h w ≫ ((toSource f g U h w) ∣_ U)) := by
    rw [fromOpenToPreimage_restrict]
    infer_instance
  exact IsProper.of_comp _ ((toSource f g U h w) ∣_ U)

/-- The original projection is an isomorphism above the original open domain. -/
theorem isIso_toSource_restrict [IsProper g] [QuasiCompact U.ι] :
    IsIso ((toSource f g U h w) ∣_ U) := by
  let j := fromOpenToPreimage f g U h w
  let : Surjective j := surjective_of_isDominant_of_isClosed_range j
    j.isClosedMap.isClosed_range
  let : IsIso j := (isIso_iff_isOpenImmersion_and_surjective j).mpr
    ⟨inferInstance, inferInstance⟩
  have : IsIso (j ≫ ((toSource f g U h w) ∣_ U)) := by
    rw [fromOpenToPreimage_restrict]
    infer_instance
  exact IsIso.of_isIso_comp_left (f := j) _

/-- The native isomorphism above the original open has the original restricted projection
as its forward morphism. -/
def toSourceRestrictIso [IsProper g] [QuasiCompact U.ι] :
    ((toSource f g U h w) ⁻¹ᵁ U).toScheme ≅ U.toScheme := by
  letI := isIso_toSource_restrict f g U h w
  exact asIso ((toSource f g U h w) ∣_ U)

/-- The comparison keeps exactly the original scheme morphism restriction. -/
theorem toSourceRestrictIso_hom [IsProper g] [QuasiCompact U.ι] :
    (toSourceRestrictIso f g U h w).hom = ((toSource f g U h w) ∣_ U) := rfl

/-- The inverse comparison is the original lift of the open graph into its inverse image. -/
theorem toSourceRestrictIso_inv [IsProper g] [QuasiCompact U.ι] :
    (toSourceRestrictIso f g U h w).inv = fromOpenToPreimage f g U h w := by
  apply (cancel_mono (toSourceRestrictIso f g U h w).hom).mp
  rw [Iso.inv_hom_id, toSourceRestrictIso_hom, fromOpenToPreimage_restrict]

/-- If the original open is dense, the original proper graph-closure projection is
surjective. Quasi-compactness of the open is unnecessary for this conclusion. -/
theorem toSource_surjective [IsProper g] (hU : Dense (U : Set X)) :
    Surjective (toSource f g U h w) := by
  let : IsDominant U.ι := Opens.isDominant_ι hU
  have : IsDominant (fromOpen f g U h w ≫ toSource f g U h w) := by
    rw [fromOpen_toSource]
    infer_instance
  let : IsDominant (toSource f g U h w) := IsDominant.of_comp (fromOpen f g U h w) _
  exact surjective_of_isDominant_of_isClosed_range _
    (toSource f g U h w).isClosedMap.isClosed_range

end AlgebraicGeometry.Scheme.GraphClosure
