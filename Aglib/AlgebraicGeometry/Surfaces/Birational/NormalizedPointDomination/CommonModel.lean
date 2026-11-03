/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.GraphClosure
public import Aglib.AlgebraicGeometry.SchemeTheoreticImage.Integral
public import Aglib.AlgebraicGeometry.Normalization.FunctionField

/-!
# Normalization of the common dense-open graph component

The common model is the normalization of the actual schematic graph image,
not the normalization of the entire fibre product. Both actual projections
are dominant and induce isomorphisms on the original function fields.
Finiteness is derived from Nagata hypotheses on the graph's affine charts;
deriving those chart hypotheses from an arbitrary nonaffine surface base
is not asserted here.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.NormalizedPointDomination

universe u

namespace CommonModel

variable {X Y S : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ S) (g : Y ⟶ S) [IsProper f] [IsProper g]
  (U : X.Opens) [Nonempty U] [QuasiCompact U.ι]
  (h : U.toScheme ⟶ Y) [IsOpenImmersion h] (w : U.ι ≫ f = h ≫ g)

local instance open_isIntegral : IsIntegral U.toScheme :=
  isIntegral_of_isOpenImmersion U.ι

/-- The actual schematic graph component is integral, including its reduced structure. -/
instance component_isIntegral : IsIntegral (GraphClosure.closure f g U h w) :=
  schemeImage_isIntegral (GraphClosure.graph f g U h w)

/-- The first original graph projection is dominant by the open-graph triangle. -/
instance component_toSource_isDominant : IsDominant (GraphClosure.toSource f g U h w) := by
  let : IsDominant U.ι := isDominant_of_isOpenImmersion U.ι
  have : IsDominant (GraphClosure.fromOpen f g U h w ≫
      GraphClosure.toSource f g U h w) := by
    rw [GraphClosure.fromOpen_toSource]
    infer_instance
  exact IsDominant.of_comp (GraphClosure.fromOpen f g U h w) _

/-- The second original graph projection is dominant by the common open immersion. -/
instance component_toTarget_isDominant : IsDominant (GraphClosure.toTarget f g U h w) := by
  let : IsDominant h := isDominant_of_isOpenImmersion h
  have : IsDominant (GraphClosure.fromOpen f g U h w ≫
      GraphClosure.toTarget f g U h w) := by
    rw [GraphClosure.fromOpen_toTarget]
    infer_instance
  exact IsDominant.of_comp (GraphClosure.fromOpen f g U h w) _

omit [IsIntegral Y] [IsProper f] [IsOpenImmersion h] in
/-- Birationality of the first projection is on its original generic stalk map. -/
theorem component_toSource_fieldMap_isIso :
    IsIso (CommRingCat.ofHom (functionFieldMap (GraphClosure.toSource f g U h w))) := by
  let j := GraphClosure.fromOpen f g U h w
  let p := GraphClosure.toSource f g U h w
  let : IsIso (CommRingCat.ofHom (functionFieldMap j)) := FunctionField.fieldMap_isIso j
  have : IsOpenImmersion (j ≫ p) := by
    change IsOpenImmersion (GraphClosure.fromOpen f g U h w ≫
      GraphClosure.toSource f g U h w)
    rw [GraphClosure.fromOpen_toSource]
    infer_instance
  have : IsIso (CommRingCat.ofHom (functionFieldMap p) ≫
      CommRingCat.ofHom (functionFieldMap j)) := by
    rw [← CommRingCat.ofHom_comp, ← functionFieldMap_comp]
    exact FunctionField.fieldMap_isIso (j ≫ p)
  exact IsIso.of_isIso_comp_right (CommRingCat.ofHom (functionFieldMap p))
    (CommRingCat.ofHom (functionFieldMap j))

omit [IsProper f] in
/-- Birationality of the second projection retains the same common open graph. -/
theorem component_toTarget_fieldMap_isIso :
    IsIso (CommRingCat.ofHom (functionFieldMap (GraphClosure.toTarget f g U h w))) := by
  let j := GraphClosure.fromOpen f g U h w
  let p := GraphClosure.toTarget f g U h w
  let : IsIso (CommRingCat.ofHom (functionFieldMap j)) := FunctionField.fieldMap_isIso j
  have : IsOpenImmersion (j ≫ p) := by
    change IsOpenImmersion (GraphClosure.fromOpen f g U h w ≫
      GraphClosure.toTarget f g U h w)
    rw [GraphClosure.fromOpen_toTarget]
    infer_instance
  have : IsIso (CommRingCat.ofHom (functionFieldMap p) ≫
      CommRingCat.ofHom (functionFieldMap j)) := by
    rw [← CommRingCat.ofHom_comp, ← functionFieldMap_comp]
    exact FunctionField.fieldMap_isIso (j ≫ p)
  exact IsIso.of_isIso_comp_right (CommRingCat.ofHom (functionFieldMap p))
    (CommRingCat.ofHom (functionFieldMap j))

local notation "G" => GraphClosure.closure f g U h w
local notation "γ" => Scheme.fromSpecStalk G (genericPoint G)

/-- Normalization of the dominating graph component in its actual function field. -/
abbrev model : Scheme.{u} := (γ).normalization

/-- The original normalization arrow followed by the first graph projection. -/
def toSource : model f g U h w ⟶ X := (γ).fromNormalization ≫ GraphClosure.toSource f g U h w

/-- The original normalization arrow followed by the second graph projection. -/
def toTarget : model f g U h w ⟶ Y := (γ).fromNormalization ≫ GraphClosure.toTarget f g U h w

omit [IsIntegral Y] [IsProper f] [IsOpenImmersion h] in
/-- The normal common model retains the exact original commuting square. -/
@[reassoc] theorem toSource_comp : toSource f g U h w ≫ f = toTarget f g U h w ≫ g := by
  simp only [toSource, toTarget, Category.assoc, GraphClosure.toSource_comp]

omit [IsIntegral Y] [IsProper f] [IsOpenImmersion h] in
/-- Normality is proved for the actual component normalization, with no normality
hypothesis on the original two models. -/
theorem normalStalks_model : NormalStalks (model f g U h w) :=
  genericNormalization_normalStalks G

instance model_isIntegral : IsIntegral (model f g U h w) := inferInstance

instance normalization_isDominant : IsDominant (γ).fromNormalization :=
  genericNormalization_isDominant G

instance toSource_isDominant : IsDominant (toSource f g U h w) := by
  unfold toSource
  infer_instance

instance toTarget_isDominant : IsDominant (toTarget f g U h w) := by
  unfold toTarget
  infer_instance

omit [IsIntegral Y] [IsProper f] [IsOpenImmersion h] in
/-- The first normalized projection induces an isomorphism on the original fields. -/
theorem toSource_fieldMap_isIso :
    IsIso (CommRingCat.ofHom (functionFieldMap (toSource f g U h w))) := by
  let : IsIso (CommRingCat.ofHom (functionFieldMap (γ).fromNormalization)) :=
    genericNormalization_fieldMap_isIso G
  let : IsIso (CommRingCat.ofHom (functionFieldMap (GraphClosure.toSource f g U h w))) :=
    component_toSource_fieldMap_isIso f g U h w
  unfold toSource
  rw [functionFieldMap_comp, CommRingCat.ofHom_comp]
  infer_instance

omit [IsProper f] in
/-- The second normalized projection induces an isomorphism on the original fields. -/
theorem toTarget_fieldMap_isIso :
    IsIso (CommRingCat.ofHom (functionFieldMap (toTarget f g U h w))) := by
  let : IsIso (CommRingCat.ofHom (functionFieldMap (γ).fromNormalization)) :=
    genericNormalization_fieldMap_isIso G
  let : IsIso (CommRingCat.ofHom (functionFieldMap (GraphClosure.toTarget f g U h w))) :=
    component_toTarget_fieldMap_isIso f g U h w
  unfold toTarget
  rw [functionFieldMap_comp, CommRingCat.ofHom_comp]
  infer_instance

omit [IsIntegral Y] [IsProper f] [IsOpenImmersion h] in
/-- Nagata properties of the actual graph charts make the original normalization
finite. This premise is local chart data, not a supplied normalization map. -/
theorem normalization_isFinite
    (hNagata : ∀ V : (G).affineOpens, Nonempty V.1 → IsNagataRing.{u, 0} Γ(G, V.1)) :
    IsFinite (γ).fromNormalization := genericNormalization_isFinite G hNagata

omit [IsIntegral Y] [IsProper f] [IsOpenImmersion h] in
/-- Finite normalization followed by the original proper graph projection is proper. -/
theorem toSource_isProper
    (hNagata : ∀ V : (G).affineOpens, Nonempty V.1 → IsNagataRing.{u, 0} Γ(G, V.1)) :
    IsProper (toSource f g U h w) := by
  let : IsFinite (γ).fromNormalization := normalization_isFinite f g U h w hNagata
  unfold toSource
  infer_instance

omit [IsIntegral Y] [IsOpenImmersion h] in
/-- Both proper projections are retained, not only the projection to the new base. -/
theorem toTarget_isProper
    (hNagata : ∀ V : (G).affineOpens, Nonempty V.1 → IsNagataRing.{u, 0} Γ(G, V.1)) :
    IsProper (toTarget f g U h w) := by
  let : IsFinite (γ).fromNormalization := normalization_isFinite f g U h w hNagata
  unfold toTarget
  infer_instance

omit [IsIntegral Y] [IsProper f] [IsOpenImmersion h] in
/-- The map from the normal common model to the literal fibre product is finite:
it is the finite normalization followed by the original closed image inclusion. -/
theorem pair_isFinite
    (hNagata : ∀ V : (G).affineOpens, Nonempty V.1 → IsNagataRing.{u, 0} Γ(G, V.1)) :
    IsFinite (pullback.lift (toSource f g U h w) (toTarget f g U h w)
      (toSource_comp f g U h w)) := by
  let : IsFinite (γ).fromNormalization := normalization_isFinite f g U h w hNagata
  have he : pullback.lift (toSource f g U h w) (toTarget f g U h w)
      (toSource_comp f g U h w) = (γ).fromNormalization ≫
        (GraphClosure.graph f g U h w).imageι := by
    apply pullback.hom_ext <;> simp [toSource, toTarget, GraphClosure.toSource,
      GraphClosure.toTarget]
  rw [he]
  infer_instance

end CommonModel

end AlgebraicGeometry.Scheme.NormalizedPointDomination
