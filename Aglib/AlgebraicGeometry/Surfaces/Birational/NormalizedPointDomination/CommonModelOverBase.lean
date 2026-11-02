/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.CommonModel
public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.FiniteNormalization

/-!
# Finite normal common models over the original Nagata surface

The Nagata premises are solely on the original base, not on the newly
constructed graph. Adapted GF2 charts derive finite normalization; all
original graph projections and their exact triangle remain unchanged.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.NormalizedPointDomination.CommonModel

universe u

variable {X Y S P : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral S] [IsIntegral P]
  [IsNoetherian P]
  (f : X ⟶ S) (g : Y ⟶ S) [IsProper f] [IsProper g] [IsDominant f]
  (hf : IsIso (CommRingCat.ofHom (functionFieldMap f)))
  (U : X.Opens) [Nonempty U] [QuasiCompact U.ι]
  (h : U.toScheme ⟶ Y) [IsOpenImmersion h] (w : U.ι ≫ f = h ≫ g)
  (b : S ⟶ P) [IsProper b] [IsDominant b]
  (hb : IsIso (CommRingCat.ofHom (functionFieldMap b)))
  (hNagata : ∀ V : P.affineOpens, Nonempty V.1 → IsNagataRing.{u, 0} Γ(P, V.1))
  (hdP : topologicalKrullDim P ≤ 2)

local notation "G" => GraphClosure.closure f g U h w
local notation "γ" => Scheme.fromSpecStalk G (genericPoint G)

include hf b hb hNagata hdP
omit [IsIntegral Y] [IsOpenImmersion h]

omit [IsNoetherian P] in
/-- Finite normalization is derived from the original base, rather than
assumed for the graph or for the whole fibre product. -/
theorem normalization_isFinite_over_base : IsFinite (γ).fromNormalization := by
  let a := GraphClosure.toSource f g U h w ≫ f ≫ b
  let : IsIso (CommRingCat.ofHom (functionFieldMap (GraphClosure.toSource f g U h w))) :=
    component_toSource_fieldMap_isIso f g U h w
  let := hf
  let := hb
  have ha : IsIso (CommRingCat.ofHom (functionFieldMap a)) := by
    simp only [a, functionFieldMap_comp, CommRingCat.ofHom_comp]
    infer_instance
  exact genericNormalization_isFinite_of_birational a hNagata hdP ha

omit [IsNoetherian P] in
/-- Both actual normalized graph projections are proper. -/
theorem projections_isProper_over_base :
    IsProper (toSource f g U h w) ∧ IsProper (toTarget f g U h w) := by
  let : IsFinite (γ).fromNormalization :=
    normalization_isFinite_over_base f g hf U h w b hb hNagata hdP
  constructor
  · unfold toSource
    infer_instance
  · unfold toTarget
    infer_instance

omit [IsNoetherian P] in
/-- The actual pair is finite over the literal fibre product, derived from
original-base Nagata charts and the selected schematic graph component. -/
theorem pair_isFinite_over_base :
    IsFinite (pullback.lift (toSource f g U h w) (toTarget f g U h w)
      (toSource_comp f g U h w)) := by
  let : IsFinite (γ).fromNormalization :=
    normalization_isFinite_over_base f g hf U h w b hb hNagata hdP
  have he : pullback.lift (toSource f g U h w) (toTarget f g U h w)
      (toSource_comp f g U h w) = (γ).fromNormalization ≫
        (GraphClosure.graph f g U h w).imageι := by
    apply pullback.hom_ext <;> simp [toSource, toTarget, GraphClosure.toSource,
      GraphClosure.toTarget]
  rw [he]
  infer_instance

/-- The actual normal common model is Noetherian, by its proper accumulated
map to the original Noetherian surface. -/
theorem model_isNoetherian_over_base : IsNoetherian (model f g U h w) := by
  let : IsProper (toSource f g U h w) :=
    (projections_isProper_over_base f g hf U h w b hb hNagata hdP).1
  let a := toSource f g U h w ≫ f ≫ b
  let : IsLocallyNoetherian (model f g U h w) :=
    LocallyOfFiniteType.isLocallyNoetherian a
  let : CompactSpace (model f g U h w) := QuasiCompact.compactSpace_of_compactSpace a
  exact ⟨⟩

omit [IsNoetherian P] in
/-- The actual common model retains the surface dimension bound. -/
theorem model_dimension_over_base : topologicalKrullDim (model f g U h w) ≤ 2 := by
  let : IsProper (toSource f g U h w) :=
    (projections_isProper_over_base f g hf U h w b hb hNagata hdP).1
  let : IsIso (CommRingCat.ofHom (functionFieldMap (toSource f g U h w))) :=
    toSource_fieldMap_isIso f g U h w
  let := hf
  let := hb
  let a := toSource f g U h w ≫ f ≫ b
  have ha : IsIso (CommRingCat.ofHom (functionFieldMap a)) := by
    simp only [a, functionFieldMap_comp, CommRingCat.ofHom_comp]
    infer_instance
  exact dimension_le_two_of_birational a hNagata hdP ha

end AlgebraicGeometry.Scheme.NormalizedPointDomination.CommonModel
