/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteFieldCoverGluing
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# Morphism descent above a fixed field stage

Restrict an actual inverse limit to `Over i`, then base change to a fixed
quasi-compact and quasi-separated source over stage i. This keeps the original
finite-subset field index, including the requirement that the new stage lies
above the previously chosen stage.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent

universe u

section GeneralLimit

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  (i : I) (U V : Over (D.obj i))
  [CompactSpace U.left] [QuasiSeparatedSpace U.left]
  [LocallyOfFinitePresentation V.hom]

/-- The actual tail system, pulled back to U. -/
abbrev tailSourceDiagram : Over i ⥤ Over U.left :=
  Over.post D ⋙ Over.pullback U.hom

/-- The cone obtained by pulling the tail of `c` back along the structural map of `U` . -/
abbrev tailSourceCone : Cone (tailSourceDiagram D i U) :=
  (Over.pullback U.hom).mapCone (c.overPost i)

/-- The limit structure on the pulled-back tail cone, induced from the supplied limit
structure `hc` . -/
def tailSourceConeIsLimit : IsLimit (tailSourceCone D c i U) :=
  isLimitOfPreserves (Over.pullback U.hom) (hc.overPost i)

instance tailSource_stage_compact (j : Over i) :
    CompactSpace ((tailSourceDiagram D i U).obj j).left := by
  change CompactSpace ↥(pullback (C := Scheme.{u}) (D.map j.hom) U.hom)
  exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd (D.map j.hom) U.hom)

instance tailSource_stage_quasiSeparated (j : Over i) :
    QuasiSeparatedSpace ((tailSourceDiagram D i U).obj j).left := by
  change QuasiSeparatedSpace ↥(pullback (C := Scheme.{u}) (D.map j.hom) U.hom)
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd (D.map j.hom) U.hom)

instance tailSource_transition_affine {j k : Over i} (f : j ⟶ k) :
    IsAffineHom ((tailSourceDiagram D i U).map f).left := by
  exact MorphismProperty.of_isPullback
    (PurelyInseparable.Global.overPullback_map_isPullback U.hom ((Over.post D).map f)).flip
      (inferInstanceAs (IsAffineHom (D.map f.left)))

include hc in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A map from the base change of U to V descends at a stage above i, preserving
its structural map and its actual composite from the limit source. -/
theorem exists_tail_hom
    (q : pullback (c.π.app i) U.hom ⟶ V.left)
    (hq : q ≫ V.hom = pullback.snd (c.π.app i) U.hom ≫ U.hom) :
    ∃ (j : Over i) (g : pullback (D.map j.hom) U.hom ⟶ V.left),
      g ≫ V.hom = pullback.snd (D.map j.hom) U.hom ≫ U.hom ∧
      ((tailSourceCone D c i U).π.app j).left ≫ g = q := by
  let W := (Over.pullback U.hom).obj V
  have : LocallyOfFinitePresentation W.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd V.hom U.hom))
  let q' : (tailSourceCone D c i U).pt ⟶ W := Over.homMk
    (pullback.lift q (pullback.snd (c.π.app i) U.hom) hq) (pullback.lift_snd _ _ _)
  obtain ⟨j, g, hg⟩ := LimitDescent.exists_overHom (tailSourceDiagram D i U)
    (tailSourceCone D c i U) (tailSourceConeIsLimit D c hc i U) W q'
  refine ⟨j, g.left ≫ pullback.fst V.hom U.hom, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (fun k ↦ k ≫ U.hom) (Over.w g)
  · have H := congrArg (fun f ↦ f.left ≫ pullback.fst V.hom U.hom) hg
    simpa only [Over.comp_left, Category.assoc, q', Over.homMk_left,
      pullback.lift_fst] using H

end GeneralLimit

section FieldLimit

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of K))

/-- The diagram of field stages with their maps to `X` forgotten. -/
abbrev fieldSchemeDiagram : (Finset Ω)ᵒᵖ ⥤ Scheme.{u} :=
  FieldLimit.schemeDiagram K Ω p ⋙ Over.forget X

/-- The standard-order base change as the actual limit cone. -/
abbrev standardFieldCone : Cone (fieldSchemeDiagram K Ω p) :=
  ((Over.forget X).mapCone (FieldLimit.schemeCone K Ω p)).extend
    (pullbackSymmetry p (Spec.algebraMap K Ω)).hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The limit structure on the standard-order field cone, transported by pullback symmetry. -/
def standardFieldConeIsLimit : IsLimit (standardFieldCone K Ω p) :=
  IsLimit.extendIso (s := (Over.forget X).mapCone (FieldLimit.schemeCone K Ω p))
    (pullbackSymmetry p (Spec.algebraMap K Ω)).hom
    (isLimitOfPreserves (Over.forget X) (FieldLimit.schemeConeIsLimit K Ω p))

@[simp] theorem standardFieldCone_π (s : (Finset Ω)ᵒᵖ) :
    (standardFieldCone K Ω p).π.app s = FieldLimit.fieldProjection K Ω p s := rfl

end FieldLimit

end AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 76f0c99a4d55a8b754bf876fd6ec57000a3af37fdcaaf82e70dabbd42bb1b53a.
Definitions, hypotheses and universes are retained modulo native names. -/
