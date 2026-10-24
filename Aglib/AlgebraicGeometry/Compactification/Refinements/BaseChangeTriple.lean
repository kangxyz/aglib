/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.BaseChangeIteration
public import Aglib.AlgebraicGeometry.Compactification.Refinements.BaseChangeAssociator
public import Aglib.AlgebraicGeometry.Compactification.Refinements.BaseChangeSourceIso
public import Aglib.AlgebraicGeometry.Compactification.Refinements.BaseChangeCongr
public import Aglib.AlgebraicGeometry.Compactification.Refinements.SourceIsoCoherence
public import Aglib.AlgebraicGeometry.Compactification.Refinements.SourceIsoEquality

/-!
# Actual triple pasting for normalized base change

Both paths are assembled from the actual double comparisons, source-transport
comparisons, and base-equality comparisons. Their source identifications are
then matched by the native triple associator equation, before thinness is used.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom.DenseCompactification

variable {X S T U V : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (b : T ⟶ S) (c : U ⟶ T) (d : V ⟶ U)

/-- Source transport for the left native triple associator. -/
def tripleTransportLeft : DenseCompactification (pullback.fst (d ≫ c ≫ b) f) ⥤
    DenseCompactification (pullback.fst d (pullback.fst c (pullback.fst b f))) :=
  sourceIso _ (tripleSourceLeft f b c d) (tripleSourceLeft_hom_fst f b c d)

/-- Source transport for the right native triple associator. -/
def tripleTransportRight : DenseCompactification (pullback.fst (d ≫ c ≫ b) f) ⥤
    DenseCompactification (pullback.fst d (pullback.fst c (pullback.fst b f))) :=
  sourceIso _ (tripleSourceRight f b c d) (tripleSourceRight_hom_fst f b c d)

variable (C : DenseCompactification f)

/-- Collapse the outer base changes first, retaining the original base-associativity transport. -/
def baseChangeTripleLeftIso :
    ((baseChange b ⋙ baseChange c) ⋙ baseChange d).obj C ≅
      (baseChange (d ≫ c ≫ b) ⋙ tripleTransportLeft b c d).obj C := by
  let q₀ := pullback.fst (d ≫ c ≫ b) f
  let q₁ := pullback.fst ((d ≫ c) ≫ b) f
  let q₂ := pullback.fst (d ≫ c) (pullback.fst b f)
  let q₃ := pullback.fst d (pullback.fst c (pullback.fst b f))
  let e₀ := congrSourceIso (f := f) (Category.assoc d c b)
  let e₁ := iteratedSourceIso (f := f) b (d ≫ c)
  let e₂ := iteratedSourceIso (f := pullback.fst b f) c d
  have h₀ : e₀.hom ≫ q₀ = q₁ := congrSourceIso_hom_fst (Category.assoc d c b)
  have h₁ : e₁.hom ≫ q₁ = q₂ := iteratedSourceIso_hom_fst b (d ≫ c)
  have h₂ : e₂.hom ≫ q₂ = q₃ := iteratedSourceIso_hom_fst c d
  let F₁ := sourceIso q₂ e₁ h₁
  let F₂ := sourceIso q₃ e₂ h₂
  let D := (baseChange (d ≫ c ≫ b)).obj C
  exact baseChangeIterationIso c d ((baseChange b).obj C) ≪≫
    F₂.mapIso (baseChangeIterationIso b (d ≫ c) C) ≪≫
    F₂.mapIso (F₁.mapIso (baseChangeCongrIso (Category.assoc d c b) C)) ≪≫
    F₂.mapIso (sourceIsoCompIso q₀ q₁ q₂ e₀ e₁ h₀ h₁ D) ≪≫
    sourceIsoCompIso q₀ q₂ q₃ (e₁ ≪≫ e₀) e₂
      (sourceIso_comp_fac q₀ q₁ q₂ e₀ e₁ h₀ h₁) h₂ D

/-- Collapse the inner base changes first, with actual base-change/source-transport exchange. -/
def baseChangeTripleRightIso :
    ((baseChange b ⋙ baseChange c) ⋙ baseChange d).obj C ≅
      (baseChange (d ≫ c ≫ b) ⋙ tripleTransportRight b c d).obj C := by
  let q₀ := pullback.fst (d ≫ c ≫ b) f
  let q₁ := pullback.fst d (pullback.fst (c ≫ b) f)
  let q₂ := pullback.fst d (pullback.fst c (pullback.fst b f))
  let r := pullback.fst c (pullback.fst b f)
  let e := iteratedSourceIso (f := f) b c
  have he : e.hom ≫ pullback.fst (c ≫ b) f = r := iteratedSourceIso_hom_fst b c
  let e₀ := iteratedSourceIso (f := f) (c ≫ b) d
  let e₁ := pullbackSourceIso r e he d
  have h₀ : e₀.hom ≫ q₀ = q₁ := iteratedSourceIso_hom_fst (c ≫ b) d
  have h₁ : e₁.hom ≫ q₁ = q₂ := pullbackSourceIso_hom_fst r e he d
  let F₁ := sourceIso q₂ e₁ h₁
  let D := (baseChange (d ≫ c ≫ b)).obj C
  exact (baseChange d).mapIso (baseChangeIterationIso b c C) ≪≫
    baseChangeSourceIsoComponent r e he d ((baseChange (c ≫ b)).obj C) ≪≫
    F₁.mapIso (baseChangeIterationIso (c ≫ b) d C) ≪≫
    sourceIsoCompIso q₀ q₁ q₂ e₀ e₁ h₀ h₁ D

/-- Match the left pasted comparison to the right original source identification. -/
def baseChangeTripleLeftComparison :
    ((baseChange b ⋙ baseChange c) ⋙ baseChange d).obj C ≅
      (baseChange (d ≫ c ≫ b) ⋙ tripleTransportRight b c d).obj C :=
  baseChangeTripleLeftIso b c d C ≪≫
    (sourceIsoEquality _ (tripleSourceIso_assoc f b c d)
      (tripleSourceLeft_hom_fst f b c d) (tripleSourceRight_hom_fst f b c d)).app
        ((baseChange (d ≫ c ≫ b)).obj C)

/-- The two actual pasted normalized comparisons agree after their sources are identified. -/
lemma baseChangeTriple_assoc :
    baseChangeTripleLeftComparison b c d C = baseChangeTripleRightIso b c d C := by
  apply Iso.ext
  exact Subsingleton.elim _ _

/-- The actual triple comparison is natural in compactification refinements. -/
def baseChangeTriple : (baseChange b ⋙ baseChange c) ⋙ baseChange d ≅
    baseChange (d ≫ c ≫ b) ⋙ tripleTransportRight (f := f) b c d :=
  NatIso.ofComponents (baseChangeTripleRightIso b c d) (fun _ => Subsingleton.elim _ _)

/-- Triple associativity retains the equality after the original final normalization inclusion. -/
lemma baseChangeTriple_normalization :
    (baseChangeTripleLeftComparison b c d C).hom.hom ≫
        baseChangeNormalization (d ≫ c ≫ b) C =
      (baseChangeTripleRightIso b c d C).hom.hom ≫
        baseChangeNormalization (d ≫ c ≫ b) C :=
  congrArg (fun a : ((baseChange b ⋙ baseChange c) ⋙ baseChange d).obj C ≅
      (baseChange (d ≫ c ≫ b) ⋙ tripleTransportRight b c d).obj C =>
        a.hom.hom ≫ baseChangeNormalization (d ≫ c ≫ b) C)
    (baseChangeTriple_assoc b c d C)

/-- The pasted comparison retains the actual structural projection to the final new base. -/
@[reassoc (attr := simp)]
lemma baseChangeTriple_normalization_fst :
    (baseChangeTripleRightIso b c d C).hom.hom ≫
        baseChangeNormalization (d ≫ c ≫ b) C ≫ pullback.fst (d ≫ c ≫ b) C.p =
      (((baseChange b ⋙ baseChange c) ⋙ baseChange d).obj C).p :=
  (congrArg (fun k => (baseChangeTripleRightIso b c d C).hom.hom ≫ k)
    (baseChangeNormalization_fst (d ≫ c ≫ b) C)).trans
      (baseChangeTripleRightIso b c d C).hom.base_fac

end AlgebraicGeometry.Scheme.Hom.DenseCompactification
