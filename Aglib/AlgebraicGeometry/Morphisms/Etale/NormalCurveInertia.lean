/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.NormalCurve
public import Aglib.RingTheory.IntegralClosure.Inertia.Inseparable

/-!
# Inertia and finite-etale normalization of a normal curve

For an integral normal Noetherian target of dimension at most one, absolute inertia
at each chosen prime above an actual codimension-one stalk's maximal ideal detects
etaleness of the normalization of the original finite-etale generic cover. Fixedness
quantifies over every inertia element and every geometric point of that cover.

This uses the all-characteristic integral-closure criterion, allowing imperfect residue
fields and an inseparable ambient algebraic closure. Empty and split covers are allowed.
There is no regular-surface purity, cohomology or torsor-realization conclusion here.

Extraction sources at revision `f8a3314ddecffcada2ec721d26d56a937bed9690`:
* `R5Lab.Aglib.AlgebraicGeometry.Morphisms.Etale.InertiaPurity`, lines 27–37,
  SHA-256 `0e2fa717bcd9ee609e8c4921a1489aca32439466cfc274b03365e2368bc6b8f4`;
* `R5Lab.Aglib.AlgebraicGeometry.Morphisms.Etale.NormalCurvePurity`, lines 33–66,
  SHA-256 `b7b4a2014cfc7dfed510e7d0874cdf7f9d50cbd1c5085c5c85b18721aaf57153`.
The source application namespaces are replaced by native scheme and integral-closure owners.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.FiniteEtale (Fiber)
open AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois
open AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization
open AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.LocalComparison
open AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.NormalCurve

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

/-- The normal-curve inertia criterion for the actual relative normalization of an original
finite-etale generic cover, retaining the chosen prime over each actual divisor stalk. -/
structure NormalCurveCoverPurity : Prop where
  /-- If every chosen absolute inertia subgroup fixes every original geometric point,
  then the actual relative-normalization structural morphism is etale. -/
  etale : ∀ (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)],
    topologicalKrullDim X ≤ 1 → ∀ (C : Scheme.FiniteEtale (Spec X.functionField))
    (Q : ∀ x : CodimensionOnePoint X,
      Ideal (integralClosure x.localRing (AlgebraicClosure X.functionField)))
    [∀ x, (Q x).IsPrime] [∀ x, (Q x).LiesOver (IsLocalRing.maximalIdeal x.localRing)],
    (∀ (x : CodimensionOnePoint X)
      (γ : (Q x).inertia (AlgebraicClosure X.functionField ≃ₐ[X.functionField] AlgebraicClosure
          X.functionField))
      (t : Fiber (geometricPoint X.functionField) C),
      pointEnd X.functionField γ.val ≫ t = t) →
        Etale (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).fromNormalization

/-- The literal integral closure at an actual divisor stalk is etale if its chosen
absolute inertia subgroup fixes every geometric point of the original cover. -/
theorem divisor_closure_etale_of_original_points_fixed
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (C : Scheme.FiniteEtale (Spec X.functionField)) (x : CodimensionOnePoint X)
    (Q : Ideal (integralClosure x.localRing (AlgebraicClosure X.functionField)))
    [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal x.localRing)]
    (hfixed : ∀ γ : Q.inertia (AlgebraicClosure X.functionField ≃ₐ[X.functionField] AlgebraicClosure
        X.functionField),
      ∀ t : Fiber (geometricPoint X.functionField) C,
      pointEnd X.functionField γ.val ≫ t = t)
    (U : X.Opens) [Nonempty U] (hxU : x.1 ∈ U) :
    letI := stalkOriginalAlgebra X C U ⟨x.1, hxU⟩
    Algebra.Etale x.localRing (integralClosure x.localRing
      (Γ(C.obj.left, (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U))) := by
  let := stalkOriginalAlgebra X C U ⟨x.1, hxU⟩
  let := stalkOriginalFieldTower X C U ⟨x.1, hxU⟩
  apply integralClosure.Inertia.Inseparable.model_etale_of_algebraicClosure_inertia_trivial
    x.localRing X.functionField
    (Γ(C.obj.left, (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U)) Q
  intro σ hσ φ
  exact chart_embeddings_fixed_of_points_fixed X C U σ (fun t => hfixed ⟨σ, hσ⟩ t) φ

/-- The normal-curve inertia criterion is proved for the actual normalization and every
original geometric point, in every characteristic and with arbitrary residue fields. -/
theorem normalCurveCoverPurity : NormalCurveCoverPurity.{u} := by
  constructor
  intro X _ _ _ hdim C Q _ _ hfixed
  apply normalization_etale_of_codimensionOne X hdim C
  intro x
  obtain ⟨U, hU, hxU, _⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (Opens.mem_top x.1)
  let : Nonempty U := ⟨⟨x.1, hxU⟩⟩
  apply localPullback_etale_of_closure_etale X C U hU ⟨x.1, hxU⟩
  exact divisor_closure_etale_of_original_points_fixed X C x (Q x) (hfixed x) U hxU

end AlgebraicGeometry.Scheme.FiniteEtale
