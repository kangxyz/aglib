/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.CardinalityInduction

/-!
# Domination by literal normalized closed-point blowups

The original proper birational model need only be integral, not normal or
regular. Its finite generic normalization reduces to the two geometric
inductions, and the resulting comparison is composed with the original
normalization map. No chain or termination certificate is an input.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.NormalizedPointDomination

universe u

/-- Every actual proper birational integral model of a normal Noetherian
Nagata surface is dominated by a constructed finite chain of literal
normalized closed-point blowups. The original source is not assumed normal
or regular. Both final arrows are proper and birational, and the comparison
triangle is an equality of the original scheme morphisms. -/
theorem exists_domination
    {P Q : Scheme.{u}} [IsIntegral P] [IsIntegral Q] [IsNoetherian P]
    (hP : NormalStalks P)
    (hNagata : ∀ V : P.affineOpens, Nonempty V.1 → IsNagataRing.{u, 0} Γ(P, V.1))
    (hdP : topologicalKrullDim P ≤ 2)
    (q : Q ⟶ P) [IsProper q] [IsDominant q]
    (hq : IsIso (CommRingCat.ofHom (functionFieldMap q))) :
    ∃ (T : Scheme.{u}) (beta : T ⟶ P) (a : T ⟶ Q) (hT : IsIntegral T),
      letI := hT
      ∃ (hbeta : IsDominant beta) (ha : IsDominant a),
        letI := hbeta
        letI := ha
        ∃ (_ : Blowup.NormalizedPointBlowupChain beta),
          a ≫ q = beta ∧ NormalStalks T ∧ IsNoetherian T ∧ topologicalKrullDim T ≤ 2 ∧
            IsProper beta ∧ IsProper a ∧
            IsIso (CommRingCat.ofHom (functionFieldMap beta)) ∧
            IsIso (CommRingCat.ofHom (functionFieldMap a)) := by
  let N := (Q.fromSpecStalk (genericPoint Q)).normalization
  let ν : N ⟶ Q := (Q.fromSpecStalk (genericPoint Q)).fromNormalization
  let : IsIntegral N := inferInstance
  let : IsDominant ν := genericNormalization_isDominant Q
  let : IsFinite ν := genericNormalization_isFinite_of_birational q hNagata hdP hq
  have hν : IsIso (CommRingCat.ofHom (functionFieldMap ν)) :=
    genericNormalization_fieldMap_isIso Q
  let qn := ν ≫ q
  have hqn : IsIso (CommRingCat.ofHom (functionFieldMap qn)) := by
    let := hν
    let := hq
    rw [functionFieldMap_comp, CommRingCat.ofHom_comp]
    infer_instance
  let : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian qn
  let : CompactSpace N := QuasiCompact.compactSpace_of_compactSpace qn
  let : IsNoetherian N := ⟨⟩
  have hN : NormalStalks N := genericNormalization_normalStalks Q
  have hdN := dimension_le_two_of_birational qn hNagata hdP hqn
  obtain ⟨T, beta, a, hT, hbetaD, haD, c, he, hTN, hTNoeth, hdT, hbetaP, haP,
    hbetaff, haff⟩ := exists_normalSource_domination (𝟙 P)
      (FunctionField.fieldMap_isIso (𝟙 P)) hNagata hdP hP hN hdN qn hqn
  let := hT
  let := hbetaD
  let := haD
  let := haP
  refine ⟨T, beta, a ≫ ν, inferInstance, hbetaD, inferInstance, c, ?_, hTN,
    hTNoeth, hdT, hbetaP, inferInstance, hbetaff, ?_⟩
  · exact (Category.assoc a ν q).trans he
  · let := haff
    let := hν
    rw [functionFieldMap_comp, CommRingCat.ofHom_comp]
    infer_instance

end AlgebraicGeometry.Scheme.NormalizedPointDomination
