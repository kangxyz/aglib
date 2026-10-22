/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.CompletionFullness
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.AlgebraizedCoverComparison
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.ResidueStage
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.ProperResidue

/-!
# Finite-etale covers of proper schemes over complete local bases

For a proper scheme over a complete Noetherian local ring, restriction to the
literal residue-field pullback is an equivalence of finite-etale covers.
Local Noetherianity of the proper scheme is derived. No flatness, projectivity,
positive-rank assumption, or chosen realization appears in the public theorem.
This is the complete-local statement, not an arbitrary Henselian-base result.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

open Modules Modules.Coherent

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]

/-- Fullness for the original closed-fibre restriction functor. -/
theorem properCompleteLocal_baseChange_full :
    (baseChange (pullback.fst f (LocalRing.residueSpecMap A))).Full := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let := Adic.firstStage_baseChange_full
    (idealThickeningIdealSheaf f (IsLocalRing.maximalIdeal A))
    (Cohomology.completionFunctorFullyFaithful (IsLocalRing.maximalIdeal A) f)
  let : (baseChange (Adic.residueStageIso f).hom).Faithful :=
    baseChange_faithful_of_isIso _
  exact Functor.Full.of_comp_faithful_iso (Adic.residueStageBaseChangeIso f)

/-- Every actual closed-fibre finite-etale cover is the restriction of an
actual global finite-etale cover, with the original fibre comparison. -/
theorem properCompleteLocal_baseChange_essSurj :
    (baseChange (pullback.fst f (LocalRing.residueSpecMap A))).EssSurj := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hI : IsLocalRing.maximalIdeal A ≠ ⊤ :=
    (inferInstance : (IsLocalRing.maximalIdeal A).IsMaximal).ne_top
  constructor
  intro C
  let T := Adic.residueCoverSystem f C
  let d := Cohomology.properAdicAlgebraization (IsLocalRing.maximalIdeal A) f T.adicSystem
  let Y := Adic.algebraizedCover f (IsLocalRing.maximalIdeal A) hI T d
  exact ⟨Y, ⟨Adic.literalResidueCoverIso f Y C
    (Adic.algebraizedFirstStageIso f (IsLocalRing.maximalIdeal A) hI T d)⟩⟩

/-- The original closed-fibre restriction is an equivalence. -/
theorem properCompleteLocal_baseChange_isEquivalence :
    (baseChange (pullback.fst f (LocalRing.residueSpecMap A))).IsEquivalence where
  faithful := inferInstance
  full := properCompleteLocal_baseChange_full f
  essSurj := properCompleteLocal_baseChange_essSurj f

/-- Finite-etale covers of the proper scheme and its literal closed fibre. -/
def properCompleteLocalEquivalence :
    FiniteEtale X ≌ FiniteEtale (pullback f (LocalRing.residueSpecMap A)) := by
  letI := properCompleteLocal_baseChange_isEquivalence f
  exact (baseChange (pullback.fst f (LocalRing.residueSpecMap A))).asEquivalence

/-- The forward functor is definitionally the specified original base change. -/
@[simp]
theorem properCompleteLocalEquivalence_functor :
    (properCompleteLocalEquivalence f).functor =
      baseChange (pullback.fst f (LocalRing.residueSpecMap A)) := rfl

end AlgebraicGeometry.Scheme.FiniteEtale
