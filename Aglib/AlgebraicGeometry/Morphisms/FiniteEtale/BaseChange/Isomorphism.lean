/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange

/-!
# Full and faithful finite-etale pullback along isomorphisms

The proofs use the actual pullback composition and identity isomorphisms.
There are no normality, Noetherianity or completeness assumptions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

/-- Base change along an actual scheme isomorphism is full on finite-etale covers. -/
theorem baseChange_full_of_isIso {X T : Scheme.{u}} (j : T ⟶ X) [IsIso j] :
    (baseChange j).Full := by
  let g := inv j
  have hFG : baseChange j ⋙ baseChange g ≅ 𝟭 (Scheme.FiniteEtale X) :=
    (baseChangeComp j g).symm ≪≫
      eqToIso (congrArg baseChange (IsIso.inv_hom_id j)) ≪≫ baseChangeId X
  have hGF : baseChange g ⋙ baseChange j ≅ 𝟭 (Scheme.FiniteEtale T) :=
    (baseChangeComp g j).symm ≪≫
      eqToIso (congrArg baseChange (IsIso.hom_inv_id j)) ≪≫ baseChangeId T
  have : (baseChange g).Faithful := Functor.Faithful.of_comp_iso hGF
  exact Functor.Full.of_comp_faithful_iso hFG

/-- Base change along an actual scheme isomorphism is faithful. -/
theorem baseChange_faithful_of_isIso {X Z : Scheme.{u}} (j : Z ⟶ X) [IsIso j] :
    (baseChange j).Faithful := by
  have e : baseChange j ⋙ baseChange (inv j) ≅ 𝟭 (Scheme.FiniteEtale X) :=
    (baseChangeComp j (inv j)).symm ≪≫
      eqToIso (congrArg baseChange (IsIso.inv_hom_id j)) ≪≫ baseChangeId X
  exact Functor.Faithful.of_comp_iso e

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/Morphisms/FiniteEtale/GenericFieldBaseChange.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 d461db587d320e150fe23052d2f5767ff1e0a272658ce257fbac1bd1416f38ab. -/
