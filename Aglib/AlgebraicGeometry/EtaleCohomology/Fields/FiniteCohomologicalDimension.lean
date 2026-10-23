/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.DimensionShift
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteCoinduction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.HigherVanishing
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteH2

/-! # Higher original finite cohomology of algebraic function fields

Actual finite-etale coinduction supplies the geometric hypotheses of
classwise dimension shifting. Consequently degree-two vanishing for all
finite locally constant coefficients with a fixed annihilator on one field
implies vanishing in every higher degree on that field. The function-field
corollary uses the actual finite-coefficient Tsen degree-two theorem.
All conclusions are for the original `Sheaf.H` and the supplied Ext universe.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u w

attribute [local instance] hasSheafifyLarge

/-- For actual finite locally constant coefficients on a field, same-field
vanishing in degree two implies vanishing in every degree at least two.
The finite-coinduction exactness and finiteness premises are fully discharged. -/
theorem subsingleton_cohomology_of_h2
    (E : Type u) [Field E]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec (.of E)))]
    (p : ℕ)
    (h2 : ∀ (F : AbelianSheaf.{u, u + 1} (Spec (.of E))),
      IsFiniteLocallyConstant F → KilledBy p F → Subsingleton (Sheaf.H.{w} F 2))
    (F : AbelianSheaf.{u, u + 1} (Spec (.of E)))
    (hF : IsFiniteLocallyConstant F) (hp : KilledBy p F)
    (q : ℕ) (hq : 2 ≤ q) : Subsingleton (Sheaf.H.{w} F q) := by
  let : ∀ L : FiniteGaloisIntermediateField E (SeparableClosure E),
      PreservesFiniteColimits (directImage (Spec.algebraMap E L)) :=
    fun L => by
      let : IsFinite (Spec.algebraMap E L) :=
        (Scheme.FiniteEtale.FieldGalois.Arbitrary.finiteFieldCover E L).property.1
      exact Finite.finiteDirectImage_preservesFiniteColimits (Spec.algebraMap E L)
  exact subsingleton_cohomology_of_h2_of_exact_finiteCoinduction E
    (fun L G hG => isFiniteLocallyConstant_finiteFieldCoinduction E L G hG)
    p h2 F hF hp q hq

/-- Every original finite p-annihilated locally constant coefficient on an
algebraic extension of a one-variable function field over a separably closed
field has zero cohomology in degrees at least two, for p invertible in the
constant field. No replacement Galois-cohomology carrier is introduced. -/
theorem finite_cohomology_subsingleton_of_separablyClosed_ratFunc
    (K : Type u) [Field K] [IsSepClosed K] (p : ℕ) [Fact p.Prime]
    (hK : IsUnit (p : (Spec (.of K)).presheaf.obj (op ⊤)))
    (E : Type u) [Field E] [Algebra (RatFunc K) E]
    [Algebra.IsAlgebraic (RatFunc K) E]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec (.of E)))]
    (F : AbelianSheaf.{u, u + 1} (Spec (.of E)))
    (hF : IsFiniteLocallyConstant F) (hp : KilledBy p F)
    (q : ℕ) (hq : 2 ≤ q) : Subsingleton (Sheaf.H.{w} F q) :=
  subsingleton_cohomology_of_h2 E p
    (fun G hG hpG => finiteH2_subsingleton_of_separablyClosed_ratFunc K p hK E G hG hpG)
    F hF hp q hq

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
