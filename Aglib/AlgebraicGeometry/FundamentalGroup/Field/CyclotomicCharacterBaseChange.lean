/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.Embedding
public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.CyclotomicCharacter
public import Aglib.AlgebraicGeometry.Group.ScalarExtension

/-!
# Cyclotomic character compatibility for actual field restriction

The field restriction and chosen algebraic-closure comparison are the original
ones. The characteristic-zero hypotheses and primitive-root normalization are
retained. Source: K2-018, revision e73d98b1b5c1e5abcdebf7d058e436d792b87982,
source SHA-256 e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Group.BaseChange (scalarExtensionMap)
open _root_.AlgebraicGeometry.Scheme.OverField (Base)

noncomputable section
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.PreGaloisCategory CategoryTheory.MonObj
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (fiberBaseChangeEquiv_left fiberToFinite
  fiberToFiniteBaseChangeIso forget mk)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
namespace AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.TateBaseChange
open FieldEmbeddingBaseChange
universe u
attribute [local instance] Over.cartesianMonoidalCategory
variable {F K : Type u} [Field F] [Field K] [CharZero F] [CharZero K]
variable (i : F →+* K) (n : ℕ) [NeZero n]

theorem arithmeticCharacter_restriction (g : Coefficients.ArithmeticGroup K) :
    Coefficients.arithmeticCharacter F n (fieldRestriction i g) =
      Coefficients.arithmeticCharacter K n g := by
  have h := cyclotomicCharacter_restriction i n
    ((FieldGalois.fundamentalGroupContinuousEquiv K).symm g)
  change (Field.absoluteGaloisGroup.CyclotomicCharacter.character F n)
    ((FieldGalois.fundamentalGroupContinuousEquiv F).symm
      (fieldRestriction i ((FieldGalois.fundamentalGroupContinuousEquiv K)
        ((FieldGalois.fundamentalGroupContinuousEquiv K).symm g)))) = _ at h
  rw [ContinuousMulEquiv.apply_symm_apply] at h
  exact h

end AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.TateBaseChange

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 0c53505790a76a2466fb4c9c425dfc798fda83d86aa3cafcea7d9a4043d2ab86.
Definitions, hypotheses and universes are retained modulo native names. -/
