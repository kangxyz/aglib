/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Basic
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Locality
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Coherent adic systems for an arbitrary ideal sheaf

The objects are native inverse diagrams on the fixed scheme. Reduction uses the
original pullback/pushforward adjunction unit for the actual closed thickening.
The ideal need not come from global functions or from the base. Index zero is
the zero quotient, and index one is the special fibre.

No abelian structure is inherited from the ambient diagram category: its
levelwise kernels need not satisfy the reduction condition.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

variable (X : Scheme.{u}) (K : X.IdealSheafData)

/-- The actual quotient functor for a closed ideal-sheaf thickening. -/
abbrev idealSheafQuotientFunctor : X.Modules ⥤ X.Modules :=
  pullback K.subschemeι ⋙ pushforward K.subschemeι

/-- The original quotient unit for a closed ideal-sheaf thickening. -/
abbrev idealSheafQuotientUnit : 𝟭 X.Modules ⟶ idealSheafQuotientFunctor X K :=
  (pullbackPushforwardAdjunction K.subschemeι).unit

/-- The coherent, annihilation, and canonical reduction conditions for an
arbitrary ideal sheaf and a native inverse diagram. -/
structure IsAdicSystem (F : ℕᵒᵖ ⥤ X.Modules) : Prop where
  coherent : ∀ n : ℕ, QuasiCoherent.affineLocallyFiniteType X (F.obj (op n))
  annihilated : ∀ n : ℕ, killedByIdealSheaf (K ^ n) (F.obj (op n))
  reduction : ∀ n : ℕ, ∃ e :
      (idealSheafQuotientFunctor X (K ^ n)).obj (F.obj (op (n + 1))) ≅ F.obj (op n),
    (idealSheafQuotientUnit X (K ^ n)).app (F.obj (op (n + 1))) ≫ e.hom =
      F.map (homOfLE (Nat.le_succ n)).op

/-- Formal coherent modules along an arbitrary ideal sheaf, with actual
natural transformations as morphisms. -/
@[nolint unusedArguments]
abbrev AdicSystem [IsLocallyNoetherian X] :=
  ObjectProperty.FullSubcategory (IsAdicSystem X K)

variable [_hX : IsLocallyNoetherian X]

/-- Forget only the adic conditions, retaining the original inverse diagram. -/
abbrev adicSystemToDiagram : AdicSystem X K ⥤ (ℕᵒᵖ ⥤ X.Modules) :=
  ObjectProperty.ι (IsAdicSystem X K)

namespace AdicSystem

variable {X K} (F : AdicSystem X K)

/-- The original successor transition of a coherent formal system. -/
abbrev transition (n : ℕ) : F.obj.obj (op (n + 1)) ⟶ F.obj.obj (op n) :=
  F.obj.map (homOfLE (Nat.le_succ n)).op

/-- The supplied reduction isomorphism, retaining the original quotient unit. -/
def reductionIso (n : ℕ) :
    (idealSheafQuotientFunctor X (K ^ n)).obj (F.obj.obj (op (n + 1))) ≅
      F.obj.obj (op n) :=
  (F.property.reduction n).choose

@[reassoc (attr := simp)]
theorem unit_reductionIso_hom (n : ℕ) :
    (idealSheafQuotientUnit X (K ^ n)).app (F.obj.obj (op (n + 1))) ≫
      (F.reductionIso n).hom = F.transition n :=
  (F.property.reduction n).choose_spec

/-- Index zero is genuinely zero, rather than an extra unconstrained term. -/
theorem zero_isZero {X : Scheme.{u}} {K : X.IdealSheafData}
    [IsLocallyNoetherian X] (F : AdicSystem X K) : IsZero (F.obj.obj (op 0)) := by
  apply (Scheme.Modules.isZero_iff_stalks _).mpr
  intro x
  have hz := killedByIdealSheaf_isZero_stalk_of_not_mem_support (K ^ 0)
    (F.obj.obj (op 0)) (F.property.annihilated 0) x (by
      change x ∉ (∅ : Set X)
      exact Set.notMem_empty x)
  exact ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat.{u}).map_isZero hz).of_iso
    ((moduleStalkForgetIso X x).app (F.obj.obj (op 0))).symm

/-- Morphisms of coherent adic systems commute with the original reductions. -/
@[reassoc]
theorem transition_naturality {G : AdicSystem X K} (f : F ⟶ G) (n : ℕ) :
    F.transition n ≫ f.hom.app (op n) =
      f.hom.app (op (n + 1)) ≫ G.transition n :=
  f.hom.naturality _

end AdicSystem

end AlgebraicGeometry.Scheme.Modules.Coherent
