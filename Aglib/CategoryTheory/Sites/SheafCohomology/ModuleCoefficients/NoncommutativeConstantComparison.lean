/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.NoncommutativeScalars
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.NoncommutativeConstant
public import Aglib.CategoryTheory.Sites.ConstantSheaf.CompositionNaturality
public import Mathlib.RingTheory.Finiteness.Basic

/-! # Original constant-module cohomology comparison for arbitrary rings

Naturality in the whole forgetful coefficient functor, rather than false
linearity of noncentral scalar multiplication, proves that the actual
underlying constant-sheaf comparison respects the original left actions.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory
namespace ModuleCat.Sheaf
universe u v r e
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type r) [Ring R]
  [HasSheafify J AddCommGrpCat.{max u v}]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{max u v})]
attribute [local instance] hasSheafify forget_preservesSheafification

/-- Actual constant-module and constant-abelian cohomology agree linearly for
possibly noncommutative scalars, with their original comparison maps. -/
def constantUnderlyingCohomologyOfRingIso (q : ℕ) :
    constantSheaf J (ModuleCat.{max u v} R) ⋙ cohomologyOfRing J R q ≅
      constantCohomologyOfRing J R q := by
  let H := CategoryTheory.Sheaf.functorH J q
  refine NatIso.ofComponents (fun M => ModuleCat.isoMk
    (M := (cohomologyOfRing J R q).obj
      ((constantSheaf J (ModuleCat.{max u v} R)).obj M))
    (N := (constantCohomologyOfRing J R q).obj M)
    (H.mapIso ((constantUnderlyingIso R J).app M)) ?_) ?_
  · intro a
    have h := constantCommuteCompose_coefficient_naturality J
      (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})
      (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})
      (ModuleCat.forgetScalar R a) M
    ext x
    have hh := congrArg H.map h.symm
    simp only [Functor.map_comp] at hh
    exact ConcreteCategory.congr_hom hh x
  · intro M N f
    apply (forget₂ (ModuleCat.{e} R) AddCommGrpCat.{e}).map_injective
    exact (Functor.isoWhiskerRight (constantUnderlyingIso R J) H).hom.naturality f

/-- The forward comparison is the original cohomology map, not a chosen equivalence. -/
theorem constantUnderlyingCohomologyOfRingIso_hom_apply (q : ℕ)
    (M : ModuleCat.{max u v} R)
    (x : (cohomologyOfRing J R q).obj
      ((constantSheaf J (ModuleCat.{max u v} R)).obj M)) :
    (constantUnderlyingCohomologyOfRingIso J R q).hom.app M x =
      CategoryTheory.Sheaf.H.map ((constantUnderlyingIso R J).hom.app M) q x := rfl

/-- Finite generation transports through the actual scalar-compatible map,
without commutativity or finite additive cardinality. -/
theorem finite_cohomologyOfRing_constant_iff (q : ℕ) (M : ModuleCat.{max u v} R) :
    Module.Finite R
        ((cohomologyOfRing J R q).obj ((constantSheaf J (ModuleCat.{max u v} R)).obj M)) ↔
      Module.Finite R ((constantCohomologyOfRing J R q).obj M) :=
  Module.Finite.equiv_iff ((constantUnderlyingCohomologyOfRingIso J R q).app M).toLinearEquiv

end ModuleCat.Sheaf
