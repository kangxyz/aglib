/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.Unbounded.GlobalSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.DirectImage

/-! # Actual unbounded compact support over a field

For an admitted separated finite-type structure morphism, compose the actual
chosen unbounded exceptional image with the original unbounded module sections.
Choice comparisons use the original exceptional comparison over a torsion ring.
This does not assert the later exceptional base-change or composition laws.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wM wΛ

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (a : X ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
  (Λ : Type (u + 1)) [CommRing Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf (Spec (.of k)) Λ)]
  [HasDerivedCategory.{wΛ} (ModuleCat.{u + 1} Λ)]

section Value

variable [HasDerivedCategory.{wM}
  (ModuleSheaf (moduleExceptionalCompactification a).Xbar Λ)]

/-- Actual unbounded `RΓ_c` for the admitted structure morphism. -/
def moduleCompactlySupportedCohomologyUnbounded :
    DerivedCategory (ModuleSheaf X Λ) ⥤ DerivedCategory (ModuleCat.{u + 1} Λ) :=
  moduleExceptionalDirectImageUnbounded a Λ ⋙
    moduleUnboundedDerivedGlobalSections (Spec (.of k)) Λ

/-- Native compactly supported homology of arbitrary unbounded input complexes. -/
def moduleCompactlySupportedCohomologyUnboundedHomology (q : ℤ) :
    DerivedCategory (ModuleSheaf X Λ) ⥤ ModuleCat.{u + 1} Λ :=
  moduleCompactlySupportedCohomologyUnbounded a Λ ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) q

end Value

variable [middleModels : ∀ C : Hom.DenseCompactification a,
  HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- Canonical compactification comparison with the exact original exceptional maps. -/
def moduleCompactlySupportedCohomologyUnboundedIso (C : Hom.DenseCompactification a) :
    moduleCompactlySupportedCohomologyUnbounded a Λ ≅
      moduleUnboundedCompactificationFunctor a Λ C ⋙
        moduleUnboundedDerivedGlobalSections (Spec (.of k)) Λ :=
  Functor.isoWhiskerRight (moduleExceptionalDirectImageUnboundedIso a Λ N hN hΛ C)
    (moduleUnboundedDerivedGlobalSections (Spec (.of k)) Λ)

/-- The forward map is the actual original exceptional comparison under native derived Γ. -/
theorem moduleCompactlySupportedCohomologyUnboundedIso_hom_app
    (C : Hom.DenseCompactification a) (K : DerivedCategory (ModuleSheaf X Λ)) :
    (moduleCompactlySupportedCohomologyUnboundedIso a Λ N hN hΛ C).hom.app K =
      (moduleUnboundedDerivedGlobalSections (Spec (.of k)) Λ).map
        ((moduleExceptionalDirectImageUnboundedIso a Λ N hN hΛ C).hom.app K) := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
