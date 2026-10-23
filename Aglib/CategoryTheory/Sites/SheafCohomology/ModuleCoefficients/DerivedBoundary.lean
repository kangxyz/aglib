/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedComparison
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.ExtBoundary

/-!
# Long exact sequences of native derived coefficient sections

These are native right-derived groups. Their connecting maps are chosen using
the canonical original-Ext normalization, not compared with an independently
preselected `Functor.rightDerived` boundary. The resulting long exact sequence
commutes with the original abelian extension-class boundary.

The comparison in `cohomologyMap_derivedScalarBoundary` is literally the
composition defining `derivedScalarCohomologyAddEquiv` and its large-scalar
variant: native derived sections to original module Ext, followed by the
original scalar-forgetting `cohomologyMap`. The square is stated on these
original maps rather than on a redundant equivalence alias.
-/

@[expose] public noncomputable section

universe u v r w eM eA s

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf.ModuleCoefficients

section General

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {T : C} (hT : IsTerminal T) (R : Sheaf J RingCat.{r})
  (Λ : Type s) [Ring Λ] (α : Λ →+* R.obj.obj (op T))
  [HasSheafify J AddCommGrpCat.{max u v r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
  [EnoughInjectives (SheafOfModules.{max u v r w} R)]
  [hExtM : HasExt.{eM} (SheafOfModules.{max u v r w} R)]

/-- Forget scalars only after taking the actual native derived section functor. -/
def derivedScalarAdditiveSections (n : ℕ) :
    SheafOfModules.{max u v r w} R ⥤ AddCommGrpCat.{max u v r w} :=
  (scalarTerminalSections.{u, v, r, w, s} R Λ α).rightDerived n ⋙
    forget₂ (ModuleCat.{max u v r w} Λ) AddCommGrpCat

/-- The chosen connecting homomorphism on native coefficient-valued derived sections. -/
def derivedScalarBoundary (S : ShortComplex (SheafOfModules.{max u v r w} R))
    (hS : S.ShortExact) (n : ℕ) :
    ((scalarTerminalSections.{u, v, r, w, s} R Λ α).rightDerived n).obj S.X₃ →+
      ((scalarTerminalSections.{u, v, r, w, s} R Λ α).rightDerived (n + 1)).obj S.X₁ :=
  moduleNormalizedExtBoundary _
    (fun n => (scalarTerminalSections.{u, v, r, w, s} R Λ α).rightDerived n)
    (derivedScalarTerminalSectionsExtAddEquiv.{u, v, r, w, eM, s} hT R Λ α) S hS n

/-- Its normalization is the original covariant extension-class boundary, with no sign change. -/
theorem derivedScalarBoundary_apply (S : ShortComplex (SheafOfModules.{max u v r w} R))
    (hS : S.ShortExact) (n : ℕ)
    (x : ((scalarTerminalSections.{u, v, r, w, s} R Λ α).rightDerived n).obj S.X₃) :
    derivedScalarTerminalSectionsExtAddEquiv.{u, v, r, w, eM, s} hT R Λ α S.X₁ (n + 1)
        (derivedScalarBoundary.{u, v, r, w, eM, s} hT R Λ α S hS n x) =
      (derivedScalarTerminalSectionsExtAddEquiv.{u, v, r, w, eM, s}
        hT R Λ α S.X₃ n x).comp hS.extClass rfl := by
  exact moduleNormalizedExtBoundary_apply_of_eq (SheafOfModules.liftedUnit.{u, v, max u v w, r} R)
    (fun n => (scalarTerminalSections.{u, v, r, w, s} R Λ α).rightDerived n)
    (derivedScalarTerminalSectionsExtAddEquiv.{u, v, r, w, eM, s} hT R Λ α) S hS n
    (derivedScalarBoundary.{u, v, r, w, eM, s} hT R Λ α S hS n) rfl x
    (derivedScalarTerminalSectionsExtAddEquiv.{u, v, r, w, eM, s}
      hT R Λ α S.X₁ (n + 1)) rfl
    (derivedScalarBoundary.{u, v, r, w, eM, s} hT R Λ α S hS n x) rfl
    (derivedScalarTerminalSectionsExtAddEquiv.{u, v, r, w, eM, s}
      hT R Λ α S.X₃ n) rfl

include hT hExtM

/-- Injectivity at the start of the long exact sequence, for native degree-zero maps. -/
theorem derivedScalarSections_injective_zero
    {M N : SheafOfModules.{max u v r w} R} (f : M ⟶ N) [Mono f] :
    Function.Injective (((scalarTerminalSections.{u, v, r, w, s} R Λ α).rightDerived 0).map f) :=
  moduleNormalizedExtBoundary_injective_zero _
    (fun n => (scalarTerminalSections.{u, v, r, w, s} R Λ α).rightDerived n)
    (derivedScalarTerminalSectionsExtAddEquiv.{u, v, r, w, eM, s} hT R Λ α)
    (fun f n x => derivedScalarTerminalSectionsExtAddEquiv_naturality.{u, v, r, w, eM, s}
      hT R Λ α f n x) f

/-- Exactness at the middle coefficient object for the actual derived section maps. -/
theorem derivedScalarBoundary_exact₂ (S : ShortComplex (SheafOfModules.{max u v r w} R))
    (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (((scalarTerminalSections.{u, v, r, w, s} R Λ α).rightDerived n).map S.f)
      (((scalarTerminalSections.{u, v, r, w, s} R Λ α).rightDerived n).map S.g) :=
  moduleNormalizedExtBoundary_exact₂ _
    (fun n => (scalarTerminalSections.{u, v, r, w, s} R Λ α).rightDerived n)
    (derivedScalarTerminalSectionsExtAddEquiv.{u, v, r, w, eM, s} hT R Λ α)
    (fun f n x => derivedScalarTerminalSectionsExtAddEquiv_naturality.{u, v, r, w, eM, s}
      hT R Λ α f n x)
    S hS n

/-- Exactness before the chosen connecting homomorphism. -/
theorem derivedScalarBoundary_exact₃ (S : ShortComplex (SheafOfModules.{max u v r w} R))
    (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (((scalarTerminalSections.{u, v, r, w, s} R Λ α).rightDerived n).map S.g)
      (derivedScalarBoundary.{u, v, r, w, eM, s} hT R Λ α S hS n) :=
  moduleNormalizedExtBoundary_exact₃ _
    (fun n => (scalarTerminalSections.{u, v, r, w, s} R Λ α).rightDerived n)
    (derivedScalarTerminalSectionsExtAddEquiv.{u, v, r, w, eM, s} hT R Λ α)
    (fun f n x => derivedScalarTerminalSectionsExtAddEquiv_naturality.{u, v, r, w, eM, s}
      hT R Λ α f n x)
    S hS n

/-- Exactness after the chosen connecting homomorphism. -/
theorem derivedScalarBoundary_exact₁ (S : ShortComplex (SheafOfModules.{max u v r w} R))
    (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (derivedScalarBoundary.{u, v, r, w, eM, s} hT R Λ α S hS n)
      (((scalarTerminalSections.{u, v, r, w, s} R Λ α).rightDerived (n + 1)).map S.f) :=
  moduleNormalizedExtBoundary_exact₁ _
    (fun n => (scalarTerminalSections.{u, v, r, w, s} R Λ α).rightDerived n)
    (derivedScalarTerminalSectionsExtAddEquiv.{u, v, r, w, eM, s} hT R Λ α)
    (fun f n x => derivedScalarTerminalSectionsExtAddEquiv_naturality.{u, v, r, w, eM, s}
      hT R Λ α f n x)
    S hS n

variable [HasExt.{eA} (Sheaf J AddCommGrpCat.{max u v r w})]

/-- Scalar forgetting carries the chosen native derived boundary to the original abelian one. -/
theorem cohomologyMap_derivedScalarBoundary
    (S : ShortComplex (SheafOfModules.{max u v r w} R)) (hS : S.ShortExact) (n : ℕ)
    (x : ((scalarTerminalSections.{u, v, r, w, s} R Λ α).rightDerived n).obj S.X₃) :
    cohomologyMap.{u, v, r, max u v w, eM, eA} hT R S.X₁ (n + 1)
        (derivedScalarTerminalSectionsExtAddEquiv.{u, v, r, w, eM, s} hT R Λ α S.X₁ (n + 1)
          (derivedScalarBoundary.{u, v, r, w, eM, s} hT R Λ α S hS n x)) =
      (cohomologyMap.{u, v, r, max u v w, eM, eA} hT R S.X₃ n
        (derivedScalarTerminalSectionsExtAddEquiv.{u, v, r, w, eM, s} hT R Λ α S.X₃ n x)).comp
          (hS.map_of_exact (SheafOfModules.toSheaf R)).extClass rfl :=
  (congrArg (cohomologyMap.{u, v, r, max u v w, eM, eA} hT R S.X₁ (n + 1))
    (derivedScalarBoundary_apply.{u, v, r, w, eM, s} hT R Λ α S hS n x)).trans
      (cohomologyMap_connecting.{u, v, r, max u v w, eM, eA} hT R S hS n _)

end General

end CategoryTheory.Sheaf.ModuleCoefficients
