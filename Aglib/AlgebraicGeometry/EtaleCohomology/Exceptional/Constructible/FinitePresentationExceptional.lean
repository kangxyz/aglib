/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.FinitePresentationDerived
public import Aglib.AlgebraicGeometry.Compactification.FinitePresentationQCQS
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.Densification
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.ModelComparisonCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.DirectImage

/-! # Original exceptional constructibility over arbitrary qcqs bases

The finite-presentation compactification is constructed from the actual base
approximation. Its value is transported through original densification and
common-refinement transitions to the unchanged chosen exceptional functor.
No finite-presentation claim is made about the chosen schematic closure.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wM
attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

/-- Genuine constructibility of the original chosen exceptional image over a
qcqs base, for a separated finitely presented map and left-Noetherian Z/n ring. -/
theorem moduleExceptionalHomology_finitePresentation_isConstructible
    {X S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wM} (ModuleSheaf (moduleExceptionalCompactification f).Xbar Λ)]
    (N : ℕ) (hN : 0 < N) (hΛ : (N : Λ) = 0)
    (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory)
    (hK : ∀ i : ℤ, Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence X Λ).inverse.obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf X Λ) i).obj K.obj))) (n : ℤ) :
    Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) n).obj
          ((moduleExceptionalDirectImagePlus f Λ).obj K))) := by
  obtain ⟨C, hC⟩ := Hom.exists_finitePresentation_compactification_of_qcqs f
  let : LocallyOfFinitePresentation C.p := hC
  have : QuasiCompact (C.j ≫ C.p) := by rw [C.fac]; infer_instance
  let : QuasiCompact C.j := QuasiCompact.of_comp C.j C.p
  let D := Hom.Compactification.densify C
  let E := moduleExceptionalCompactification f
  let W := Hom.DenseCompactification.common D E
  let := HasDerivedCategory.standard (ModuleSheaf C.Xbar Λ)
  let := HasDerivedCategory.standard (ModuleSheaf D.Xbar Λ)
  let := HasDerivedCategory.standard (ModuleSheaf W.Xbar Λ)
  have h := moduleCompactificationHomology_finitePresentation_isConstructible
    C Λ N hN hΛ K.obj hK n
  let e : (moduleRawCompactificationFunctor C Λ).obj K ≅
      (moduleExceptionalDirectImagePlus f Λ).obj K :=
    (moduleCompactificationDensificationIso C Λ).app K ≪≫
      (asIso (moduleCompactificationMixedTransition Λ
        (Hom.DenseCompactification.commonToLeft D E))).app K ≪≫
      ((asIso (moduleCompactificationMixedTransition Λ
        (Hom.DenseCompactification.commonToRight D E))).app K).symm
  exact (Constructible.Modules.isConstructible_iff_of_iso
    ((moduleSheafEquivalence S Λ).inverse.mapIso
      ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) n).mapIso e))).mp h

end AlgebraicGeometry.Scheme.EtaleCohomology
