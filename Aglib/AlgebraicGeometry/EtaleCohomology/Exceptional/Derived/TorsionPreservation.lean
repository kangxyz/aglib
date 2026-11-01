/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Serre
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.HigherTorsion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnderlyingTorsion

/-!
# Internal torsion under original bounded-below direct image

The original higher direct images of a qcqs morphism preserve internal torsion.
The abstract Serre-property Postnikov theorem therefore gives the same result
on every homology sheaf of the native bounded-below derived direct image.
Original derived scalar forgetting transports this to genuine module sheaves.
No common annihilator, finite amplitude, properness, or coefficient-ring
Noetherian hypothesis is imposed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open ZeroObject

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u wX wS wMX wMS

attribute [local instance] hasSheafifyLarge

/-- Internal torsion is a Serre property on the actual abelian etale sheaves. -/
instance isSerreClass_isTorsion (X : Scheme.{u}) :
    ObjectProperty.IsSerreClass (IsTorsion X) where
  exists_zero := ⟨0, isZero_zero _, by
    apply isTorsion_of_geometricStalks
    intro Ω _ _ η
    let T := (pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})
    let : HasFilteredColimitsOfSize.{u, u} AddCommGrpCat.{u + 1} :=
      hasFilteredColimitsOfSize_of_univLE.{u, u, u + 1, u + 1}
    let : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
      AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
    let : T.Additive := Functor.additive_of_preserves_binary_products T
    let : Subsingleton (T.obj 0) :=
      AddCommGrpCat.subsingleton_of_isZero (T.map_isZero (isZero_zero _))
    intro x
    rw [Subsingleton.elim x 0]
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨1, by decide, by simp⟩⟩
  prop_of_mono f _ h := h.of_mono f
  prop_of_epi f _ h := h.of_epi f
  prop_X₂_of_shortExact hS h₁ h₃ := by
    let : ObjectProperty.Small.{u + 1} (FibrewiseClosed.pointFamily (𝟙 X)) := by
      unfold FibrewiseClosed.pointFamily
      infer_instance
    exact Sheaf.IsTorsion.extension (FibrewiseClosed.pointFamily (𝟙 X))
      (FibrewiseClosed.pointFamily_isConservative (𝟙 X)) _ hS h₁ h₃

section Abelian

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
  [HasDerivedCategory.{wX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wS} (AbelianSheaf.{u, u + 1} S)]

/-- Qcqs direct image preserves internal torsion in all original `D+` homology
sheaves, by ordinary higher-image torsion and abstract Serre devissage. -/
theorem derivedDirectImage_isTorsion_homology
    (K : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X))
    (hK : ∀ i : ℤ, IsTorsion X
      ((DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} X) i).obj K))
    (n : ℤ) : IsTorsion S
      ((DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) n).obj
        ((derivedDirectImage f).obj K)) :=
  (directImage f).homologyProperty_rightDerivedFunctorPlus (IsTorsion S) K
    (fun i q => higherDirectImage_isTorsion f q _ (hK i)) n

end Abelian

namespace Coefficients

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]

/-- The original module-derived direct image of a qcqs morphism preserves the
actual torsion-cohomology range. The two module realizations remain independent;
the auxiliary abelian realizations are selected only inside the proof. -/
theorem moduleDerivedDirectImage_preservesTorsionCohomology
    (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (hK : moduleTorsionCohomologyPlus X Λ K) :
    moduleTorsionCohomologyPlus S Λ ((moduleDerivedDirectImage Λ f).obj K) := by
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S)
  apply (moduleTorsionCohomologyPlus_iff_underlying S Λ _).mpr
  intro n
  let e := (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) n).mapIso
    ((moduleDerivedDirectImageUnderlyingIso Λ f).app K)
  exact (derivedDirectImage_isTorsion_homology f ((moduleDerivedUnderlying Λ X).obj K)
    ((moduleTorsionCohomologyPlus_iff_underlying X Λ K).mp hK) n).of_mono e.hom

end Coefficients

end AlgebraicGeometry.Scheme.EtaleCohomology
