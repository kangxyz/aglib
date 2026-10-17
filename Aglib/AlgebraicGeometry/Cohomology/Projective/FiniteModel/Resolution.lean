/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KProjective.Representative
public import Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteModel

/-!
# An actual projective-model map to original injective-resolution sections

The canonical native derived-global-sections model and the original derived
unit on an actual injective resolution give a displayed derived isomorphism
to the original section complex. Native K-projectivity constructs an actual
quasi-isomorphism representative whose literal `Q.map` is that same original
comparison. No projectivity of the resolution section terms is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HomologicalComplex

namespace AlgebraicGeometry.Scheme.Cohomology.ProjectiveCohomologyModel

variable {R : Type u} [CommRing R] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace R ι} [IsClosedImmersion i]
  {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules} [M.IsQuasicoherent] {n : ℕ}
  (D : ProjectiveCohomologyModel R ι i f M n) (e : ι ≃ Fin (n + 1))
  (I : InjectiveResolution M)

/-- The standard derived-category structure on the indicated module category. -/
local instance resolutionModelSource : HasDerivedCategory.{u + 1} X.Modules :=
  HasDerivedCategory.standard _

/-- The standard derived-category structure on the indicated module category. -/
local instance resolutionModelTarget : HasDerivedCategory.{u + 1} (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

/-- The original native model comparison followed by the inverse original
derived-unit comparison on the actual module injective resolution. -/
def resolutionSectionsDerivedIsoPlus :
    DerivedCategory.Plus.Q.obj D.toPlus ≅
      DerivedCategory.Plus.Q.obj
        ((moduleGlobalSectionsFunctorOfHom X
          (f.appTop.hom.comp
            (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).mapCochainComplexPlus.obj
            I.cochainComplexPlus) :=
  D.derivedGlobalSectionsIso e I ≪≫
    (InjectiveResolution.rightDerivedFunctorPlusIso
      (moduleGlobalSectionsFunctorOfHom X
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) I).symm

/-- The section-complex comparison retains the actual original Cech
model comparison and the original injective-resolution derived unit. -/
theorem resolutionSectionsDerivedIsoPlus_hom :
    (D.resolutionSectionsDerivedIsoPlus e I).hom =
      (D.derivedGlobalSectionsIso e I).hom ≫
        (InjectiveResolution.rightDerivedFunctorPlusIso
          (moduleGlobalSectionsFunctorOfHom X
            (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) I).inv := rfl

/-- The same original bounded-below comparison in the native ambient
quasi-isomorphism localization, using its two original inclusion factors. -/
def resolutionSectionsDerivedIso :
    DerivedCategory.Q.obj D.complex ≅
      DerivedCategory.Q.obj
        (((moduleGlobalSectionsFunctorOfHom X
          (f.appTop.hom.comp
            (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).mapCochainComplexPlus.obj
            I.cochainComplexPlus).obj) :=
  ((DerivedCategory.Plus.QCompιIso (ModuleCat.{u} R)).app D.toPlus).symm ≪≫
    (DerivedCategory.Plus.ι).mapIso (D.resolutionSectionsDerivedIsoPlus e I) ≪≫
      (DerivedCategory.Plus.QCompιIso (ModuleCat.{u} R)).app
        ((moduleGlobalSectionsFunctorOfHom X
          (f.appTop.hom.comp
            (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).mapCochainComplexPlus.obj
            I.cochainComplexPlus)

/-- The original derived section comparison has an actual chain
quasi-isomorphism representative, with precisely its original `Q.map` value. -/
theorem exists_resolutionSectionsComparison :
    ∃ u : D.complex ⟶
        (((moduleGlobalSectionsFunctorOfHom X
          (f.appTop.hom.comp
            (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).mapCochainComplexPlus.obj
            I.cochainComplexPlus).obj),
      QuasiIso u ∧ DerivedCategory.Q.map u = (D.resolutionSectionsDerivedIso e I).hom := by
  let := D.upperBound
  let (j : ℤ) : Module.Projective R (D.complex.X j) := D.projective_X j
  have (j : ℤ) : Projective (D.complex.X j) := inferInstance
  let : D.complex.IsKProjective :=
    CochainComplex.isKProjective_of_projective D.complex (n : ℤ)
  exact CochainComplex.IsKProjective.exists_quasiIso_of_derivedIso D.complex _
    (D.resolutionSectionsDerivedIso e I)

/-- A chosen actual chain representative of the fixed original derived
section comparison. Choice affects no asserted derived map. -/
def resolutionSectionsComparison : D.complex ⟶
    (((moduleGlobalSectionsFunctorOfHom X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).mapCochainComplexPlus.obj
        I.cochainComplexPlus).obj) :=
  Classical.choose (D.exists_resolutionSectionsComparison e I)

/-- This same actual chain representative is a quasi-isomorphism. -/
theorem resolutionSectionsComparison_quasiIso : QuasiIso (D.resolutionSectionsComparison e I) :=
  (Classical.choose_spec (D.exists_resolutionSectionsComparison e I)).1

/-- The actual chain representative retains the original derived
Cech/injective-resolution comparison under literal native localization. -/
theorem resolutionSectionsComparison_Q_map :
    DerivedCategory.Q.map (D.resolutionSectionsComparison e I) =
      (D.resolutionSectionsDerivedIso e I).hom :=
  (Classical.choose_spec (D.exists_resolutionSectionsComparison e I)).2

end AlgebraicGeometry.Scheme.Cohomology.ProjectiveCohomologyModel
