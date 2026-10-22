/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections
public import Aglib.AlgebraicGeometry.Modules.Invertible.DualTensorEquivalence
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Projective coordinates from a family with an original line-module source

An original family `d i : D ⟶ J` with epimorphic coproduct map supplies a
canonical generating section family of `Dᵛ ⊗ J`. The construction uses the
existing actual dual evaluation isomorphism and dual-tensor equivalence.
The resulting projective map, twisting pullback comparison and coordinate
recovery retain the original index and every original morphism.

The scheme and base ring are arbitrary. Only local rank one of `D` and `J`,
finiteness of the original index and the original epimorphic row are needed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.ProjectiveSpace.FromSections.LineSource

universe u

variable {X : Scheme.{u}} (D J : X.Modules)

/-- The actual coefficient line module, using the existing structure-linear dual. -/
abbrev coefficientModule : X.Modules := tensorSheaf X (dualSheaf X D) J

/-- The canonical coefficient module is locally rank one when both original
modules are locally rank one. -/
theorem coefficientModule_locallyRankOne (hD : IsLocallyRankOne X D)
    (hJ : IsLocallyRankOne X J) : IsLocallyRankOne X (coefficientModule D J) :=
  tensorSheaf_locallyRankOne X _ _ (dualSheaf_locallyRankOne X D hD) hJ

variable (hD : IsLocallyRankOne X D)

/-- The canonical section of `Dᵛ ⊗ J` attached to the specified original map.
No frame or alternative generating family is selected. -/
def sectionOfHom (d : D ⟶ J) :
    SheafOfModules.unit X.ringCatSheaf ⟶ coefficientModule D J :=
  (dualEvaluationIso X ⟨D, hD⟩).inv ≫
    (lineBundleDualTensorEquivalence X ⟨D, hD⟩).functor.map d

/-- The exact unit-section triangle retains the original map under the actual
dual-tensor equivalence. -/
@[reassoc]
theorem sectionOfHom_triangle (d : D ⟶ J) :
    (dualEvaluationIso X ⟨D, hD⟩).hom ≫ sectionOfHom D J hD d =
      (lineBundleDualTensorEquivalence X ⟨D, hD⟩).functor.map d := by
  simp only [sectionOfHom, Iso.hom_inv_id_assoc]

/-- Generation of the canonical sections follows from the original coproduct
row. This argument uses no target rank-one or finite-index premise. -/
instance sectionFamily_epi {I : Type u} (d : I → (D ⟶ J)) [Epi (Sigma.desc d)] :
    Epi (Sigma.desc (fun i => sectionOfHom D J hD (d i))) := by
  let F := (lineBundleDualTensorEquivalence X ⟨D, hD⟩).functor
  let : F.IsLeftAdjoint :=
    (lineBundleDualTensorEquivalence X ⟨D, hD⟩).isLeftAdjoint_functor
  let : Epi (F.map (Sigma.desc d)) := inferInstance
  have hrow : Epi (Sigma.desc (fun i => F.map (d i))) := by
    rw [← sigmaComparison_map_desc F (fun _ : I => D) J d]
    infer_instance
  let a := CategoryTheory.Limits.Sigma.map
    (fun _ : I => (dualEvaluationIso X ⟨D, hD⟩).hom)
  have hfac : a ≫ Sigma.desc (fun i => sectionOfHom D J hD (d i)) =
      Sigma.desc (fun i => F.map (d i)) := by
    apply Sigma.hom_ext
    intro i
    simp only [a, Sigma.ι_map_assoc, Sigma.ι_comp_desc]
    exact sectionOfHom_triangle D J hD (d i)
  exact @epi_of_epi_fac X.Modules _ _ _ _ _ _ _ hrow hfac

section ProjectiveMap

variable {R : Type u} [CommRing R] {I : Type u} [Finite I]
variable (p : X ⟶ Spec (.of R)) (hJ : IsLocallyRankOne X J)
variable (d : I → (D ⟶ J)) [Epi (Sigma.desc d)]

/-- The actual projective map supplied by the original epimorphic family with
line-module source. Its coordinates have the original index. -/
def mapOfFamily : X ⟶ ProjectiveSpace R I :=
  mapOfFiniteFamily p (coefficientModule D J)
    (coefficientModule_locallyRankOne D J hD hJ)
    (fun i => sectionOfHom D J hD (d i))

/-- The constructed morphism retains the original map to the affine base. -/
@[reassoc]
theorem mapOfFamily_toSpec : mapOfFamily D J hD p hJ d ≫ toSpec R I = p :=
  mapOfFiniteFamily_toSpec p (coefficientModule D J)
    (coefficientModule_locallyRankOne D J hD hJ)
    (fun i => sectionOfHom D J hD (d i))

/-- The actual twisting pullback is the canonical coefficient module. -/
def twistingPullbackIso :
    (Scheme.Modules.pullback (mapOfFamily D J hD p hJ d)).obj (twistingSheaf R I 1) ≅
      coefficientModule D J :=
  twistingPullbackIsoOfFiniteFamily p (coefficientModule D J)
    (coefficientModule_locallyRankOne D J hD hJ)
    (fun i => sectionOfHom D J hD (d i))

/-- Pullback of the original native homogeneous coordinate, before applying the
coefficient-module comparison. -/
def pulledCoordinate (i : I) : SheafOfModules.unit X.ringCatSheaf ⟶
    (Scheme.Modules.pullback (mapOfFamily D J hD p hJ d)).obj (twistingSheaf R I 1) :=
  pulledCoordinateMapOfFiniteFamily p (coefficientModule D J)
    (coefficientModule_locallyRankOne D J hD hJ)
    (fun i => sectionOfHom D J hD (d i)) i

/-- Each pulled native coordinate becomes the canonical section of the same
original map, globally on the original source. -/
@[reassoc]
theorem pulledCoordinate_comp (i : I) :
    pulledCoordinate D J hD p hJ d i ≫ (twistingPullbackIso D J hD p hJ d).hom =
      sectionOfHom D J hD (d i) :=
  pulledCoordinateMapOfFiniteFamily_comp p (coefficientModule D J)
    (coefficientModule_locallyRankOne D J hD hJ)
    (fun i => sectionOfHom D J hD (d i)) i

/-- The pulled coordinate satisfies the exact native duality triangle with the
original `d i`, without choosing source or target frames. -/
@[reassoc]
theorem pulledCoordinate_triangle (i : I) :
    (dualEvaluationIso X ⟨D, hD⟩).hom ≫ pulledCoordinate D J hD p hJ d i ≫
        (twistingPullbackIso D J hD p hJ d).hom =
      (lineBundleDualTensorEquivalence X ⟨D, hD⟩).functor.map (d i) := by
  rw [pulledCoordinate_comp]
  exact sectionOfHom_triangle D J hD (d i)

/-- Recover the original-source morphism from the actual pulled coordinate via
the existing fully faithful dual-tensor equivalence. -/
def recoveredCoordinate (i : I) : D ⟶ J :=
  (lineBundleDualTensorEquivalence X ⟨D, hD⟩).functor.preimage
    ((dualEvaluationIso X ⟨D, hD⟩).hom ≫ pulledCoordinate D J hD p hJ d i ≫
      (twistingPullbackIso D J hD p hJ d).hom)

/-- Recovery is exactly the original indexed morphism, rather than an
alternative family with the same span. -/
@[simp]
theorem recoveredCoordinate_eq (i : I) : recoveredCoordinate D J hD p hJ d i = d i := by
  unfold recoveredCoordinate
  rw [pulledCoordinate_triangle]
  exact Functor.preimage_map _

/-- On any actual source and target frames, the recovered native coordinate
has the coefficient of the original map applied to the original source
generator. This also holds on every original smaller open. -/
theorem recoveredCoordinate_coefficient (U : X.Opens)
    (eD : D.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eJ : J.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    {V : X.Opens} (hV : V ≤ U) (i : I) :
    chartSectionEquiv X J U eJ V hV
        ((recoveredCoordinate D J hD p hJ d i).val.app (op V)
          ((chartSectionEquiv X D U eD V hV).symm 1)) =
      chartSectionEquiv X J U eJ V hV
        ((d i).val.app (op V) ((chartSectionEquiv X D U eD V hV).symm 1)) := by
  rw [recoveredCoordinate_eq]

end ProjectiveMap

end AlgebraicGeometry.ProjectiveSpace.FromSections.LineSource
