/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IdealPowers.ThickeningTransitions
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ThickeningCohomologyComparison
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Original cohomology on actual ideal thickenings

The coefficient quotient is first identified with the actual closed direct
image. Affine pushforward then compares original cohomology, with the same
geometric forward arrow. Original transition maps are retained before forming
any inverse limit.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules)

local notation "α" => idealThickeningBaseScalar f

/-- Original cohomology on the actual thickening, with its induced structural
base-ring action (not an abstractly transported action). -/
abbrev idealThickeningCohomology (J : Ideal A) (p : ℕ) : ModuleCat.{u + 1} A :=
  (moduleCohomologyFunctorOfHom (idealThickeningSpace f J)
    ((idealThickeningι f J).appTop.hom.comp α) p).obj (idealThickeningCoefficient f F J)

/-- Scalar normalization for the original transition between thickenings. -/
theorem idealThickeningMap_scalars {J K : Ideal A} (h : J ≤ K) :
    (idealThickeningMap f h).appTop.hom.comp ((idealThickeningι f J).appTop.hom.comp α) =
      (idealThickeningι f K).appTop.hom.comp α := by
  rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop,
    idealThickeningMap_ι]

/-- The actual geometric cohomology transition, with the original coefficient
arrow and the original structural action. -/
def idealThickeningCohomologyMap {J K : Ideal A} (h : J ≤ K) (p : ℕ) :
    idealThickeningCohomology f F J p ⟶ idealThickeningCohomology f F K p :=
  moduleCohomologyAlongHom (idealThickeningMap f h)
    ((idealThickeningι f J).appTop.hom.comp α)
    ((idealThickeningι f K).appTop.hom.comp α) (idealThickeningMap_scalars f h)
    (idealThickeningCoefficientMap f F h) p

theorem idealThickeningCohomologyMap_apply {J K : Ideal A} (h : J ≤ K) (p : ℕ)
    (x : idealThickeningCohomology f F J p) :
    idealThickeningCohomologyMap f F h p x =
      moduleCohomologyMapAlong (idealThickeningMap f h)
        (idealThickeningCoefficientMap f F h) p x :=
  moduleCohomologyAlongHom_apply _ _ _ _ _ _ _

/-- The actual quotient-base inclusion is a closed immersion. -/
instance idealThickeningι_isClosedImmersion (J : Ideal A) :
    IsClosedImmersion (idealThickeningι f J) := by
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of A) J
  exact inferInstanceAs (IsClosedImmersion
    (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))))

variable [CompactSpace X] [X.IsSeparated] [F.IsQuasicoherent]

/-- Quotient cohomology is original cohomology on the actual thickening,
through the original coefficient comparison and affine pushforward map. -/
def idealQuotientThickeningCohomologyEquiv (J : Ideal A) (p : ℕ) :
    (moduleCohomologyFunctorOfHom X α p).obj (idealQuotient X α F J) ≃ₗ[A]
      idealThickeningCohomology f F J p :=
  moduleCohomologyCoefficientAffineEquiv (idealThickeningι f J)
    (idealThickeningCoefficient f F J) (idealQuotient X α F J)
    (idealQuotientThickeningIso f F J) α p

/-- The stagewise forward map is the actual geometric cohomology map. -/
theorem idealQuotientThickeningCohomologyEquiv_apply (J : Ideal A) (p : ℕ)
    (x : (moduleCohomologyFunctorOfHom X α p).obj (idealQuotient X α F J)) :
    idealQuotientThickeningCohomologyEquiv f F J p x =
      moduleCohomologyMapAlong (idealThickeningι f J) (idealQuotientThickeningIso f F J).hom
        p x :=
  moduleCohomologyCoefficientAffineEquiv_apply _ _ _ _ _ _ _

/-- The stagewise comparison intertwines the original quotient map with the
actual geometric cohomology transition between the thickenings. -/
theorem idealQuotientThickeningCohomologyEquiv_naturality {J K : Ideal A} (h : J ≤ K)
    (p : ℕ) :
    cohomologyEquivNaturality (idealQuotientThickeningCohomologyEquiv f F J p)
      (idealQuotientThickeningCohomologyEquiv f F K p)
      (idealThickeningCohomologyMap f F h p)
      ((moduleCohomologyFunctorOfHom X α p).map (idealQuotientMap X α F h)) := by
  exact moduleCohomologyPullbackTriangleEquiv_naturality
    (idealThickeningι f J) (idealThickeningι f K) (idealThickeningMap f h)
    (idealThickeningMap_ι f h) F (idealQuotient X α F J) (idealQuotient X α F K)
    (idealQuotientThickeningIso f F J) (idealQuotientThickeningIso f F K)
    (idealQuotientMap X α F h) (idealQuotientThickeningIso_naturality f F h).symm
    α (idealThickeningMap_scalars f h) p

/-- The original reduction to a thickening is exactly geometric pullback. -/
theorem idealQuotientThickeningCohomologyEquiv_reduction (J : Ideal A) (p : ℕ)
    (x : (moduleCohomologyFunctorOfHom X α p).obj F) :
    idealQuotientThickeningCohomologyEquiv f F J p
      ((moduleCohomologyFunctorOfHom X α p).map (idealQuotientπ X α F J) x) =
        moduleCohomologyPullback (idealThickeningι f J) F p x := by
  rw [idealQuotientThickeningCohomologyEquiv_apply]
  change moduleCohomologyMapAlong _ _ p
    (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map
      (idealQuotientπ X α F J)) p x) = _
  rw [← moduleCohomologyMapAlong_precomp, idealQuotientπ_thickeningIso_hom]
  rfl

end AlgebraicGeometry.Scheme.Cohomology
