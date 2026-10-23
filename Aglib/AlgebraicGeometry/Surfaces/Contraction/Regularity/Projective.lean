/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Contraction.FormalNeighborhood.StructureMap
public import Aglib.AlgebraicGeometry.Surfaces.Contraction.Regularity
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Line.PositiveTwist
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Smooth
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Regularity
public import Aglib.RingTheory.RegularLocalRing.TwoGenerators

/-!
# Regularity at the original point of a projective Cartier image

The original first-order sections determine the maximal ideal of the original
image stalk and show that it is nonprincipal. The actual proper local source
supplies normality through the proved original structure-map bijection. The
native two-generator criterion then gives dimension two and regularity of that
same stalk. The residue field and all presentation maps are retained.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Surfaces.Contraction.FormalNeighborhood

universe u

namespace AlgebraicGeometry.Scheme.Surfaces.Contraction.CartierProjectivePresentation

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {ι : Type u} {X : Scheme.{u}} {p : X ⟶ ProjectiveSpace A ι} [IsClosedImmersion p]
  {k : Type u} [Field k]
  (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X) [IsClosedImmersion i]
  (hI : IsLocallyRankOne X (Hom.idealModule i)) (H : LineBundle X)
  {eP : H.val ≅ (Scheme.Modules.pullback p).obj (twistingSheaf A ι 1)} (d : ℕ)
  {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)
  (eH : (Scheme.Modules.pullback i).obj H.val ≅
    twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual projective image stalk at the original full residue-field point
is a regular local ring of dimension two, from the original first-order lifts.
Its structure-map bijectivity, normality and dimension are conclusions. -/
theorem pointLocalRing_regularLocal_dimension_two
    (r : ℕ) (eι : ι ≃ Fin (r + 1)) (hn2 : 2 ≤ n * d) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
    (hρ : Function.Surjective ((cartierResidueMap i hI H d eI eH n).val.app (op ⊤)))
    (t : ULift.{u} (Fin 2) → (SheafOfModules.unit X.ringCatSheaf ⟶
      (cartierPowerTwist i hI H n (n * d - 2 + 1)).val))
    (ht : ∀ a, t a ≫ (cartierStepSequence i hI
      (cartierPowerTwist i hI H n (n * d - 2))).g =
        firstOrderQuotientCoordinate i hI H d eI eH n hn2 a)
    (q : ULift.{u} (Fin 2) → F.index)
    (hq : ∀ a, F.sections (q a) = firstOrderCartierImage i hI H d n hn2 (t a)) :
    ringKrullDim (pointLocalRing (F.residueToImage eI eH j₀ h₀)) = 2 ∧
      IsRegularLocalRing (pointLocalRing (F.residueToImage eI eH j₀ h₀)) := by
  let _ : Finite ι := Finite.of_equiv _ eι.symm
  let _ : Finite F.index := F.finiteIndex
  let _ : IsProper F.toImage := F.toImage_isProper r eι
  let _ : IsLocallyNoetherian F.image :=
    LocallyOfFiniteType.isLocallyNoetherian F.imageInclusion
  let c := F.residueToImage eI eH j₀ h₀
  let _ : IsClosedImmersion c :=
    F.residueToImage_isClosedImmersion eI eH (Field.toIsField k) j₀ h₀ hρ
  let _ : IsNoetherianRing (pointLocalRing c) := inferInstance
  have hker : c.ker.comap F.toImage = i.ker :=
    F.pointIdeal_comap_eq eI eH r eι (Field.toIsField k) hn2 j₀ h₀ hρ t ht q hq
  have hC : RegularStalks (ProjectiveSpace k (ULift.{u} (Fin 2))) := by
    let _ : SmoothOfRelativeDimension 1 (toSpec k (ULift.{u} (Fin 2))) :=
      ProjectiveSpace.toSpec_smoothOfRelativeDimension k (ULift.{u} (Fin 2)) 1 Equiv.ulift
    exact Scheme.smoothFieldRegularity k _ (toSpec k (ULift.{u} (Fin 2)))
      (SmoothOfRelativeDimension.smooth 1 _)
  let _ : IsIntegral (ProjectiveSpace k (ULift.{u} (Fin 2))) :=
    ProjectiveSpace.Line.nativeIntegral k
  let _ : ConnectedSpace (ProjectiveSpace k (ULift.{u} (Fin 2))) := inferInstance
  obtain ⟨hbij, hgen⟩ := selectedLocalStructureAndParameters
    i hI H d F eI eH r eι hn2 j₀ h₀ hρ t ht q hq
  have hnormal := pointLocalRing_isDomain_and_isIntegrallyClosed_of_localStructureHom_bijective
    c F.toImage i (toSpec k (ULift.{u} (Fin 2)))
      (F.exceptional_toImage_eq eI eH j₀ h₀).symm hker hI hC hbij
  let _ : IsDomain (pointLocalRing c) := hnormal.1
  let _ : IsIntegrallyClosed (pointLocalRing c) := hnormal.2
  have hnot : ¬(pointMaximalIdeal c).IsPrincipal :=
    selectedLocalMaximalIdeal_not_isPrincipal i hI H d F eI eH hn2 j₀ h₀ t ht q hq
  exact IsLocalRing.regularLocal_dimension_two_of_span_pair (R := pointLocalRing c)
    (selectedLocalCoordinate i hI H d F eI eH j₀ h₀ (q ⟨0⟩))
    (selectedLocalCoordinate i hI H d F eI eH j₀ h₀ (q ⟨1⟩)) hgen hnot

end AlgebraicGeometry.Scheme.Surfaces.Contraction.CartierProjectivePresentation
