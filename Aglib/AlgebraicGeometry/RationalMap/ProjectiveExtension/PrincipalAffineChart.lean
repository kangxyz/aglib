/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.ProjectiveExtension.PrincipalOpen
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.AffineChart

/-!
# Proper projective extension from an affine principal open

For every finite tuple on `Spec A[1/f]`, the actual native coordinate-ideal
blowup is proper when `A` is Noetherian, is unchanged over that entire
principal open, and its projective map agrees there with the standard
projective affine-chart morphism of the original tuple. The ring `A` may
be reducible or nonreduced. This is a principal-open theorem, not the
arbitrary-open gluing theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace.FromSections
open IsLocalization.Away

universe u

namespace AlgebraicGeometry.Scheme.RationalCoordinates

variable {I : Type u} {S : Type u} [CommRing S]

/-- The scalar presentation and the native affine-chart family are the same
actual unit-sheaf maps. -/
theorem affineTupleSection_eq_chartFamily (s : I → S) :
    affineTupleSection s = AffineChart.family s := by
  funext i
  exact Blowup.IdealFrames.affineMultiplication_eq_unitMul S (Option.elim i 1 s)

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [Finite I]
variable {R : Type u} [CommRing R]

/-- Actual properness, principal-open isomorphism, and agreement with the
original affine chart, without an assumed line source, denominator, or map
equality. The blowdown and extension map are the native constructions. -/
theorem exists_principalAffineChart_extension (φ : R →+* A) (f : A)
    (s : I → Localization.Away f) :
    ∃ (n : ℕ) (a : I → A),
      IsProper (Blowup.blowupDatum
        (Blowup.affineCenter A (principalCoordinateIdeal f n a))).map ∧
      IsIso (pullback.snd
        (Blowup.blowupDatum (Blowup.affineCenter A (principalCoordinateIdeal f n a))).map
        (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))) ∧
      principalCoordinateLift A f n a ≫
        affineCoordinateBlowupMap A (principalHomogeneousCoordinates f n a)
          (Spec.map (CommRingCat.ofHom φ)) =
        AffineChart.map ((algebraMap A (Localization.Away f)).comp φ) s := by
  obtain ⟨n, a, h⟩ := exists_principalCoordinateBlowupMap_agrees A f
    (Spec.map (CommRingCat.ofHom φ)) s
  refine ⟨n, a, affineCoordinateBlowup_isProper A (principalHomogeneousCoordinates f n a),
    principalCoordinateBlowup_isIso A f n a, ?_⟩
  rw [h]
  let : Epi (Sigma.desc (affineTupleSection s)) := affineTupleSection_epi s
  let : Epi (Sigma.desc (AffineChart.family s)) := AffineChart.family_epi s
  refine (@mapOfFiniteFamily_iso R _ (Option I) (Spec (.of (Localization.Away f)))
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) ≫
      Spec.map (CommRingCat.ofHom φ))
    (SheafOfModules.unit (Spec (.of (Localization.Away f))).ringCatSheaf)
    (SheafOfModules.unit (Spec (.of (Localization.Away f))).ringCatSheaf)
    (affineUnit_locallyRankOne (Localization.Away f))
    (affineUnit_locallyRankOne (Localization.Away f))
    inferInstance (affineTupleSection s) (AffineChart.family s)
    (affineTupleSection_epi s) (AffineChart.family_epi s)
    (Iso.refl _) (fun i ↦ ?_)).trans ?_
  · exact (Category.comp_id (affineTupleSection s i)).trans
      (congrFun (affineTupleSection_eq_chartFamily s) i)
  · have hp : Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) ≫
        Spec.map (CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom ((algebraMap A (Localization.Away f)).comp φ)) := by
      rw [← Spec.map_comp]
      rfl
    rw [hp]
    exact AffineChart.mapOfFiniteFamily_eq _ s _

end AlgebraicGeometry.Scheme.RationalCoordinates
