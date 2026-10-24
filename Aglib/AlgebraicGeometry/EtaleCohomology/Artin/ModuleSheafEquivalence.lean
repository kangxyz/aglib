/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.ArtinBaseChangeSite
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Nilpotent
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ConstantPullbackSections
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Noetherian.Nilpotent

/-!
# Original module sheaves and sections across Artin residue maps

The actual finite-etale basis comparison makes the original module direct and
inverse images equivalences. The original adjunction unit and terminal transport
then make the original section pullback an isomorphism, including across an
actual nilpotent quotient and the residue map of a local Artinian ring.

The coefficient ring has an independent universe, and no torsion, finiteness or
Noetherian hypothesis is imposed on it.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.FiniteEtale
open Scheme.EtaleCohomology.Constructible.Modules

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Artin

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type r) [CommRing R]

section Artin

variable {X S : Scheme.{u}}
  [IsLocallyArtinian X] [QuasiSeparatedSpace X]
  [IsLocallyArtinian S] [QuasiSeparatedSpace S]

/-- Restriction to the actual finite-etale basis at the original module value universe. -/
abbrev moduleFiniteEtaleRestriction (X : Scheme.{u}) [IsLocallyArtinian X]
    [QuasiSeparatedSpace X] :
    ModuleSheaf R X ⥤ Sheaf (artinTopology X) (ModuleCat.{u + 1} R) :=
  (toEtale X).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
    (artinTopology X) X.smallEtaleTopology

instance moduleFiniteEtaleRestriction_isEquivalence :
    (moduleFiniteEtaleRestriction R X).IsEquivalence := by
  let : ∀ U : X.Etaleᵒᵖ,
      Limits.HasLimitsOfShape (StructuredArrow U (toEtale X).op) (ModuleCat.{u + 1} R) :=
    fun _ => ModuleCat.hasLimitsOfShape.{_, _, u + 1, r}
  unfold moduleFiniteEtaleRestriction
  infer_instance

/-- Original module direct image is an equivalence under the actual Artin site comparison. -/
theorem moduleDirectImage_isEquivalence_of_artin (f : S ⟶ X) [Surjective f]
    [(baseChange f).IsEquivalence] : (moduleDirectImage R f).IsEquivalence := by
  let F := (baseChange f).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
    (artinTopology X) (artinTopology S)
  let : F.IsEquivalence :=
    (artinBaseChangeSheafEquivalence f (ModuleCat.{u + 1} R)).isEquivalence_inverse
  let e : moduleDirectImage R f ⋙ moduleFiniteEtaleRestriction R X ≅
      moduleFiniteEtaleRestriction R S ⋙ F := Iso.refl _
  let : (moduleDirectImage R f ⋙ moduleFiniteEtaleRestriction R X).IsEquivalence :=
    CategoryTheory.Functor.isEquivalence_of_iso e.symm
  exact CategoryTheory.Functor.isEquivalence_of_comp_right
    (moduleDirectImage R f) (moduleFiniteEtaleRestriction R X)

/-- The native module inverse image itself is an equivalence. -/
theorem moduleInverseImage_isEquivalence_of_artin (f : S ⟶ X) [Surjective f]
    [(baseChange f).IsEquivalence] : (moduleInverseImage R f).IsEquivalence := by
  let := moduleDirectImage_isEquivalence_of_artin R f
  exact (moduleImageAdjunction R f).isEquivalence_left_of_isEquivalence_right

end Artin

/-- An equivalence of the native inverse image makes the original section map invertible. -/
theorem moduleGlobalSectionsPullback_isIso_of_isEquivalence
    {X S : Scheme.{u}} (f : S ⟶ X) [(moduleInverseImage R f).IsEquivalence]
    (F : ModuleSheaf R X) : IsIso (moduleGlobalSectionsPullback R f F) := by
  let : IsIso ((moduleImageAdjunction R f).unit.app F) := by infer_instance
  unfold moduleGlobalSectionsPullback
  infer_instance

/-- The Artin site equivalence preserves the literal original module global sections. -/
theorem moduleGlobalSectionsPullback_isIso_of_artin
    {X S : Scheme.{u}} [IsLocallyArtinian X] [QuasiSeparatedSpace X]
    [IsLocallyArtinian S] [QuasiSeparatedSpace S]
    (f : S ⟶ X) [Surjective f] [(baseChange f).IsEquivalence]
    (F : ModuleSheaf R X) : IsIso (moduleGlobalSectionsPullback R f F) := by
  let := moduleInverseImage_isEquivalence_of_artin R f
  exact moduleGlobalSectionsPullback_isIso_of_isEquivalence R f F

/-- Original module-section pullback across an actual nilpotent Artinian quotient. -/
theorem moduleGlobalSectionsPullback_quotient_isIso
    (A : Type u) [CommRing A] [IsArtinianRing A] (I : Ideal A) (hI : IsNilpotent I)
    (F : ModuleSheaf R (Spec (.of A))) :
    IsIso (moduleGlobalSectionsPullback R
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) F) := by
  let f := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have hnil : I ≤ _root_.nilradical A :=
    (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian I)).mp hI
  let : Surjective f :=
    ⟨(PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical hnil).surjective⟩
  let : (FiniteEtale.baseChange f).IsEquivalence :=
    FiniteEtale.Nilpotent.quotient_baseChange_isEquivalence A I hI
  exact moduleGlobalSectionsPullback_isIso_of_artin R f F

/-- The literal residue pullback preserves original module sections of a local Artinian ring. -/
theorem moduleGlobalSectionsPullback_residue_isIso
    (A : Type u) [CommRing A] [IsArtinianRing A] [IsLocalRing A]
    (F : ModuleSheaf R (Spec (.of A))) :
    IsIso (moduleGlobalSectionsPullback R
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) F) := by
  have hI : IsNilpotent (IsLocalRing.maximalIdeal A) := by
    rw [← Ring.KrullDimLE.nilradical_eq_maximalIdeal A]
    exact IsNoetherianRing.isNilpotent_nilradical A
  exact moduleGlobalSectionsPullback_quotient_isIso R A (IsLocalRing.maximalIdeal A) hI F

end AlgebraicGeometry.Scheme.EtaleCohomology.Artin
