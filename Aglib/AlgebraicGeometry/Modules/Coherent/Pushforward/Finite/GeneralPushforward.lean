/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.Finite.AffinePushforward
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward
public import Aglib.AlgebraicGeometry.Modules.Coherent.AffineDetection
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Comparison
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion
public import Aglib.AlgebraicGeometry.Modules.Pushforward.Isomorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
/-!
# Coherent direct image along arbitrary finite morphisms

The original module-sheaf pushforward preserves finite-type quasicoherent
sheaves along finite morphisms. Actual affine presentations and open base
change reduce this to finite scalar restriction. Over locally noetherian
schemes this gives an exact coherent functor with the actual open-base-change
isomorphism.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open CategoryTheory.ExactCategory
open ModuleCat ModuleCat.FiniteRestrictionScalars
open Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts
universe u
namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite

/-- A finite map into an affine scheme has its actual finite coordinate presentation. -/
theorem exists_affine_presentation {Z : Scheme.{u}} (R : CommRingCat.{u})
    (f : Z ⟶ Spec R) [AlgebraicGeometry.IsFinite f] :
    ∃ (S : CommRingCat.{u}) (φ : R ⟶ S), φ.hom.Finite ∧
      ∃ e : Z ≅ Spec S, f = e.hom ≫ Spec.map φ :=
  QuasiCoherent.FiniteMorphism.exists_affine_presentation R f

/-- The generic finite-type preservation theorem on an affine target. -/
theorem affineLocallyFiniteType_pushforward_affine {Z : Scheme.{u}} (R : CommRingCat.{u})
    (f : Z ⟶ Spec R) [AlgebraicGeometry.IsFinite f] {M : Z.Modules}
    (hM : affineLocallyFiniteType Z M) :
    affineLocallyFiniteType (Spec R) ((pushforward f).obj M) :=
  QuasiCoherent.FiniteMorphism.affineLocallyFiniteType_pushforward_affine R f hM

/-- The generic finite-type preservation theorem over arbitrary schemes. -/
theorem affineLocallyFiniteType_pushforward {Z X : Scheme.{u}} (f : Z ⟶ X)
    [AlgebraicGeometry.IsFinite f] {M : Z.Modules} (hM : affineLocallyFiniteType Z M) :
    affineLocallyFiniteType X ((pushforward f).obj M) :=
  QuasiCoherent.FiniteMorphism.affineLocallyFiniteType_pushforward f hM

variable {Z X : Scheme.{u}} [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
  (f : Z ⟶ X) [AlgebraicGeometry.IsFinite f]

/-- Canonical finite direct image on coherent sheaves over locally Noetherian schemes. -/
abbrev coherentPushforward : Scheme.CoherentSheaf Z ⥤ Scheme.CoherentSheaf X :=
  finiteTypePushforward f

/-- The underlying functor remains the original module-sheaf pushforward. -/
@[simp] theorem coherentPushforward_comp_inclusion :
    coherentPushforward f ⋙ finiteTypeSheavesToModules X =
      finiteTypeSheavesToModules Z ⋙ pushforward f := rfl

theorem coherentPushforward_additive : (coherentPushforward f).Additive := by
  infer_instance

instance coherentPushforward_preservesFiniteLimits :
    PreservesFiniteLimits (coherentPushforward f) := by
  have : PreservesFiniteLimits (coherentPushforward f ⋙ finiteTypeSheavesToModules X) := by
    rw [coherentPushforward_comp_inclusion]
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ (finiteTypeSheavesToModules X)

/-- The generic open-base-change comparison specialized to coherent sheaves. -/
abbrev coherentOpenBaseChange {V : Scheme.{u}} (a : V ⟶ X) [IsOpenImmersion a] :
    letI : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion a
    coherentPushforward f ⋙ finiteTypeSheavesRestriction a ≅
      finiteTypeSheavesRestriction (pullback.fst f a) ⋙ coherentPushforward (pullback.snd f a) := by
  letI : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion a
  exact finiteTypePushforwardOpenBaseChange f a

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.Affine
variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : φ.hom.Finite)

variable [hR : IsNoetherianRing R] [hS : IsNoetherianRing S]

/-- Affine-coordinate specialization on coherent sheaves over Noetherian rings. -/
abbrev coherentPushforward : Scheme.CoherentSheaf (Spec S) ⥤ Scheme.CoherentSheaf (Spec R) :=
  finiteTypePushforwardSpec φ hφ

theorem coherentPushforward_comp_inclusion :
    coherentPushforward φ hφ ⋙ finiteTypeSheavesToModules (Spec R) =
      finiteTypeSheavesToModules (Spec S) ⋙ Scheme.Modules.pushforward (Spec.map φ) := rfl

/-- The generic scalar-restriction square specialized to coherent sheaves. -/
abbrev coherentPushforwardSquare :
    coherentPushforward φ hφ ⋙ (finiteTypeSheavesSpecModuleEquivalence R).functor ≅
      (finiteTypeSheavesSpecModuleEquivalence S).functor ⋙ moduleRestriction φ hφ :=
  finiteTypePushforwardSpecSquare φ hφ

theorem coherentPushforward_preservesFiniteLimits :
    PreservesFiniteLimits (coherentPushforward φ hφ) := by
  infer_instance

instance coherentPushforward_preservesFiniteColimits : PreservesFiniteColimits (coherentPushforward
  φ hφ) := by
  have : PreservesFiniteColimits
      (coherentPushforward φ hφ ⋙ (finiteTypeSheavesSpecModuleEquivalence R).functor) :=
    preservesFiniteColimits_of_natIso (coherentPushforwardSquare φ hφ).symm
  exact preservesFiniteColimits_of_reflects_of_preserves (coherentPushforward φ hφ)
    (finiteTypeSheavesSpecModuleEquivalence R).functor

theorem coherentPushforward_additive : (coherentPushforward φ hφ).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts (coherentPushforward φ hφ)
  exact Functor.additive_of_preservesBinaryBiproducts _


end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.Affine

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite
variable {Z X : Scheme.{u}} [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
  (f : Z ⟶ X) [AlgebraicGeometry.IsFinite f]

/-- The generic affine-presentation comparison specialized to coherent sheaves. -/
abbrev affinePresentationComparison {Z : Scheme.{u}} [IsLocallyNoetherian Z]
    (R S : CommRingCat.{u}) [IsNoetherianRing R] [IsNoetherianRing S]
    (f : Z ⟶ Spec R) [AlgebraicGeometry.IsFinite f] (φ : R ⟶ S) (hφ : φ.hom.Finite)
    (e : Z ≅ Spec S) (hf : f = e.hom ≫ Spec.map φ) :
    coherentPushforward f ≅
      finiteTypeSheavesRestriction e.inv ⋙ Pushforward.Finite.Affine.coherentPushforward φ hφ :=
  finiteTypePushforwardAffinePresentationComparison R S f φ hφ e hf

instance coherentPushforward_affine_preservesFiniteColimits {Z : Scheme.{u}}
    [IsLocallyNoetherian Z] (R : CommRingCat.{u}) [IsNoetherianRing R]
    (f : Z ⟶ Spec R) [AlgebraicGeometry.IsFinite f] :
    PreservesFiniteColimits (coherentPushforward f) := by
  obtain ⟨S, φ, hφ, e, hf⟩ := exists_affine_presentation R f
  have : IsNoetherianRing S := noetherian_affineChart S e.inv
  exact preservesFiniteColimits_of_natIso (affinePresentationComparison R S f φ hφ e hf).symm

/-- The actual finite coherent direct image preserves epimorphisms, detected
by vanishing cokernels on the original affine target charts. -/
instance coherentPushforward_preservesEpimorphisms :
    (coherentPushforward f).PreservesEpimorphisms where
  preserves {M N} a ha := by
    apply Preadditive.epi_of_isZero_cokernel
    apply coherent_isZero_of_affineRestrictions
    intro R _ j _
    have : PreservesFiniteColimits (coherentPushforward f ⋙ finiteTypeSheavesRestriction j) :=
      preservesFiniteColimits_of_natIso (coherentOpenBaseChange f j).symm
    have : Epi ((finiteTypeSheavesRestriction j).map ((coherentPushforward f).map a)) :=
      inferInstanceAs (Epi ((coherentPushforward f ⋙ finiteTypeSheavesRestriction j).map a))
    exact (isZero_cokernel_of_epi
      ((finiteTypeSheavesRestriction j).map ((coherentPushforward f).map a))).of_iso
      (PreservesCokernel.iso (finiteTypeSheavesRestriction j) ((coherentPushforward f).map a))

instance coherentPushforward_preservesFiniteColimits :
    PreservesFiniteColimits (coherentPushforward f) := by
  have : (coherentPushforward f).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  exact Functor.preservesFiniteColimits_of_preservesHomology _

/-- Exact direct image on actual coherent sheaves under geometric finiteness. -/
def coherentPushforwardExact :
    ExactFunctor (coherentExactStructure Z) (coherentExactStructure X) where
  toFunctor := coherentPushforward f
  map_conflation _ h := h.map_of_exact _

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.Affine
variable {R S : CommRingCat.{u}} [IsNoetherianRing R] [IsNoetherianRing S]

/-- The exact affine-coordinate specialization of finite direct image. -/
abbrev coherentPushforwardExact (φ : R ⟶ S) (hφ : φ.hom.Finite) :
    ExactFunctor (coherentExactStructure (Spec S)) (coherentExactStructure (Spec R)) :=
  letI : AlgebraicGeometry.IsFinite (Spec.map φ) :=
    (AlgebraicGeometry.IsFinite.SpecMap_iff φ).mpr hφ
  Pushforward.Finite.coherentPushforwardExact (Spec.map φ)

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.Affine
