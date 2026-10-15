/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.IdealPushforward
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion
public import Aglib.AlgebraicGeometry.Modules.Coherent.AffineDetection
public import Aglib.AlgebraicGeometry.Modules.Pushforward.Isomorphism
/-!
# Actual coherent pushforward along arbitrary closed immersions

Open base change and the quotient description of a closed immersion with
affine target prove coherence of the genuine module-sheaf pushforward.
Neither an assumed coherent pushforward nor an assumed localization theorem
is used in this construction.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion
open Scheme.Modules

/-- Actual pushforward along a scheme isomorphism preserves the all-chart
coherence property. -/
theorem affineLocallyFiniteType_pushforward_iso {Z X : Scheme.{u}} (e : Z ≅ X)
    {M : Z.Modules} (hM : affineLocallyFiniteType Z M) :
    affineLocallyFiniteType X ((pushforward e.hom).obj M) :=
  (affineLocallyFiniteType X).prop_of_iso
    ((Scheme.Modules.pushforwardIsoRestrict e).app M).symm
    (affineLocallyFiniteType_restrict e.inv hM)

/-- A genuine closed immersion into an affine scheme preserves coherent
module sheaves, by its quotient-ring presentation. -/
theorem affineLocallyFiniteType_pushforward_affine {Z : Scheme.{u}} (R : CommRingCat.{u})
    (i : Z ⟶ Spec R) [IsClosedImmersion i] {M : Z.Modules} (hM : affineLocallyFiniteType Z M) :
    affineLocallyFiniteType (Spec R) ((pushforward i).obj M) := by
  obtain ⟨I, e, hi⟩ := (IsClosedImmersion.Spec_iff (f := i)).mp inferInstance
  rw [hi]
  exact (affineLocallyFiniteType (Spec R)).prop_of_iso
    ((pushforwardComp e.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).app M)
    (Ideal.affineLocallyFiniteType_pushforward R I (affineLocallyFiniteType_pushforward_iso e hM))

/-- Actual direct image along every closed immersion preserves coherence.
The proof tests actual affine charts and uses actual open base change. -/
theorem affineLocallyFiniteType_pushforward {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] {M : Z.Modules} (hM : affineLocallyFiniteType Z M) :
    affineLocallyFiniteType X ((pushforward i).obj M) := by
  intro R a _
  have h : affineLocallyFiniteType (Spec R)
      ((pushforward (pullback.snd i a)).obj ((restrictFunctor (pullback.fst i a)).obj M)) :=
    affineLocallyFiniteType_pushforward_affine R (pullback.snd i a)
      (affineLocallyFiniteType_restrict _ hM)
  exact (affineFiniteSheaf R).prop_of_iso ((openBaseChange i a).app M).symm
    ((affineLocallyFiniteType_spec_iff R _).mp h)

/-- Direct image along an embedding of scheme spaces is faithful: every
source open is the preimage of a target open. -/
theorem pushforwardFaithful {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (pushforward i).Faithful where
  map_injective {M N} {f g} h := by
    apply Scheme.Modules.hom_ext
    intro W
    obtain ⟨U, hU, heq⟩ := i.isClosedEmbedding.isEmbedding.isInducing.isOpen_iff.mp W.isOpen
    let V : X.Opens := ⟨U, hU⟩
    have hV : i ⁻¹ᵁ V = W := SetLike.ext' heq
    have h' := congrArg (fun k ↦ Scheme.Modules.Hom.app k V) h
    rw [← hV]
    exact h'

variable {Z X : Scheme.{u}} [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
  (i : Z ⟶ X) [IsClosedImmersion i]

/-- Closed-immersion specialization of canonical finite direct image. -/
abbrev coherentPushforward : Scheme.CoherentSheaf Z ⥤ Scheme.CoherentSheaf X :=
  Pushforward.Finite.coherentPushforward i

/-- The finite-type quasicoherent direct image has exactly the ordinary
underlying sheaf pushforward. -/
theorem coherentPushforward_comp_inclusion :
    coherentPushforward i ⋙ finiteTypeSheavesToModules X =
      finiteTypeSheavesToModules Z ⋙ pushforward i := rfl

instance coherentPushforward_faithful : (coherentPushforward i).Faithful where
  map_injective h := by
    have := pushforwardFaithful i
    apply ObjectProperty.hom_ext
    exact (pushforward i).map_injective (congrArg (fun k ↦ k.hom) h)

/-- The geometric open-base-change comparison restricts to the actual
finite-type quasicoherent full subcategories. -/
abbrev coherentOpenBaseChange {V : Scheme.{u}}
    (a : V ⟶ X) [IsOpenImmersion a] :
    letI : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion a
    coherentPushforward i ⋙ finiteTypeSheavesRestriction a ≅
      finiteTypeSheavesRestriction (pullback.fst i a) ⋙ coherentPushforward (pullback.snd i a) := by
  letI : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion a
  exact Pushforward.Finite.coherentOpenBaseChange i a

/-- The actual coherent pushforward into an affine scheme agrees with its
quotient presentation, including the source scheme isomorphism. -/
def affinePresentationComparison {Z : Scheme.{u}} [IsLocallyNoetherian Z]
    (R : CommRingCat.{u}) [IsNoetherianRing R] (i : Z ⟶ Spec R) [IsClosedImmersion i]
    (I : Ideal R) (e : Z ≅ Spec (Ideal.closedRing R I))
    (hi : i = e.hom ≫ Ideal.closedMap R I) :
    coherentPushforward i ≅ finiteTypeSheavesRestriction e.inv ⋙ Ideal.coherentPushforward R I :=
  Functor.fullyFaithfulCancelRight (finiteTypeSheavesToModules (Spec R))
    (Functor.isoWhiskerLeft (finiteTypeSheavesToModules Z)
      (pushforwardCongr hi ≪≫ (pushforwardComp e.hom (Ideal.closedMap R I)).symm ≪≫
        Functor.isoWhiskerRight (Scheme.Modules.pushforwardIsoRestrict e) _))

/-- The exact closed-immersion specialization of finite direct image. -/
abbrev coherentPushforwardExact :
    ExactFunctor (coherentExactStructure Z) (coherentExactStructure X) :=
  Pushforward.Finite.coherentPushforwardExact i

/-- The global construction specializes definitionally to the actual
quotient pushforward already constructed in the affine case. -/
@[simp] theorem coherentPushforward_quotient (R : CommRingCat.{u}) [IsNoetherianRing R]
    (I : Ideal R) :
    coherentPushforward (Ideal.closedMap R I) = Ideal.coherentPushforward R I := rfl

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion
