/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffinePushforwardFactorization
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FormalPushforwardOpenComparison

/-! # Unique original comparison on every affine open chart

The local target remains the pullback of the single global completion target.
The native open mate transports local formal functions to this target, retaining
the exact original ambient equation and uniqueness of the entire formal map.
-/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u

private theorem uniqueFactorization_transport
    {C D : Type*} [Category C] [Category D] (U : C ⥤ D)
    {F N N' : C} {T T' : D} (e : N ≅ N') (d : T ≅ T')
    (ψ : U.obj N ⟶ T) (ψ' : U.obj N' ⟶ T') (γ : U.obj F ⟶ T)
    (hs : ψ ≫ d.hom = U.map e.hom ≫ ψ')
    (he : ∃! q : F ⟶ N', U.map q ≫ ψ' = γ ≫ d.hom) :
    ∃! q : F ⟶ N, U.map q ≫ ψ = γ := by
  obtain ⟨q, hq, huniq⟩ := he
  refine ⟨q ≫ e.inv, ?_, ?_⟩
  · apply (cancel_mono d.hom).mp
    rw [Functor.map_comp, Category.assoc, Category.assoc, hs,
      ← Category.assoc (U.map e.inv), ← Functor.map_comp, Iso.inv_hom_id,
      U.map_id, Category.id_comp]
    exact hq
  · intro r hr
    have heq : r ≫ e.hom = q := huniq _ (by
      change U.map (r ≫ e.hom) ≫ ψ' = γ ≫ d.hom
      rw [Functor.map_comp, Category.assoc, ← hs, ← Category.assoc, hr])
    rw [← heq, Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable {A : Type u} [CommRing A] {B : CommRingCat.{u}} [IsNoetherianRing B]
  {X Y Y' : Scheme.{u}}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Y']
  (a : Y' ⟶ Y) (b : Y' ⟶ Spec B) (p : Y ⟶ X) (g : Spec B ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion g] [IsProper p] [IsProper b]
  (h : IsPullback a b p g) (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I)) (G : Y.CoherentSheaf)

include h in
/-- Every original compatible family factors uniquely on an affine open, with
target the restriction of the actual global coherent pushforward completion. -/
theorem existsUnique_affineRestrictionFactorization
    (γ : F.obj ⟶ ((completionFunctor Y
      (idealThickeningIdealSheaf (p ≫ f) I)).obj G).obj ⋙ pushforward p) :
    ∃! α : (baseIdealPullbackFunctor g f I).obj F ⟶
        (baseIdealPullbackFunctor g f I).obj
          ((completionFunctor X (idealThickeningIdealSheaf f I)).obj
            (properPushforwardCoefficient p G)),
      α.hom ≫ Functor.whiskerRight (formalPushforwardComparison p f I G) (pullback g) =
        Functor.whiskerRight γ (pullback g) := by
  exact uniqueFactorization_transport
    (F := (baseIdealPullbackFunctor g f I).obj F)
    (adicSystemToDiagram (Spec B) (idealThickeningIdealSheaf (g ≫ f) I))
    (formalPushforwardOpenTargetIso a b p g h f I G)
    (formalPushforwardOpenAmbientIso a b p g h f I G)
    (Functor.whiskerRight (formalPushforwardComparison p f I G) (pullback g))
    (formalPushforwardComparison b (g ≫ f) I ((coherentPullback a).obj G))
    (Functor.whiskerRight γ (pullback g))
    (formalPushforwardOpenComparison_square a b p g h f I G)
    (existsUnique_affinePushforwardFactorization_overBase b ((coherentPullback a).obj G)
      (g ≫ f) I ((baseIdealPullbackFunctor g f I).obj F)
      (Functor.whiskerRight γ (pullback g) ≫
        (formalPushforwardOpenAmbientIso a b p g h f I G).hom))

end AlgebraicGeometry.Scheme.Modules.Coherent
