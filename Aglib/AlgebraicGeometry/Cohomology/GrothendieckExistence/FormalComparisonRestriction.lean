/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FormalComparisonAffineRestriction
public import Aglib.AlgebraicGeometry.Modules.InternalHom.DiagramRestriction

/-! # Unique comparison in the original open-restriction coordinates -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u
variable {A : Type u} [CommRing A] {X Y : Scheme.{u}}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (p : Y ⟶ X) [IsProper p] (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I)) (G : Y.CoherentSheaf)

/-- Formal functions gives unique factorization on every original affine
restriction, with both targets still restrictions of the global diagrams. -/
theorem existsUnique_formalComparison_restrict
    (γ : F.obj ⟶ ((completionFunctor Y
      (idealThickeningIdealSheaf (p ≫ f) I)).obj G).obj ⋙ pushforward p)
    (B : CommRingCat.{u}) (j : Spec B ⟶ X) [IsOpenImmersion j] :
    ∃! q : F.obj ⋙ restrictFunctor j ⟶
      ((completionFunctor X (idealThickeningIdealSheaf f I)).obj
        (properPushforwardCoefficient p G)).obj ⋙ restrictFunctor j,
      q ≫ Functor.whiskerRight (formalPushforwardComparison p f I G) (restrictFunctor j) =
        Functor.whiskerRight γ (restrictFunctor j) := by
  let : IsLocallyNoetherian (Spec B) := isLocallyNoetherian_of_isOpenImmersion j
  let : IsNoetherianRing B := isLocallyNoetherian_Spec.mp inferInstance
  let : IsLocallyNoetherian (Limits.pullback p j) :=
    isLocallyNoetherian_of_isOpenImmersion (pullback.fst p j)
  obtain ⟨α, hα, huniq⟩ := existsUnique_affineRestrictionFactorization
    (pullback.fst p j) (pullback.snd p j) p j (IsPullback.of_hasPullback p j) f I F G γ
  let e := restrictFunctorIsoPullback j
  refine ⟨InternalHom.diagramHomTransport e α.hom,
    InternalHom.diagramHomTransport_comp e α.hom
      (formalPushforwardComparison p f I G) γ hα, ?_⟩
  intro r hr
  let s : (baseIdealPullbackFunctor j f I).obj F ⟶
      (baseIdealPullbackFunctor j f I).obj
        ((completionFunctor X (idealThickeningIdealSheaf f I)).obj
          (properPushforwardCoefficient p G)) :=
    ObjectProperty.homMk (InternalHom.diagramHomTransport e.symm r)
  have hs : s = α := huniq s
    (InternalHom.diagramHomTransport_comp e.symm r
      (formalPushforwardComparison p f I G) γ hr)
  have hh : InternalHom.diagramHomTransport e.symm r = α.hom :=
    congrArg (fun t => t.hom) hs
  rw [← InternalHom.diagramHomTransport_symm e r, hh]

end AlgebraicGeometry.Scheme.Modules.Coherent
