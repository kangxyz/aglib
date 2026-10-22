/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FormalComparisonRestriction
public import Aglib.AlgebraicGeometry.Modules.InternalHom.DiagramFactorizationGluing

/-! # The actual global formal modification comparison

Affine formal functions determines entire local compatible families. Native
Hom-sheaf gluing produces their actual global natural transformation, with
its original comparison equation and whole-family uniqueness.
-/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u
variable {A : Type u} [CommRing A] {X Y : Scheme.{u}}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (p : Y ⟶ X) [IsProper p] (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I)) (G : Y.CoherentSheaf)

/-- The actual global factorization exists uniquely. No boundedness,
effectivity, or stagewise injectivity is an input. -/
theorem existsUnique_globalFormalComparison
    (γ : F.obj ⟶ ((completionFunctor Y
      (idealThickeningIdealSheaf (p ≫ f) I)).obj G).obj ⋙ pushforward p) :
    ∃! α : F ⟶ (completionFunctor X (idealThickeningIdealSheaf f I)).obj
      (properPushforwardCoefficient p G),
      α.hom ≫ formalPushforwardComparison p f I G = γ := by
  obtain ⟨α, hα, huniq⟩ := InternalHom.existsUnique_factorization_of_affine
    (formalPushforwardComparison p f I G) γ
    (existsUnique_formalComparison_restrict p f I F G γ)
  refine ⟨ObjectProperty.homMk α, hα, ?_⟩
  intro r hr
  apply ObjectProperty.hom_ext
  exact huniq r.hom hr

/-- The comparison of the specified upstairs formal map, in the original
coherent adic category. -/
def globalFormalModificationComparison
    (β : (baseIdealPullbackFunctor p f I).obj F ⟶
      (completionFunctor Y (idealThickeningIdealSheaf (p ≫ f) I)).obj G) :
    F ⟶ (completionFunctor X (idealThickeningIdealSheaf f I)).obj
      (properPushforwardCoefficient p G) :=
  (existsUnique_globalFormalComparison p f I F G
    (formalModificationAdjoint p f I F _ β)).choose

/-- The actual global map satisfies the specified original adjunction equation. -/
theorem globalFormalModificationComparison_diagram
    (β : (baseIdealPullbackFunctor p f I).obj F ⟶
      (completionFunctor Y (idealThickeningIdealSheaf (p ≫ f) I)).obj G) :
    (globalFormalModificationComparison p f I F G β).hom ≫
        formalPushforwardComparison p f I G = formalModificationAdjoint p f I F _ β :=
  (existsUnique_globalFormalComparison p f I F G
    (formalModificationAdjoint p f I F _ β)).choose_spec.1

end AlgebraicGeometry.Scheme.Modules.Coherent
