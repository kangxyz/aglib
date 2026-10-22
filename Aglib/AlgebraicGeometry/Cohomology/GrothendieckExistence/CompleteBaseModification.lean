/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FormalPullbackCompletion
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FullFaithful
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ProperAlgebraicComparison

/-! # The actual algebraic modification adjoint over a complete base

Full faithfulness lifts the specified formal pullback isomorphism, retaining
its original completion map. The algebraic adjoint has uniformly bounded
coherent defects off the modification's isomorphism locus. This is the
complete-base step, not an assertion of effectivity over an uncompleted chart.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
section
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  (I : Ideal A) [IsAdicComplete I A]
  {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (p : Y ⟶ X) (f : X ⟶ Spec (CommRingCat.of A)) [IsProper p] [IsProper f]
  (M : X.CoherentSheaf) (G : Y.CoherentSheaf)
  (β : (baseIdealPullbackFunctor p f I).obj
      ((completionFunctor X (idealThickeningIdealSheaf f I)).obj M) ≅
    (completionFunctor Y (idealThickeningIdealSheaf (p ≫ f) I)).obj G)

/-- The specific formal pullback isomorphism has a unique algebraic lift. -/
def completeBaseModificationIso : (coherentPullback p).obj M ≅ G :=
  (Cohomology.completionFunctorFullyFaithful I (p ≫ f)).preimageIso
    ((baseIdealPullbackCompletionIso p f I M).symm ≪≫ β)

/-- Lifting keeps the specified formal comparison rather than an unrelated iso. -/
theorem completeBaseModificationIso_completion :
    (baseIdealPullbackCompletionIso p f I M).hom ≫
      (completionFunctor Y (idealThickeningIdealSheaf (p ≫ f) I)).map
        (completeBaseModificationIso I p f M G β).hom = β.hom := by
  rw [completeBaseModificationIso, Functor.FullyFaithful.preimageIso]
  rw [(Cohomology.completionFunctorFullyFaithful I (p ≫ f)).map_preimage]
  exact Iso.hom_inv_id_assoc _ _

/-- The original module-sheaf isomorphism, forgetting only coherent membership. -/
def completeBaseModificationModuleIso : (pullback p).obj M.obj ≅ G.obj :=
  (QuasiCoherent.finiteTypeSheavesToModules Y).mapIso
    (completeBaseModificationIso I p f M G β)

/-- The original geometric adjoint after the specified full-faithful lift. -/
def completeBaseModificationAdjoint : M.obj ⟶ (pushforward p).obj G.obj :=
  (pullbackPushforwardAdjunction p).homEquiv _ _
    (completeBaseModificationModuleIso I p f M G β).hom

end

section
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  (I : Ideal A) [IsAdicComplete I A]
  {X Y : Scheme.{u}} [IsNoetherian X] [IsLocallyNoetherian Y]
  (p : Y ⟶ X) (f : X ⟶ Spec (CommRingCat.of A)) [IsProper p] [IsProper f]
  (M : X.CoherentSheaf) (G : Y.CoherentSheaf)
  (β : (baseIdealPullbackFunctor p f I).obj
      ((completionFunctor X (idealThickeningIdealSheaf f I)).obj M) ≅
    (completionFunctor Y (idealThickeningIdealSheaf (p ≫ f) I)).obj G)

/-- One positive exceptional-ideal power bounds both ordinary algebraic defects. -/
theorem completeBaseModificationAdjoint_bounded
    (K : X.IdealSheafData) (U : X.Opens) [IsIso (p ∣_ U)]
    (hU : (U : Set X)ᶜ ⊆ K.support) :
    ∃ t : ℕ, 0 < t ∧
      killedByIdealSheaf (K ^ t) (kernel (completeBaseModificationAdjoint I p f M G β)) ∧
      killedByIdealSheaf (K ^ t) (cokernel (completeBaseModificationAdjoint I p f M G β)) :=
  exists_pos_pow_killedByIdealSheaf_pullbackIso_adjoint p K U hU M.property G.property
    (completeBaseModificationModuleIso I p f M G β)

end

end AlgebraicGeometry.Scheme.Modules.Coherent
