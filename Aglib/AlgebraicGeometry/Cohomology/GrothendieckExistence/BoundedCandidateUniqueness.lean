/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineBoundedUniqueness
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.OpenBoundedCandidate
public import Aglib.AlgebraicGeometry.Modules.InternalHom.OpenCoverExt

/-! # Global uniqueness retaining the algebraic target and every formal stage

The algebraic target map is essential: completion alone need not be faithful
for the exceptional ideal. The arbitrary coherent source permits original
transitions between reconstructions with different algebraic targets.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u v

/-- Restriction to an actual jointly covering open family detects equality of
original module morphisms, without quasicoherence assumptions. -/
theorem reconstructionHom_ext_of_openCover
    {X : Scheme.{u}} {ι : Type v} (Y : ι → Scheme.{u})
    (p : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (p i)]
    (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), p i y = x)
    {M N : X.Modules} (f g : M ⟶ N)
    (h : ∀ i, (restrictFunctor (p i)).map f = (restrictFunctor (p i)).map g) : f = g :=
  InternalHom.hom_ext_of_openCover Y p hcover f g h

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (p : Y ⟶ X) [IsOpenImmersion p] {K : X.IdealSheafData}
  {F : AdicSystem X K} {G : X.CoherentSheaf}

/-- Pulling the candidate to an open retains the original unit followed by its
specified formal isomorphism, before and after changing quotient coordinates. -/
@[reassoc]
theorem openReconstructionCandidateIso_stage
    (β : (completionFunctor X K).obj G ≅ F) (n : ℕ) :
    (idealSheafQuotientUnit Y (K.comap p ^ n)).app ((pullback p).obj G.obj) ≫
        (openReconstructionCandidateIso p β).hom.hom.app (op n) =
      (pullback p).map ((idealSheafQuotientUnit X (K ^ n)).app G.obj ≫
        β.hom.hom.app (op n)) := by
  have hi := diagramIso_unit_inv
    ((adicSystemToDiagram Y (K.comap p)).mapIso (openIdealPullbackCompletionIso p K G))
    n ((pullback p).map ((idealSheafQuotientUnit X (K ^ n)).app G.obj))
    ((idealSheafQuotientUnit Y (K.comap p ^ n)).app ((pullback p).obj G.obj))
    (openIdealPullbackCompletionIso_unit p K G n)
  change _ ≫ ((openIdealPullbackCompletionIso p K G).inv.hom.app (op n) ≫
    (pullback p).map (β.hom.hom.app (op n))) = _
  calc
    _ = (_ ≫ (openIdealPullbackCompletionIso p K G).inv.hom.app (op n)) ≫
        (pullback p).map (β.hom.hom.app (op n)) := (Category.assoc _ _ _).symm
    _ = (pullback p).map ((idealSheafQuotientUnit X (K ^ n)).app G.obj) ≫
        (pullback p).map (β.hom.hom.app (op n)) :=
      congrArg (fun k => k ≫ (pullback p).map (β.hom.hom.app (op n))) hi
    _ = _ := (Functor.map_comp _ _ _).symm

/-- Actual affine pullbacks detect the two-projection uniqueness of a bounded
candidate. No effectiveness or gluing assumption occurs in this theorem. -/
theorem boundedCandidate_hom_ext_of_affineCover
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ι : Type v} (B : ι → CommRingCat.{u}) [∀ i, IsNoetherianRing (B i)]
    (p : ∀ i, Spec (B i) ⟶ X) [∀ i, IsOpenImmersion (p i)]
    (hcover : ∀ x : X, ∃ (i : ι) (y : Spec (B i)), p i y = x)
    {K : X.IdealSheafData} {F : AdicSystem X K} {H G A : X.CoherentSheaf}
    (α : F ⟶ (completionFunctor X K).obj H)
    (a : G ⟶ H) (β : (completionFunctor X K).obj G ≅ F)
    (_hβ : β.hom ≫ α = (completionFunctor X K).map a)
    (t : ℕ) (hk : killedByIdealSheaf (K ^ t) (kernel a.hom))
    (hc : killedByIdealSheaf (K ^ t) (cokernel a.hom))
    (f g : A ⟶ G) (ha : f ≫ a = g ≫ a)
    (hs : ∀ n : ℕ,
      f.hom ≫ (idealSheafQuotientUnit X (K ^ n)).app G.obj ≫ β.hom.hom.app (op n) =
      g.hom ≫ (idealSheafQuotientUnit X (K ^ n)).app G.obj ≫ β.hom.hom.app (op n)) :
    f = g := by
  apply ObjectProperty.hom_ext
  apply reconstructionHom_ext_of_openCover (fun i => Spec (B i)) p hcover
  intro i
  have hb := openReconstructionCandidate_bounds (p i) a t hk hc
  have he := affineBoundedCandidate_hom_ext
    ((coherentPullback (p i)).map a) (openReconstructionCandidateIso (p i) β) t hb.1
    ((coherentPullback (p i)).map f) ((coherentPullback (p i)).map g)
    (by simpa only [← Functor.map_comp] using congrArg ((coherentPullback (p i)).map) ha)
    (by
      intro n
      change (pullback (p i)).map f.hom ≫
          ((idealSheafQuotientUnit (Spec (B i)) (K.comap (p i) ^ n)).app
            ((pullback (p i)).obj G.obj) ≫
              (openReconstructionCandidateIso (p i) β).hom.hom.app (op n)) =
        (pullback (p i)).map g.hom ≫
          ((idealSheafQuotientUnit (Spec (B i)) (K.comap (p i) ^ n)).app
            ((pullback (p i)).obj G.obj) ≫
              (openReconstructionCandidateIso (p i) β).hom.hom.app (op n))
      rw [openReconstructionCandidateIso_stage (p i) β n,
        ← Functor.map_comp, ← Functor.map_comp]
      exact congrArg ((pullback (p i)).map) (hs n))
  have hp : (pullback (p i)).map f.hom = (pullback (p i)).map g.hom :=
    congrArg (fun q => q.hom) he
  apply (cancel_mono ((restrictFunctorIsoPullback (p i)).hom.app G.obj)).mp
  rw [(restrictFunctorIsoPullback (p i)).hom.naturality,
    (restrictFunctorIsoPullback (p i)).hom.naturality, hp]

end AlgebraicGeometry.Scheme.Modules.Coherent
