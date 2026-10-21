/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.SerreVanishing
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ReesCohomologyAffine
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Cartesian
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Twisting
public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.FiniteLocallyFree

/-!
# One twist bound for summands of a coherent graded realization

For an arbitrary ring map `A → B` with `B` Noetherian, a coherent coefficient
on `P_B` has ONE Serre bound after affine pushforward to `P_A`. Consequently
that same bound controls any family of retracts of this pushforward, even an
infinite family. The coefficient on `P_B`, rather than each individual
summand, is the sole input to Serre vanishing.

The associated-graded construction for a formal system must supply the
coherent coefficient and its component inclusions/projections. This file
neither assumes a uniform vanishing bound nor assumes an algebraization of
the original formal system. It is not itself the existence theorem.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u v

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A B : Type u} [CommRing A] [CommRing B]
  (φ : A →+* B) (ι : Type u)

/-- The native twist of the native affine direct image is the direct image
of the native twist over the extended base. The forward comparison uses the
original projection-formula map and the original twist base-change map. -/
def projectiveTwistPushforwardIso (d : ℤ) (N : (ProjectiveSpace B ι).Modules) :
    (moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj
        ((pushforward (ProjectiveSpace.map φ ι)).obj N) ≅
      (pushforward (ProjectiveSpace.map φ ι)).obj
        ((moduleTensorLeftFunctor (ProjectiveSpace B ι) (twistingSheaf B ι d)).obj N) :=
  projectionFormulaIso (ProjectiveSpace.map φ ι) (twistingSheaf A ι d) N ≪≫
    (pushforward (ProjectiveSpace.map φ ι)).mapIso
      ((moduleTensorRightFunctor (ProjectiveSpace B ι) N).mapIso
        (twistingPullbackIso φ ι d))

/-- A coherent realization over one Noetherian extended base gives a single
bound on its original direct image. The original base need not be Noetherian
and the extended base need not be flat over it. -/
theorem projectiveSerreVanishing_pushforward [IsNoetherianRing B]
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : (ProjectiveSpace B ι).Modules)
    (hN : affineLocallyFiniteType (ProjectiveSpace B ι) N) :
    ∃ C : ℕ, ∀ d : ℤ, (C : ℤ) ≤ d → ∀ q : ℕ, q ≠ 0 →
      Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace A ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj
          ((pushforward (ProjectiveSpace.map φ ι)).obj N))) q) := by
  let : Finite ι := Finite.of_equiv _ e.symm
  let : CompactSpace (ProjectiveSpace A ι) :=
    QuasiCompact.compactSpace_of_compactSpace (toSpec A ι)
  let : IsAffineHom (Spec.map (CommRingCat.ofHom φ)) := isAffineHom_of_isAffine _
  let : IsAffineHom (pullback.fst (toSpec A ι) (Spec.map (CommRingCat.ofHom φ))) :=
    MorphismProperty.pullback_fst _ _ (inferInstance : IsAffineHom
      (Spec.map (CommRingCat.ofHom φ)))
  let p := ProjectiveSpace.map φ ι
  let : IsAffineHom p := by
    change IsAffineHom (ProjectiveSpace.map φ ι)
    rw [← baseChangeIso_hom_fst φ ι]
    infer_instance
  obtain ⟨C, hC⟩ := projectiveSerreVanishing B ι n e N hN
  refine ⟨C, ?_⟩
  intro d hd q hq
  let T := (moduleTensorLeftFunctor (ProjectiveSpace B ι) (twistingSheaf B ι d)).obj N
  have hT := twistingTensor_affineLocallyFiniteType B ι d N hN
  let : T.IsQuasicoherent := quasicoherent_of_affineCharts T (fun R j _ => (hT R j).1)
  let : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι) T) q) :=
    hC d hd q hq
  have hpush : Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (ProjectiveSpace A ι) ((pushforward p).obj T)) q) :=
    (moduleCohomologyAffinePushforward_bijective p T q).injective.subsingleton
  exact moduleCohomology_subsingleton_of_iso
    (projectiveTwistPushforwardIso φ ι d N).symm q hpush

/-- All the components of a coherent graded realization obey the SAME bound.
The index type is arbitrary and has its own universe. Only actual split
inclusions into the original pushforward are used. -/
theorem projectiveSerreVanishing_retracts [IsNoetherianRing B]
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : (ProjectiveSpace B ι).Modules)
    (hN : affineLocallyFiniteType (ProjectiveSpace B ι) N)
    {J : Type v} (M : J → (ProjectiveSpace A ι).Modules)
    (inc : ∀ j, M j ⟶ (pushforward (ProjectiveSpace.map φ ι)).obj N)
    (pr : ∀ j, (pushforward (ProjectiveSpace.map φ ι)).obj N ⟶ M j)
    (h : ∀ j, inc j ≫ pr j = 𝟙 (M j)) :
    ∃ C : ℕ, ∀ d : ℤ, (C : ℤ) ≤ d → ∀ j : J, ∀ q : ℕ, q ≠ 0 →
      Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace A ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj
          (M j))) q) := by
  obtain ⟨C, hC⟩ := projectiveSerreVanishing_pushforward φ ι n e N hN
  refine ⟨C, ?_⟩
  intro d hd j q hq
  let H := moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d) ⋙
    moduleCohomologyFunctorOfHom (ProjectiveSpace A ι) (RingHom.id Γ(ProjectiveSpace A ι, ⊤)) q
  let : Subsingleton (H.obj ((pushforward (ProjectiveSpace.map φ ι)).obj N)) := hC d hd q hq
  have hc : H.map (inc j) ≫ H.map (pr j) = 𝟙 (H.obj (M j)) := by
    rw [← H.map_comp, h, H.map_id]
  have hl : Function.LeftInverse (H.map (pr j)) (H.map (inc j)) := by
    intro x
    simpa only [ModuleCat.comp_apply, ModuleCat.id_apply] using
      ConcreteCategory.congr_hom hc x
  have hi : Function.Injective (H.map (inc j)) := hl.injective
  exact hi.subsingleton

end AlgebraicGeometry.Scheme.Cohomology
