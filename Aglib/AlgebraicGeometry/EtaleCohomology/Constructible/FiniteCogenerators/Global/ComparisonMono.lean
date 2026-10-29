/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.AffineIntegralConstants.SheafColimit
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! # The original finite-constant comparison is mono after surjective pullback

The original relative test map is a genuine base change. Its surjectivity
detects maps to the fixed finite étale group through its open diagonal.
Thus the frozen represented-coordinate and literal copyObj pushforward maps
are themselves monic, with no replacement by another coefficient arrow.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global

universe u

attribute [local instance] hasSheafifyLarge Over.cartesianMonoidalCategory

open AffineIntegralConstants

/-- Original maps to an unramified target are detected after an actual
surjective source map, by the original open diagonal equalizer. The bounded
argument is the native private unramified_hom_ext in FiniteEtale.Nilpotent. -/
theorem unramified_precomposition_injective
    {T T' Z X : Scheme.{u}} (q : T' ⟶ T) [Surjective q]
    (p : Z ⟶ X) [FormallyUnramified p] [LocallyOfFiniteType p]
    (s t : T ⟶ Z) (hbase : s ≫ p = t ≫ p) (heq : q ≫ s = q ≫ t) : s = t := by
  let a : T ⟶ pullback p p := pullback.lift s t hbase
  let j : pullback a (pullback.diagonal p) ⟶ T := pullback.fst _ _
  have hjopen : IsOpenImmersion j := by dsimp [j]; infer_instance
  have hqa : q ≫ a = (q ≫ s) ≫ pullback.diagonal p := by
    apply pullback.hom_ext
    · simp [a, pullback.lift_fst]
    · simpa [a, pullback.lift_fst, pullback.lift_snd] using heq.symm
  let l : T' ⟶ pullback a (pullback.diagonal p) := pullback.lift q (q ≫ s) hqa
  have hlj : l ≫ j = q := by exact pullback.lift_fst _ _ _
  have hjsurj : Surjective j := by
    constructor
    intro x
    obtain ⟨z, hz⟩ := q.surjective x
    exact ⟨l z, (congrArg (fun k : T' ⟶ T => k z) hlj).trans hz⟩
  have : IsIso j := (isIso_iff_isOpenImmersion_and_surjective j).mpr ⟨hjopen, hjsurj⟩
  apply (cancel_epi j).mp
  have hj : j ≫ a = pullback.snd a (pullback.diagonal p) ≫ pullback.diagonal p :=
    pullback.condition
  calc
    j ≫ s = (j ≫ a) ≫ pullback.fst p p := by simp [a, pullback.lift_fst]
    _ = pullback.snd a (pullback.diagonal p) := by rw [hj]; simp
    _ = (j ≫ a) ≫ pullback.snd p p := by rw [hj]; simp
    _ = j ≫ t := by simp [a, pullback.lift_snd]

/-- The actual base-changed test map is the base change of the original
relative scheme map in its literal cartesian square. -/
theorem baseChangedTestMap_isPullback {X : Scheme.{u}} (U : Over X)
    {Y Z : Over X} (a : Y ⟶ Z) :
    IsPullback (baseChangedTestMap U a).left (pullback.snd U.hom Y.hom)
      (pullback.snd U.hom Z.hom) a.left := by
  exact IsPullback.of_two_pullback_projections
    (IsPullback.of_hasPullback U.hom Y.hom).flip
    (IsPullback.of_hasPullback U.hom Z.hom).flip
    (baseChangedTestMap U a).left a.left (Over.w a)
    (baseChangedTestMap_snd U a) (baseChangedTestMap_fst U a)

instance baseChangedTestMap_surjective {X : Scheme.{u}} (U : Over X)
    {Y Z : Over X} (a : Y ⟶ Z) [Surjective a.left] :
    Surjective (baseChangedTestMap U a).left :=
  MorphismProperty.of_isPullback (baseChangedTestMap_isPullback U a).flip inferInstance

section Coefficients

variable {X : Scheme.{u}} (B : Type u) [AddCommGroup B] [Finite B]
  {Y Z : Over X} (a : Y ⟶ Z) [Surjective a.left]

/-- The original relative coordinate map is mono, with no replacement by a
separately chosen adjunction unit. -/
instance constantDirectImageCoordinateMap_mono : Mono (constantDirectImageCoordinateMap B a) := by
  have (U : X.Etaleᵒᵖ) : Mono ((constantDirectImageCoordinateMap B a).app U) := by
    apply (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mpr
    intro s t hst
    apply ULift.ext
    change s.down.toMul = t.down.toMul
    apply Over.OverMorphism.ext
    apply unramified_precomposition_injective
      (baseChangedTestMap ((Scheme.Etale.forget X).obj U.unop) a).left
      (ConstantFinite.representation B X).group.X.hom s.down.toMul.left t.down.toMul.left
      ((Over.w s.down.toMul).trans (Over.w t.down.toMul).symm)
    exact congrArg (fun z => z.down.toMul.left) hst
  exact NatTrans.mono_of_mono_app _

instance constantRepresentedDirectImageMap_mono : Mono (constantRepresentedDirectImageMap B a) := by
  have : Mono (constantRepresentedDirectImageMap B a).hom := by
    change Mono ((constantDirectImageCoordinatesIso B Z).hom ≫
      constantDirectImageCoordinateMap B a ≫ (constantDirectImageCoordinatesIso B Y).inv)
    infer_instance
  exact (sheafToPresheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).mono_of_mono_map
    (inferInstanceAs (Mono (constantRepresentedDirectImageMap B a).hom))

/-- The original literal finite-constant pushforward transition along a
surjective relative scheme map is mono. -/
instance constantPushforwardFunctor_map_mono : Mono ((constantPushforwardFunctor B).map a.op) := by
  rw [constantPushforwardFunctor_map]
  change Mono ((constantRepresentedDirectImageIso B Z).inv ≫
    constantRepresentedDirectImageMap B a ≫ (constantRepresentedDirectImageIso B Y).hom)
  infer_instance

end Coefficients
end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global
