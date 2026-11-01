/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FormallyUnramified.SectionRigidity
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Section descent along geometrically connected effective epimorphisms

The diagonal section of the actual kernel pair supplies the compatibility
needed by native effective-epimorphism descent. The descended scheme map,
its structural equation and its unique factorization are retained. Flat fpqc
and fppf morphisms supply the effective epimorphism in the final specializations.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Any lift through a separated unramified map coequalizes the actual kernel
pair of a geometrically connected morphism. -/
theorem kernelPair_comp_eq_of_geometricallyConnected
    {E B Y T : Scheme.{u}} (p : E ⟶ B)
    [IsSeparated p] [FormallyUnramified p] [LocallyOfFiniteType p]
    (q : Y ⟶ T) [GeometricallyConnected q] (b : T ⟶ B)
    (t : Y ⟶ E) (ht : t ≫ p = q ≫ b) :
    pullback.fst q q ≫ t = pullback.snd q q ≫ t := by
  apply eq_of_comp_eq_of_section p (pullback.fst q q) (pullback.diagonal q)
    (by simp) _ _
  · simpa only [Category.assoc, ht] using
      congrArg (fun k => k ≫ b) (pullback.condition (f := q) (g := q))
  · simp

/-- Native effective-epimorphism descent constructs the unique lift over the
specified base map, with its original factorization equation. -/
theorem existsUnique_lift_of_geometricallyConnected
    {E B Y T : Scheme.{u}} (p : E ⟶ B)
    [IsSeparated p] [FormallyUnramified p] [LocallyOfFiniteType p]
    (q : Y ⟶ T) [GeometricallyConnected q] [EffectiveEpi q] (b : T ⟶ B)
    (t : Y ⟶ E) (ht : t ≫ p = q ≫ b) :
    ∃! s : T ⟶ E, s ≫ p = b ∧ q ≫ s = t := by
  have hc : ∀ {Z : Scheme.{u}} (a c : Z ⟶ Y),
      a ≫ q = c ≫ q → a ≫ t = c ≫ t := by
    intro Z a c hac
    have h := congrArg (fun k => pullback.lift a c hac ≫ k)
      (kernelPair_comp_eq_of_geometricallyConnected p q b t ht)
    simpa only [← Category.assoc, pullback.lift_fst, pullback.lift_snd] using h
  let s := EffectiveEpi.desc q t hc
  have hs : q ≫ s = t := EffectiveEpi.fac q t hc
  refine ⟨s, ⟨?_, hs⟩, ?_⟩
  · apply (cancel_epi q).mp
    simpa only [← Category.assoc, hs] using ht
  · intro r hr
    exact EffectiveEpi.uniq q t hc r hr.2

/-- The literal pullback functor is bijective on arrows into any separated
unramified target when the source projection is an effective epimorphism. -/
theorem bijective_overPullback_map
    {B Y : Scheme.{u}} (q : Y ⟶ B) [GeometricallyConnected q]
    (U V : Over B) [IsSeparated V.hom] [FormallyUnramified V.hom]
    [LocallyOfFiniteType V.hom] [EffectiveEpi (pullback.fst U.hom q)] :
    Function.Bijective (fun a : U ⟶ V => (Over.pullback q).map a) := by
  constructor
  · intro a b hab
    apply Over.OverMorphism.ext
    apply (cancel_epi (pullback.fst U.hom q)).mp
    have h := congrArg (fun k => k.left ≫ pullback.fst V.hom q) hab
    simpa only [Over.pullback_map_left, pullback.lift_fst] using h
  · intro a
    have haw : a.left ≫ pullback.snd V.hom q = pullback.snd U.hom q := by
      simpa only [Over.pullback_obj_hom] using (Over.w a)
    have ha : (a.left ≫ pullback.fst V.hom q) ≫ V.hom =
        pullback.fst U.hom q ≫ U.hom := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, haw]
      exact pullback.condition.symm
    obtain ⟨s, hs, _⟩ := existsUnique_lift_of_geometricallyConnected V.hom
      (pullback.fst U.hom q) U.hom (a.left ≫ pullback.fst V.hom q) ha
    refine ⟨Over.homMk s hs.1, ?_⟩
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa only [Over.pullback_map_left, Over.homMk_left, pullback.lift_fst] using hs.2
    · simpa only [Over.pullback_map_left, pullback.lift_snd] using haw.symm

/-- The section case of the same construction. No finiteness or flatness
condition is imposed on the unramified target. -/
theorem existsUnique_factor_of_geometricallyConnected
    {E B Y : Scheme.{u}} (p : E ⟶ B)
    [IsSeparated p] [FormallyUnramified p] [LocallyOfFiniteType p]
    (q : Y ⟶ B) [GeometricallyConnected q] [EffectiveEpi q]
    (t : Y ⟶ E) (ht : t ≫ p = q) :
    ∃! s : B ⟶ E, s ≫ p = 𝟙 B ∧ q ≫ s = t :=
  existsUnique_lift_of_geometricallyConnected p q (𝟙 B) t (by simpa using ht)

/-- Flat quasi-compact geometrically connected morphisms supply the native
effective epimorphism, hence unique descent of sections. -/
theorem existsUnique_factor_of_flat_quasiCompact
    {E B Y : Scheme.{u}} (p : E ⟶ B)
    [IsSeparated p] [FormallyUnramified p] [LocallyOfFiniteType p]
    (q : Y ⟶ B) [Flat q] [QuasiCompact q] [GeometricallyConnected q]
    (t : Y ⟶ E) (ht : t ≫ p = q) :
    ∃! s : B ⟶ E, s ≫ p = 𝟙 B ∧ q ≫ s = t :=
  existsUnique_factor_of_geometricallyConnected p q t ht

/-- The same construction applies to flat locally finitely presented
geometrically connected morphisms, without quasi-compactness. -/
theorem existsUnique_factor_of_flat_locallyOfFinitePresentation
    {E B Y : Scheme.{u}} (p : E ⟶ B)
    [IsSeparated p] [FormallyUnramified p] [LocallyOfFiniteType p]
    (q : Y ⟶ B) [Flat q] [LocallyOfFinitePresentation q] [GeometricallyConnected q]
    (t : Y ⟶ E) (ht : t ≫ p = q) :
    ∃! s : B ⟶ E, s ≫ p = 𝟙 B ∧ q ≫ s = t :=
  existsUnique_factor_of_geometricallyConnected p q t ht

end AlgebraicGeometry.Scheme.Hom
