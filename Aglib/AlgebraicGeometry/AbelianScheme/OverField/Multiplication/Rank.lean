/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Multiplication.Degree
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.RankBaseChange
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Projective
public import Aglib.AlgebraicGeometry.Group.BaseChange.MarkedKernel

/-!
# All-field rank of original positive multiplication

Choose the existing constant locally free rank on the original connected
group. The actual Cartesian group base change preserves that same rank.
Over the algebraic closure, the proved Hilbert calculation gives n^(2d).
The native smooth relative dimension d is the original identity cotangent
dimension and is preserved by base change. Comparing ranks at the actual
base-changed unit point identifies the original rank.

Every positive n is allowed, including characteristic-dividing levels.
The native multiplication kernel inherits the same rank on its original
Cartesian identity square. No numerical degree, polarization law or rank
base-change family is a premise.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.Group.Multiplication

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k]

-- Canonical group pullback projections and the native morphism-property dictionaries
-- have definitionally equal field-scheme source types, as in the pinned base-change instances.
set_option backward.isDefEq.respectTransparency.types false in
/-- Over every field, positive original multiplication has native locally
free rank n^(2d), for the actual original identity cotangent dimension d. -/
theorem multiplication_hasLocallyFreeRank
    (G : Grp (Over (Spec (.of k)))) [IsCommMonObj G.X]
    [IsHProjective G.X.hom] [GeometricallyIntegral G.X.hom] [Smooth G.X.hom]
    (n : ℕ) (hn : 0 < n) :
    Hom.HasLocallyFreeRank ((𝟙 G.X) ^ n).left
      (n ^ (2 * Module.finrank k (Cotangent.Space η[G.X]))) := by
  let : IsIntegral G.X.left := GeometricallyIntegral.isIntegral_of_subsingleton G.X.hom
  let d := Module.finrank k (Cotangent.Space η[G.X])
  let : SmoothOfRelativeDimension d G.X.hom :=
    Group.smoothOfRelativeDimension_finrank_identityCotangent_of_preconnected G.X
  let f := MultiplicationKernel.multiplicationHom G n
  have hmap : f.hom.hom = (𝟙 G.X) ^ n := by
    simpa only [MultiplicationKernel.multiplication] using
      MultiplicationKernel.multiplicationHom_hom G n
  obtain ⟨hfinite, _, hsurjective⟩ := multiplication_finite_flat_surjective_of_isHProjective G n hn
  let : IsFinite f.hom.hom.left := by rw [hmap]; exact hfinite
  let : Surjective f.hom.hom.left := by rw [hmap]; exact hsurjective
  have hfree := Group.finite_surjective_hom_finiteLocallyFree G G f
  obtain ⟨r, hr⟩ := Hom.exists_hasLocallyFreeRank f.hom.hom.left hfree
  let K := AlgebraicClosure k
  let s : Spec (.of K) ⟶ Spec (.of k) := Spec.algebraMap k K
  let P := Over.pullback s
  let B := BaseChange.groupSchemeBaseChange s
  let G' := B.functor.obj G
  let f' := B.functor.map f
  let : GrpObj (P.obj G.X) := Functor.grpObjObj
  let : IsCommMonObj G'.X := inferInstanceAs (IsCommMonObj (P.obj G.X))
  let : IsHProjective G'.X.hom := IsHProjective.pullback_snd G.X.hom s
  let : GeometricallyIntegral G'.X.hom :=
    MorphismProperty.pullback_snd (P := @GeometricallyIntegral.{u}) G.X.hom s inferInstance
  let : SmoothOfRelativeDimension d G'.X.hom :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension.{u} d) G.X.hom s inferInstance
  have hdK : topologicalKrullDim G'.X.left = (d : WithBot ℕ∞) :=
    Scheme.smoothFieldDimension K G'.X.left G'.X.hom d inferInstance ⟨unitPoint G'.X⟩
  have hpow : f'.hom.hom = (𝟙 G'.X) ^ n := by
    change P.map f.hom.hom = (𝟙 (P.obj G.X)) ^ n
    rw [hmap]
    calc
      _ = (P.map (𝟙 G.X)) ^ n :=
        (P.homMonoidHom (X := G.X) (M := G.X)).map_pow _ _
      _ = _ := by rw [CategoryTheory.Functor.map_id]
  have hr' : Hom.HasLocallyFreeRank f'.hom.hom.left r :=
    Hom.hasLocallyFreeRank_of_isPullback (pullback.fst G.X.hom s) f'.hom.hom.left
      f.hom.hom.left (pullback.fst G.X.hom s) (BaseChange.map_isPullback s f) r hr
  have hcalc : Hom.HasLocallyFreeRank f'.hom.hom.left (n ^ (2 * d)) := by
    rw [hpow]
    exact multiplication_hasLocallyFreeRank_of_dimension_of_infinite G' n hn d hdK
  have h₁ := (Hom.hasLocallyFreeRank_iff_rank_eq f'.hom.hom.left hr'.finiteLocallyFree r).mp
    hr' (unitPoint G'.X)
  have h₂ := (Hom.hasLocallyFreeRank_iff_rank_eq f'.hom.hom.left hr'.finiteLocallyFree
    (n ^ (2 * d))).mp hcalc (unitPoint G'.X)
  have heq : r = n ^ (2 * d) := h₁.symm.trans h₂
  have hfinal : Hom.HasLocallyFreeRank f.hom.hom.left (n ^ (2 * d)) := heq ▸ hr
  simpa only [hmap, d] using hfinal

/-- The existing scheme-theoretic multiplication kernel has the same
native locally free rank, on its original identity fibre square. -/
theorem kernelGroup_hasLocallyFreeRank
    (G : Grp (Over (Spec (.of k)))) [IsCommMonObj G.X]
    [IsHProjective G.X.hom] [GeometricallyIntegral G.X.hom] [Smooth G.X.hom]
    (n : ℕ) (hn : 0 < n) :
    Hom.HasLocallyFreeRank (MultiplicationKernel.kernelGroup G n).X.hom
      (n ^ (2 * Module.finrank k (Cotangent.Space η[G.X]))) := by
  apply Hom.hasLocallyFreeRank_of_isPullback _ _ _ _ (MultiplicationKernel.kernelSquare G n)
  exact multiplication_hasLocallyFreeRank G n hn

/-- The full native positive-level statement on the original map:
finite, flat, surjective, with rank determined by the actual smooth dimension. -/
theorem multiplication_finite_flat_surjective_rank
    (G : Grp (Over (Spec (.of k)))) [IsCommMonObj G.X]
    [IsHProjective G.X.hom] [GeometricallyIntegral G.X.hom] [Smooth G.X.hom]
    (n : ℕ) (hn : 0 < n) :
    IsFinite ((𝟙 G.X) ^ n).left ∧ Flat ((𝟙 G.X) ^ n).left ∧
      Surjective ((𝟙 G.X) ^ n).left ∧
        Hom.HasLocallyFreeRank ((𝟙 G.X) ^ n).left
          (n ^ (2 * Module.finrank k (Cotangent.Space η[G.X]))) := by
  obtain ⟨hf, hflat, hs⟩ := multiplication_finite_flat_surjective_of_isHProjective G n hn
  exact ⟨hf, hflat, hs, multiplication_hasLocallyFreeRank G n hn⟩

end AlgebraicGeometry.Scheme.Group.Multiplication
