/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.CoproductClassDetection
public import Aglib.AlgebraicGeometry.Limits.FiniteCoproductPullback
public import Aglib.CategoryTheory.Limits.Shapes.PullbackFamilyRefinement

/-! # Original family classes under finite target coproducts and refinements

Component restrictions concern the pullbacks of an arbitrary original family,
not classes on the target charts themselves. The native finite-coproduct
pullback isomorphism produces whole-family zero. A target-stage map then
returns that same original class to the direct base change of the family.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u e

attribute [local instance] hasSheafifyLarge HasExt.standard

/-- Actual componentwise restrictions of one class vanish on the coproduct
of arbitrary scheme arrows. No etale hypothesis on those arrows is needed. -/
theorem sigmaDesc_cohomologyPullback_eq_zero
    {W : Scheme.{u}} [HasExt.{e} (AbelianSheaf.{u, u + 1} W)]
    {ι : Type u} [Finite ι] (T : ι → Scheme.{u}) (a : ∀ i, T i ⟶ W)
    (M : AbelianSheaf.{u, u + 1} W) (q : ℕ) (c : Sheaf.H.{e} M q)
    (hc : ∀ i, cohomologyPullback.{u, e, u + 2} (a i) M q c = 0) :
    cohomologyPullback.{u, e, u + 2} (Sigma.desc a) M q c = 0 := by
  apply eq_zero_of_finiteCoproduct_cohomologyPullbacks_eq_zero T _ q
  intro i
  exact restriction_zero_after_refinement
    (a i) (Sigma.desc a) (Sigma.ι T i) (𝟙 (T i))
    (by rw [Category.id_comp, Sigma.ι_comp_desc]) M q c (hc i)

/-- Zero on every actual family pullback gives zero after base change to the
whole finite target coproduct. The comparison is the canonical scheme iso. -/
theorem finiteCoproductPullback_cohomologyPullback_eq_zero
    {X W : Scheme.{u}} [HasExt.{e} (AbelianSheaf.{u, u + 1} W)]
    {ι : Type u} [Finite ι] (T : ι → Scheme.{u}) (a : ∀ i, T i ⟶ X)
    (p : W ⟶ X) (M : AbelianSheaf.{u, u + 1} W)
    (q : ℕ) (c : Sheaf.H.{e} M q)
    (hc : ∀ i,
      cohomologyPullback.{u, e, u + 2} (pullback.snd (a i) p) M q c = 0) :
    cohomologyPullback.{u, e, u + 2} (pullback.snd (Sigma.desc a) p) M q c = 0 := by
  have hwhole := sigmaDesc_cohomologyPullback_eq_zero
    (fun i => pullback (a i) p) (fun i => pullback.snd (a i) p) M q c hc
  have hprojection : (FiniteCoproductPullback.iso T a p).inv ≫
      Sigma.desc (fun i => pullback.snd (a i) p) = pullback.snd (Sigma.desc a) p := by
    rw [← FiniteCoproductPullback.iso_hom_snd T a p, Iso.inv_hom_id_assoc]
  exact TwoFieldEffacement.original_class_zero_of_map_law
    (FiniteCoproductPullback.iso T a p).inv
    (Sigma.desc (fun i => pullback.snd (a i) p))
    (pullback.snd (Sigma.desc a) p) hprojection M q c hwhole

/-- An original target-stage refinement transports zero on the chart's family
pullback to the direct stage of the original composite family map. -/
theorem familyStage_cohomologyPullback_eq_zero
    {S X W T U : Scheme.{u}} [HasExt.{e} (AbelianSheaf.{u, u + 1} W)]
    (t : T ⟶ S) (f : X ⟶ S) (p : W ⟶ X) (a : U ⟶ X)
    (b : pullback t f ⟶ U) (hb : b ≫ a = pullback.snd t f)
    (M : AbelianSheaf.{u, u + 1} W) (q : ℕ) (c : Sheaf.H.{e} M q)
    (hc : cohomologyPullback.{u, e, u + 2} (pullback.snd a p) M q c = 0) :
    cohomologyPullback.{u, e, u + 2} (pullback.snd t (p ≫ f)) M q c = 0 :=
  TwoFieldEffacement.original_class_zero_of_map_law
    (pullback.familyRefinement t f p a b hb) (pullback.snd a p)
    (pullback.snd t (p ≫ f)) (pullback.familyRefinement_snd t f p a b hb)
    M q c hc

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
