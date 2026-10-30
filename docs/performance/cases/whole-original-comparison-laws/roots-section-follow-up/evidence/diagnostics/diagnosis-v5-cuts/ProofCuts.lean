/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Representable.SectionComparisonValues
public import Aglib.AlgebraicGeometry.EtaleCohomology.BaseChangeMap
public import Aglib.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.TriangleCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.SectionPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.BoundaryNaturality

/-! # Original roots coefficient transport along an actual section

The whole formal identity, coefficient contraction and Ext assembly are in
SectionComparison. The native wrapper supplies the original roots isomorphisms,
actual inverse-image composition/identity maps and their existing intrinsic
coherence. Positivity and invertibility of the level remain geometric. No
geometric point, connected parameter family or new roots model is selected.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology.PointedNaturality
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.SectionPullback

universe u w w'
attribute [local instance] hasSheafifyLarge

/-- The original identity roots comparison is the original inverse-image identity. -/
theorem rootsPullbackIso_identity (X : Scheme.{u}) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) :
    (rootsPullbackIso (𝟙 X) n hn hinv).hom = (inverseImageId X).hom.app (mu X n) := by
  let j := (eqToIso (congrArg (fun f => (inverseImage f).obj (mu X n))
    (Category.comp_id (𝟙 X)))).hom
  have hc := TriangleCoherence.rootsPullbackIso_comp_intrinsic (𝟙 X) (𝟙 X) n hn hinv
  have hg := TriangleCoherence.rootsPullbackIso_congr (Category.comp_id (𝟙 X)) n hn hinv
  have hu := congrArg (fun e => e.hom.app (mu X n)) (inverseImageComp_id_comp (𝟙 X))
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, eqToIso.hom, eqToHom_app] at hu
  change (inverseImageComp (𝟙 X) (𝟙 X)).hom.app (mu X n) ≫
    (inverseImage (𝟙 X)).map ((inverseImageId X).hom.app (mu X n)) ≫
      𝟙 ((inverseImage (𝟙 X)).obj (mu X n)) = j at hu
  exact Functor.coefficientIso_identity_of_unit_composite
    (inverseImage (𝟙 X)) (inverseImageId X)
    (inverseImageComp (𝟙 X) (𝟙 X)) (mu X n) j (rootsPullbackIso (𝟙 X) n hn hinv)
    (hc.trans hg.symm) hu

/- Exact native proof/value cuts for the remaining transport failure.
The original passing identity prefix is needed because the failed native module
has no usable output. The three new declarations infer their actual producer
types; none assumes the desired public theorem. -/

theorem rootsCongr_value_cut {X Y : Scheme.{u}} (r : Y ⟶ X) (a : X ⟶ Y)
    (ha : a ≫ r = 𝟙 X) (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) :=
  TriangleCoherence.rootsPullbackIso_congr ha n hn hinv

#check rootsCongr_value_cut

theorem rootsIdentity_value_cut (X : Scheme.{u}) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) :=
  rootsPullbackIso_identity X n hn hinv

#check rootsIdentity_value_cut

theorem rootsComposite_inferred_cut {X Y : Scheme.{u}} (r : Y ⟶ X) (a : X ⟶ Y)
    (ha : a ≫ r = 𝟙 X) (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) :=
  Functor.comparison_transport_iso_hom_app_of_original
    (fun f : X ⟶ X => inverseImage f) ha (inverseImageId X) (mu X n)
    (rootsCongr_value_cut r a ha n hn hinv) (rootsIdentity_value_cut X n hn hinv)

#check rootsComposite_inferred_cut

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.SectionPullback
