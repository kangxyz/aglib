/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Restriction.Cartesian
public import Aglib.Topology.Sheaves.Cohomology.OpenTransfer.RestrictionSquare

/-! # Complete original cartesian restriction squares

The complete constructors retain the original geometric maps and coefficient
compatibility family. Their focused owner leaves the canonical pointwise laws
in Restriction.Cartesian unchanged.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y : Scheme.{u}}

/-- The original module coefficient paths agree on the complete open-index family. -/
theorem moduleHPrimeOpenMap_comp_congr
    {W T : Scheme.{u}} (a : W ⟶ Y) (b : W ⟶ T) (p : Y ⟶ X) (j : T ⟶ X)
    (w : a ≫ p = b ≫ j) {M : X.Modules} {N : Y.Modules} {L : T.Modules} {P : W.Modules}
    (φp : M ⟶ (Scheme.Modules.pushforward p).obj N)
    (φa : N ⟶ (Scheme.Modules.pushforward a).obj P)
    (φj : M ⟶ (Scheme.Modules.pushforward j).obj L)
    (φb : L ⟶ (Scheme.Modules.pushforward b).obj P)
    (hφ : φp ≫ (Scheme.Modules.pushforward p).map φa ≫
        (Scheme.Modules.pushforwardComp a p).hom.app P ≫
        (Scheme.Modules.pushforwardCongr w).hom.app P =
      φj ≫ (Scheme.Modules.pushforward j).map φb ≫
        (Scheme.Modules.pushforwardComp b j).hom.app P)
    (n : ℕ) (U : X.Opensᵒᵖ) :
    ((zariskiCohomologyOpenMap p (moduleAddSheaf X M) (moduleAddSheaf Y N)
        (moduleCoefficientPullback p φp) n).app U ≫
      (zariskiCohomologyOpenMap a (moduleAddSheaf Y N) (moduleAddSheaf W P)
        (moduleCoefficientPullback a φa) n).app ((Opens.map p.base).op.obj U)) ≫
      (Sheaf.cohomologyPresheaf.{u + 1} (moduleAddSheaf W P) n).map
        (eqToHom (congrArg (fun f : W ⟶ X => f ⁻¹ᵁ U.unop) w).symm).op =
    (zariskiCohomologyOpenMap j (moduleAddSheaf X M) (moduleAddSheaf T L)
        (moduleCoefficientPullback j φj) n).app U ≫
      (zariskiCohomologyOpenMap b (moduleAddSheaf T L) (moduleAddSheaf W P)
        (moduleCoefficientPullback b φb) n).app ((Opens.map j.base).op.obj U) := by
  let ρ := φp ≫ (Scheme.Modules.pushforward p).map φa ≫
    (Scheme.Modules.pushforwardComp a p).hom.app P
  have hp := zariskiCohomologyOpenMap_module_comp_app p a φp φa n U
  have hj := zariskiCohomologyOpenMap_module_comp_app j b φj φb n U
  have hc := zariskiCohomologyOpenMap_module_congr_app (a ≫ p) (b ≫ j) w ρ n U
  have hρ : ρ ≫ (Scheme.Modules.pushforwardCongr w).hom.app P =
      φj ≫ (Scheme.Modules.pushforward j).map φb ≫
        (Scheme.Modules.pushforwardComp b j).hom.app P := by
    simpa only [ρ, Category.assoc] using hφ
  erw [hρ] at hc
  exact (congrArg (fun z => z ≫
    (Sheaf.cohomologyPresheaf.{u + 1} (moduleAddSheaf W P) n).map
      (eqToHom (congrArg (fun f : W ⟶ X => f ⁻¹ᵁ U.unop) w).symm).op) hp).trans
        (hc.trans hj.symm)

/-- The actual module inputs to the complete lower Ext-diagram restriction square. -/
def moduleHPrimeOpenMapCompCongrTopSquare
    {W T : Scheme.{u}} (a : W ⟶ Y) (b : W ⟶ T) (p : Y ⟶ X) (j : T ⟶ X)
    (w : a ≫ p = b ≫ j) {M : X.Modules} {N : Y.Modules} {L : T.Modules} {P : W.Modules}
    (φp : M ⟶ (Scheme.Modules.pushforward p).obj N)
    (φa : N ⟶ (Scheme.Modules.pushforward a).obj P)
    (φj : M ⟶ (Scheme.Modules.pushforward j).obj L)
    (φb : L ⟶ (Scheme.Modules.pushforward b).obj P)
    (hφ : φp ≫ (Scheme.Modules.pushforward p).map φa ≫
        (Scheme.Modules.pushforwardComp a p).hom.app P ≫
        (Scheme.Modules.pushforwardCongr w).hom.app P =
      φj ≫ (Scheme.Modules.pushforward j).map φb ≫
        (Scheme.Modules.pushforwardComp b j).hom.app P)
    (U : X.Opens) (ha : a ⁻¹ᵁ (p ⁻¹ᵁ U) = ⊤) (hj : j ⁻¹ᵁ U = ⊤) (n : ℕ) :
    Square AddCommGrpCat.{u + 1} :=
  TopCat.Sheaf.openCohomologyRestrictionSquare.{u, u + 1}
    a.base b.base p.base j.base (congrArg (fun f : W ⟶ X => f.base) w)
    (moduleCoefficientPullback p φp) (moduleCoefficientPullback a φa)
    (moduleCoefficientPullback j φj) (moduleCoefficientPullback b φb)
    n U ha hj (moduleHPrimeOpenMap_comp_congr a b p j w φp φa φj φb hφ n)

/-- The complete original cartesian open-restriction square, with all four
original edges and its law constructed before exposing native components. -/
def moduleOpenPullbackRestrictionSquare (p : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) (n : ℕ) : Square AddCommGrpCat.{u + 1} := by
  let V := p ⁻¹ᵁ U
  let a := V.ι
  let b := p ∣_ U
  let j := U.ι
  let h : IsPullback a b p j := (isPullback_morphismRestrict p U).flip
  let N : Y.Modules := (Scheme.Modules.pullback p).obj M
  let P : V.toScheme.Modules := (Scheme.Modules.pullback b).obj (M.restrict j)
  let ε : N.restrict a ⟶ P := inv ((Scheme.Modules.cartesianPullbackBaseChangeMate a b p j h).app M)
  let φp : M ⟶ (Scheme.Modules.pushforward p).obj N :=
    (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M
  let φa : N ⟶ (Scheme.Modules.pushforward a).obj P :=
    (Scheme.Modules.restrictAdjunction a).unit.app N ≫
    (Scheme.Modules.pushforward a).map ε
  let φj : M ⟶ (Scheme.Modules.pushforward j).obj (M.restrict j) :=
    (Scheme.Modules.restrictAdjunction j).unit.app M
  let φb : M.restrict j ⟶ (Scheme.Modules.pushforward b).obj P :=
    (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app (M.restrict j)
  exact moduleHPrimeOpenMapCompCongrTopSquare a b p j h.w φp φa φj φb
    (Scheme.Modules.cartesianPullbackBaseChangeMate_inv_unit_comp a b p j h M)
    U V.ι_preimage_self U.ι_preimage_self n

end AlgebraicGeometry.Scheme.Cohomology
