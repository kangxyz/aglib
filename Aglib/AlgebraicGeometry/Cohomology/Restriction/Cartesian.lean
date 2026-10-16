/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.Open
public import Aglib.AlgebraicGeometry.Cohomology.Restriction.Geometric
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Units

/-! # The original geometric map under cartesian open restriction

The actual module pullback/restriction mate identifies the original
geometric maps on native open cohomology. The proof uses the exact original
module unit equation, native coefficient composition and actual preimage
transport. All coefficients and scheme morphisms are arbitrary.
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

private theorem moduleHPrimeOpenMap_comp_congr
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

private theorem paste_native_naturality
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : D ⥤ E) (J : D ⥤ C) (Q : E ⥤ C) (δ : J ⟶ F ⋙ Q)
    {A B : C} {s t : D} {v : E} (f : A ⟶ B) (g : B ⟶ Q.obj v)
    (j : A ⟶ J.obj s) (k : s ⟶ t) (e : v ⟶ F.obj s) (a : v ⟶ F.obj t)
    (he : e ≫ F.map k = a) (h : (f ≫ g) ≫ Q.map e = j ≫ δ.app s) :
    f ≫ g ≫ Q.map a = j ≫ J.map k ≫ δ.app t := by
  calc
    _ = (f ≫ g) ≫ Q.map a := (Category.assoc f g (Q.map a)).symm
    _ = ((f ≫ g) ≫ Q.map e) ≫ Q.map (F.map k) :=
      (congrArg (fun z => (f ≫ g) ≫ Q.map z) he.symm).trans
        ((congrArg (fun z => (f ≫ g) ≫ z) (Q.map_comp e (F.map k))).trans
          (Category.assoc (f ≫ g) (Q.map e) (Q.map (F.map k))).symm)
    _ = (j ≫ δ.app s) ≫ Q.map (F.map k) := congrArg (fun z => z ≫ Q.map (F.map k)) h
    _ = _ := (Category.assoc j (δ.app s) (Q.map (F.map k))).trans
      (congrArg (fun z => j ≫ z) (δ.naturality k).symm)

set_option maxHeartbeats 500000 in
-- The literal statement expands the original module units through four native cohomology maps.
/-- The two original unit paths through an open cartesian square agree on actual native
open cohomology, retaining the actual pullback/restriction mate and open transports. -/
theorem moduleHPrimeOpenMap_pullback_restrict (p : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) (n : ℕ) :
    let V := p ⁻¹ᵁ U
    let a := V.ι
    let b := p ∣_ U
    let j := U.ι
    let h : IsPullback a b p j := (isPullback_morphismRestrict p U).flip
    let N : Y.Modules := (Scheme.Modules.pullback p).obj M
    let P : V.toScheme.Modules := (Scheme.Modules.pullback b).obj (M.restrict j)
    let ε : N.restrict a ⟶ P :=
      inv ((Scheme.Modules.cartesianPullbackBaseChangeMate a b p j h).app M)
    let φp : M ⟶ (Scheme.Modules.pushforward p).obj N :=
      (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M
    let φa : N ⟶ (Scheme.Modules.pushforward a).obj P :=
      (Scheme.Modules.restrictAdjunction a).unit.app N ≫ (Scheme.Modules.pushforward a).map ε
    let φj : M ⟶ (Scheme.Modules.pushforward j).obj (M.restrict j) :=
      (Scheme.Modules.restrictAdjunction j).unit.app M
    let φb : M.restrict j ⟶ (Scheme.Modules.pushforward b).obj P :=
      (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app (M.restrict j)
    (zariskiCohomologyOpenMap p (moduleAddSheaf X M) (moduleAddSheaf Y N)
        (moduleCoefficientPullback p (M := M) (N := N) φp)
        n).app (op U) ≫
      (zariskiCohomologyOpenMap a (moduleAddSheaf Y N) (moduleAddSheaf V.toScheme P)
        (moduleCoefficientPullback a (M := N) (N := P) φa) n).app (op V) ≫
      (Sheaf.cohomologyPresheaf.{u + 1} (moduleAddSheaf V.toScheme P) n).map
        (eqToHom V.ι_preimage_self.symm).op =
    (zariskiCohomologyOpenMap j (moduleAddSheaf X M)
        (moduleAddSheaf U.toScheme (M.restrict j))
        (moduleCoefficientPullback j (M := M) (N := M.restrict j) φj)
        n).app (op U) ≫
      (Sheaf.cohomologyPresheaf.{u + 1} (moduleAddSheaf U.toScheme (M.restrict j)) n).map
        (eqToHom U.ι_preimage_self.symm).op ≫
      (zariskiCohomologyOpenMap b (moduleAddSheaf U.toScheme (M.restrict j))
        (moduleAddSheaf V.toScheme P)
        (moduleCoefficientPullback b (M := M.restrict j) (N := P) φb)
        n).app (op ⊤) := by
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
  let A : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    Sheaf.cohomologyPresheaf.{u + 1} (moduleAddSheaf X M) n
  let B : Y.Opensᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    Sheaf.cohomologyPresheaf.{u + 1} (moduleAddSheaf Y N) n
  let Q : V.toScheme.Opensᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    Sheaf.cohomologyPresheaf.{u + 1} (moduleAddSheaf V.toScheme P) n
  let J : U.toScheme.Opensᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    Sheaf.cohomologyPresheaf.{u + 1} (moduleAddSheaf U.toScheme (M.restrict j)) n
  let gp : A ⟶ (Opens.map p.base).op ⋙ B :=
    zariskiCohomologyOpenMap p (moduleAddSheaf X M) (moduleAddSheaf Y N)
      (moduleCoefficientPullback p (M := M) (N := N) φp) n
  let ga : B ⟶ (Opens.map a.base).op ⋙ Q :=
    zariskiCohomologyOpenMap a (moduleAddSheaf Y N) (moduleAddSheaf V.toScheme P)
      (moduleCoefficientPullback a (M := N) (N := P) φa) n
  let gj : A ⟶ (Opens.map j.base).op ⋙ J :=
    zariskiCohomologyOpenMap j (moduleAddSheaf X M)
      (moduleAddSheaf U.toScheme (M.restrict j))
      (moduleCoefficientPullback j (M := M) (N := M.restrict j) φj) n
  let gb : J ⟶ (Opens.map b.base).op ⋙ Q :=
    zariskiCohomologyOpenMap b (moduleAddSheaf U.toScheme (M.restrict j))
      (moduleAddSheaf V.toScheme P) (moduleCoefficientPullback b (M := M.restrict j) (N := P) φb) n
  let kA : (⊤ : V.toScheme.Opens) ⟶ a ⁻¹ᵁ V := eqToHom V.ι_preimage_self.symm
  let kJ : (⊤ : U.toScheme.Opens) ⟶ j ⁻¹ᵁ U := eqToHom U.ι_preimage_self.symm
  let t : op ((a ≫ p) ⁻¹ᵁ U) ⟶ op ((b ≫ j) ⁻¹ᵁ U) :=
    (eqToHom (congrArg (fun f : V.toScheme ⟶ X => f ⁻¹ᵁ U) h.w).symm).op
  have hc : (gp.app (op U) ≫ ga.app (op V)) ≫ Q.map t =
      gj.app (op U) ≫ gb.app (op (j ⁻¹ᵁ U)) :=
    moduleHPrimeOpenMap_comp_congr a b p j h.w φp φa φj φb
      (Scheme.Modules.cartesianPullbackBaseChangeMate_inv_unit_comp a b p j h M) n (op U)
  have hk : t ≫ (Opens.map b.base).op.map kJ.op = kA.op := Subsingleton.elim _ _
  exact paste_native_naturality (Opens.map b.base).op J Q gb
    (gp.app (op U)) (ga.app (op V)) (gj.app (op U)) kJ.op t kA.op hk hc

end AlgebraicGeometry.Scheme.Cohomology
