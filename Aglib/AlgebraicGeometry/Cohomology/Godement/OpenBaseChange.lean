/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.PullbackPushforward
public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Flasque.Complex
public import Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.QuasiIso

/-! # Descent of the canonical unit through cartesian open base change

Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/P5PositiveUnitOpen.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`5c431ecd8bb08af3ce18cc4d638cada3b8b8d1cde05b6044df1ecd8add2d3446`.
Selected declarations: totalTermsFlasque, pushPlus_quasiIso_flasque, quasiIso_of_QPlus_map_isIso,
  openPushPlusIso, openPullPlusIso, open_geometric_unit, openTotalBridge, openTotalBridge_quasiIso,
  restrictedTotal_flasque, restrictedPositive, localPositive, restrictedTotal, openSpanTarget,
  restrictedPositiveUnit, openPositiveComparison, globalSpanLeg, localSpanLeg,
  restrictedPositiveUnit_factor, quasiIso_of_plus_span, globalSpanLeg_quasiIso,
  localSpanLeg_quasiIso, augmentation_component_naturality, openTotalBridge_f,
  local_total_unit_component, open_component_first_square, open_component_second_square,
  open_positive_unit_span_component, open_positive_unit_span_factorized, open_positive_unit_span,
  positivePlusUnit_restrict_quasiIso.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

namespace Plus

/-- The standard derived category used for bounded-below flasque direct-image comparisons. -/
local instance openBaseChangeDerivedStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

lemma pushforward_quasiIso_of_flasque {P X : Scheme.{u}} (p : P ⟶ X)
    {K M : CochainComplex.Plus P.Modules} (s : K ⟶ M) [QuasiIso s.hom]
    (hK : ∀ n, TopCat.Presheaf.IsFlasque (K.obj.X n).presheaf)
    (hM : ∀ n, TopCat.Presheaf.IsFlasque (M.obj.X n).presheaf) :
    QuasiIso ((Scheme.Modules.pushforward p).mapCochainComplexPlus.map s).hom := by
  obtain ⟨a, ha⟩ := K.property
  obtain ⟨b, hb⟩ := M.property
  let := ha
  let := hb
  exact quasiIso_pushforward_of_flasque p s.hom a b
    (fun n hn => CochainComplex.isZero_of_isStrictlyGE K.obj a n hn)
    (fun n hn => CochainComplex.isZero_of_isStrictlyGE M.obj b n hn) hK hM

lemma quasiIso_of_isIso_Q_map {X : Scheme.{u}}
    {K M : CochainComplex.Plus X.Modules} (s : K ⟶ M)
    (h : IsIso (DerivedCategory.Plus.Q.map s)) : QuasiIso s.hom := by
  let := h
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso X.Modules _).mp
  change IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map s))
  infer_instance

lemma quasiIso_of_span {Y : Scheme.{u}}
    {A B C D E : CochainComplex.Plus Y.Modules}
    (u : A ⟶ B) (β : B ⟶ C) [IsIso β] (r : C ⟶ E) (v : A ⟶ D) (s : D ⟶ E)
    (he : u ≫ β ≫ r = v ≫ s)
    (hr : QuasiIso r.hom) (hv : QuasiIso v.hom) (hs : QuasiIso s.hom) :
    QuasiIso u.hom := by
  let := hr
  let := hv
  let := hs
  let e := (CochainComplex.Plus.ι Y.Modules).mapIso (asIso β)
  have : IsIso β.hom := by
    change IsIso e.hom
    infer_instance
  have : QuasiIso (u.hom ≫ (β.hom ≫ r.hom)) := by
    have hvs : QuasiIso (v.hom ≫ s.hom) := inferInstance
    have hehom : u.hom ≫ β.hom ≫ r.hom = v.hom ≫ s.hom :=
      congrArg (fun q => q.hom) he
    exact hehom.symm ▸ hvs
  exact _root_.quasiIso_of_comp_right u.hom (β.hom ≫ r.hom)

end Plus

namespace Godement

/-- The standard derived category used for the cartesian open Godement comparison. -/
local instance openBaseChangeDerivedStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

lemma totalPlus_terms_isFlasque (P : Scheme.{u}) (K : CochainComplex.Plus P.Modules) (n : ℤ) :
    TopCat.Presheaf.IsFlasque (((godementTotalPlus P).obj K).obj.X n).presheaf := by
  obtain ⟨a, ha⟩ := K.property
  let := ha
  exact godementTotal_isFlasque K.obj a
    (fun i hi => CochainComplex.isZero_of_isStrictlyGE K.obj a i hi) n

variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j] (h : IsPullback a b f j)

/-- Open restriction after direct image agrees with direct image after restriction in the
supplied cartesian square. -/
def openPushPlusIso :
    (Scheme.Modules.pushforward f).mapCochainComplexPlus ⋙
        (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus ≅
      (Scheme.Modules.restrictFunctor a).mapCochainComplexPlus ⋙
        (Scheme.Modules.pushforward b).mapCochainComplexPlus :=
  (Functor.mapCochainComplexPlusCompIso (Scheme.Modules.pushforward f)
    (Scheme.Modules.restrictFunctor j)).symm ≪≫
    NatIso.mapCochainComplexPlus (cartesianOpenBaseChange a b f j h) ≪≫
    Functor.mapCochainComplexPlusCompIso (Scheme.Modules.restrictFunctor a)
      (Scheme.Modules.pushforward b)

/-- The bounded-below pullback/restriction comparison for the supplied cartesian open square. -/
def openPullPlusIso :
    (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus ⋙
        (Scheme.Modules.pullback b).mapCochainComplexPlus ≅
      (Scheme.Modules.pullback f).mapCochainComplexPlus ⋙
        (Scheme.Modules.restrictFunctor a).mapCochainComplexPlus :=
  (Functor.mapCochainComplexPlusCompIso (Scheme.Modules.restrictFunctor j)
    (Scheme.Modules.pullback b)).symm ≪≫
    NatIso.mapCochainComplexPlus (asIso (cartesianPullbackBaseChangeMate a b f j h)) ≪≫
    Functor.mapCochainComplexPlusCompIso (Scheme.Modules.pullback f)
      (Scheme.Modules.restrictFunctor a)

lemma open_geometric_unit (K : CochainComplex.Plus X.Modules) :
    (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.map
        ((Plus.pullbackPushforwardUnit f).app K) ≫
        (openPushPlusIso a b f j h).hom.app
          ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K) =
      (Plus.pullbackPushforwardUnit b).app ((Scheme.Modules.restrictFunctor
        j).mapCochainComplexPlus.obj K) ≫
        (Scheme.Modules.pushforward b).mapCochainComplexPlus.map
          ((openPullPlusIso a b f j h).hom.app K) := by
  apply ObjectProperty.hom_ext
  apply HomologicalComplex.Hom.ext
  funext n
  exact cartesianOpenBaseChange_pullback_unit a b f j h (K.obj.X n)

/-- The cartesian pullback comparison followed by the restricted Godement augmentation. -/
def openTotalBridge (K : CochainComplex.Plus X.Modules) :
    (Scheme.Modules.pullback b).mapCochainComplexPlus.obj
        ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K) ⟶
      (Scheme.Modules.restrictFunctor a).mapCochainComplexPlus.obj
        ((godementTotalPlus U).obj ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)) :=
  (openPullPlusIso a b f j h).hom.app K ≫
    (Scheme.Modules.restrictFunctor a).mapCochainComplexPlus.map
      ((godementTotalPlusUnit U).app ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K))

lemma openTotalBridge_quasiIso (K : CochainComplex.Plus X.Modules) :
    QuasiIso (openTotalBridge a b f j h K).hom := by
  have : QuasiIso ((godementTotalPlusUnit U).app
      ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).hom :=
    godementTotalPlusUnit_quasiIso _ _
  have hres : QuasiIso ((Scheme.Modules.restrictFunctor a).mapCochainComplexPlus.map
      ((godementTotalPlusUnit U).app
        ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K))).hom := by
    exact Complex.restrict_quasiIso a
      ((godementTotalPlusUnit U).app
        ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).hom
  have hiso : IsIso ((openPullPlusIso a b f j h).hom.app K) := inferInstance
  let e := (CochainComplex.Plus.ι W.Modules).mapIso ((openPullPlusIso a b f j h).app K)
  have : IsIso ((openPullPlusIso a b f j h).hom.app K).hom := by
    change IsIso e.hom
    infer_instance
  unfold openTotalBridge
  change QuasiIso (((openPullPlusIso a b f j h).hom.app K).hom ≫
    ((Scheme.Modules.restrictFunctor a).mapCochainComplexPlus.map _).hom)
  infer_instance

lemma restrictedTotalPlus_flasque (K : CochainComplex.Plus X.Modules) (n : ℤ) :
    let J := (Scheme.Modules.restrictFunctor a).mapCochainComplexPlus.obj
      ((godementTotalPlus U).obj ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K))
    TopCat.Presheaf.IsFlasque (J.obj.X n).presheaf := by
  dsimp only
  let C := (Scheme.Modules.pullback f).mapCochainComplexPlus.obj K
  exact @Scheme.Modules.restrictModule_isFlasque W U a inferInstance
    (((godementTotalPlus U).obj C).obj.X n) (totalPlus_terms_isFlasque U C n)

/-- The resolved pullback/direct-image complex for f restricted along the open immersion j. -/
def restrictedPullbackPushforwardPlus (K : CochainComplex.Plus X.Modules) : CochainComplex.Plus
  V.Modules :=
  (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj ((pullbackPushforwardPlus f).obj K)

/-- The resolved pullback/direct-image complex for b applied to the complex restricted along j. -/
def localPullbackPushforwardPlus (K : CochainComplex.Plus X.Modules) : CochainComplex.Plus
  V.Modules :=
  (pullbackPushforwardPlus b).obj ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K)

/-- The restriction along a of the Godement total of the complex pulled back along f. -/
abbrev restrictedTotalPlus (K : CochainComplex.Plus X.Modules) : CochainComplex.Plus W.Modules :=
  (Scheme.Modules.restrictFunctor a).mapCochainComplexPlus.obj
    ((godementTotalPlus U).obj ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K))

/-- The common span target obtained by further Godement totalization and direct image of the
restricted source total. -/
def openBaseChangeSpanTarget (K : CochainComplex.Plus X.Modules) : CochainComplex.Plus V.Modules :=
  (Scheme.Modules.pushforward b).mapCochainComplexPlus.obj
    ((godementTotalPlus W).obj (restrictedTotalPlus a f K))

/-- The resolved pullback/direct-image unit after restriction along j. -/
def restrictedPullbackPushforwardPlusUnit (K : CochainComplex.Plus X.Modules) :
    (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K ⟶
      restrictedPullbackPushforwardPlus f j K :=
  (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.map ((pullbackPushforwardPlusUnit
    f).app K)

/-- The cartesian open direct-image comparison on the resolved pullback complex. -/
def openPullbackPushforwardComparison (K : CochainComplex.Plus X.Modules) :
    restrictedPullbackPushforwardPlus f j K ≅
      (Scheme.Modules.pushforward b).mapCochainComplexPlus.obj (restrictedTotalPlus a f K) :=
  (openPushPlusIso a b f j h).app
    ((godementTotalPlus U).obj ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K))

/-- The direct image of the Godement augmentation on the restricted source total. -/
def openBaseChangeGlobalLeg (K : CochainComplex.Plus X.Modules) :
    (Scheme.Modules.pushforward b).mapCochainComplexPlus.obj (restrictedTotalPlus a f K) ⟶
      openBaseChangeSpanTarget a b f K :=
  (Scheme.Modules.pushforward b).mapCochainComplexPlus.map
    ((godementTotalPlusUnit W).app (restrictedTotalPlus a f K))

/-- The direct image of the Godement-total map induced by the cartesian bridge. -/
def openBaseChangeLocalLeg (K : CochainComplex.Plus X.Modules) :
    localPullbackPushforwardPlus b j K ⟶ openBaseChangeSpanTarget a b f K :=
  (Scheme.Modules.pushforward b).mapCochainComplexPlus.map
    ((godementTotalPlus W).map (openTotalBridge a b f j h K))

lemma restrictedPullbackPushforwardPlusUnit_factor (K : CochainComplex.Plus X.Modules) :
    restrictedPullbackPushforwardPlusUnit f j K =
      (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.map
          ((Plus.pullbackPushforwardUnit f).app K) ≫
        ((Scheme.Modules.pushforward f).mapCochainComplexPlus ⋙
          (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus).map
            ((godementTotalPlusUnit U).app
              ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)) := by
  unfold restrictedPullbackPushforwardPlusUnit
  rw [pullbackPushforwardPlusUnit_app, Functor.map_comp]
  rfl

lemma openBaseChangeGlobalLeg_quasiIso (K : CochainComplex.Plus X.Modules) :
    QuasiIso (openBaseChangeGlobalLeg a b f K).hom := by
  have : QuasiIso ((godementTotalPlusUnit W).app (restrictedTotalPlus a f K)).hom :=
    godementTotalPlusUnit_quasiIso _ _
  exact Plus.pushforward_quasiIso_of_flasque b _
    (restrictedTotalPlus_flasque a f K) (totalPlus_terms_isFlasque W (restrictedTotalPlus a f K))

lemma openBaseChangeLocalLeg_quasiIso (K : CochainComplex.Plus X.Modules) :
    QuasiIso (openBaseChangeLocalLeg a b f j h K).hom := by
  have : QuasiIso (openTotalBridge a b f j h K).hom :=
    openTotalBridge_quasiIso a b f j h K
  have : QuasiIso ((godementTotalPlus W).map (openTotalBridge a b f j h K)).hom :=
    godementTotalPlus_map_quasiIso _
  exact Plus.pushforward_quasiIso_of_flasque b _ (totalPlus_terms_isFlasque W _)
    (totalPlus_terms_isFlasque W _)

private lemma augmentation_component_naturality {C : Type*} [Category C] [HasZeroMorphisms C]
    (T : CochainComplex.Plus C ⥤ CochainComplex.Plus C) (η : 𝟭 _ ⟶ T)
    (K L : CochainComplex.Plus C) (s : K ⟶ L) (n : ℤ) :
    s.hom.f n ≫ (η.app L).hom.f n = (η.app K).hom.f n ≫ (T.map s).hom.f n := by
  exact congrArg (fun q => q.hom.f n) (η.naturality s)

lemma openTotalBridge_f (K : CochainComplex.Plus X.Modules) (n : ℤ) :
    (openTotalBridge a b f j h K).hom.f n =
      (cartesianPullbackBaseChangeMate a b f j h).app (K.obj.X n) ≫
        (Scheme.Modules.restrictFunctor a).map
          (((godementTotalPlusUnit U).app
            ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).hom.f n) := rfl

lemma local_total_unit_component (K : CochainComplex.Plus X.Modules) (n : ℤ) :
    ((cartesianPullbackBaseChangeMate a b f j h).app (K.obj.X n) ≫
      (Scheme.Modules.restrictFunctor a).map
        (((godementTotalPlusUnit U).app
          ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).hom.f n)) ≫
      ((godementTotalPlusUnit W).app (restrictedTotalPlus a f K)).hom.f n =
    ((godementTotalPlusUnit W).app ((Scheme.Modules.pullback b).mapCochainComplexPlus.obj
      ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K))).hom.f n ≫
        ((godementTotalPlus W).map (openTotalBridge a b f j h K)).hom.f n := by
  rw [← openTotalBridge_f]
  exact augmentation_component_naturality (godementTotalPlus W) (godementTotalPlusUnit W)
    ((Scheme.Modules.pullback b).mapCochainComplexPlus.obj
      ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K))
    (restrictedTotalPlus a f K) (openTotalBridge a b f j h K) n

lemma open_component_first_square (K : CochainComplex.Plus X.Modules) (n : ℤ) :
    (((Scheme.Modules.restrictFunctor j).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (K.obj.X n))) ≫
        (Scheme.Modules.restrictFunctor j).map ((Scheme.Modules.pushforward f).map
          (((godementTotalPlusUnit U).app
            ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).hom.f n))) ≫
      (cartesianOpenBaseChange a b f j h).hom.app
        (((godementTotalPlus U).obj
          ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).obj.X n) =
    (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app
      ((Scheme.Modules.restrictFunctor j).obj (K.obj.X n)) ≫
    (Scheme.Modules.pushforward b).map
      ((cartesianPullbackBaseChangeMate a b f j h).app (K.obj.X n) ≫
        (Scheme.Modules.restrictFunctor a).map
          (((godementTotalPlusUnit U).app
            ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).hom.f n)) := by
  let u : (Scheme.Modules.pullback f).obj (K.obj.X n) ⟶
      ((godementTotalPlus U).obj
        ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).obj.X n :=
    ((godementTotalPlusUnit U).app
      ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).hom.f n
  have hn := (cartesianOpenBaseChange a b f j h).hom.naturality u
  dsimp only [Functor.comp_map] at hn
  have he := cartesianOpenBaseChange_pullback_unit a b f j h (K.obj.X n)
  rw [Category.assoc, hn]
  rw [← Category.assoc ((Scheme.Modules.restrictFunctor j).map
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (K.obj.X n))), he]
  simp only [Functor.map_comp, Category.assoc, u]

lemma open_component_second_square (K : CochainComplex.Plus X.Modules) (n : ℤ) :
    (Scheme.Modules.pushforward b).map
      ((cartesianPullbackBaseChangeMate a b f j h).app (K.obj.X n) ≫
        (Scheme.Modules.restrictFunctor a).map
          (((godementTotalPlusUnit U).app
            ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).hom.f n)) ≫
      (Scheme.Modules.pushforward b).map
        (((godementTotalPlusUnit W).app (restrictedTotalPlus a f K)).hom.f n) =
    (Scheme.Modules.pushforward b).map
      (((godementTotalPlusUnit W).app ((Scheme.Modules.pullback b).mapCochainComplexPlus.obj
        ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K))).hom.f n) ≫
      (Scheme.Modules.pushforward b).map
        (((godementTotalPlus W).map (openTotalBridge a b f j h K)).hom.f n) := by
  have ht := congrArg (Scheme.Modules.pushforward b).map
    (local_total_unit_component a b f j h K n)
  simpa only [Functor.map_comp] using ht

lemma open_unit_span_component (K : CochainComplex.Plus X.Modules) (n : ℤ) :
    (((Scheme.Modules.restrictFunctor j).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (K.obj.X n))) ≫
        (Scheme.Modules.restrictFunctor j).map ((Scheme.Modules.pushforward f).map
          (((godementTotalPlusUnit U).app
            ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).hom.f n))) ≫
      (cartesianOpenBaseChange a b f j h).hom.app
        (((godementTotalPlus U).obj
          ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).obj.X n) ≫
      (Scheme.Modules.pushforward b).map
        (((godementTotalPlusUnit W).app (restrictedTotalPlus a f K)).hom.f n) =
      ((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app
        ((Scheme.Modules.restrictFunctor j).obj (K.obj.X n)) ≫
      (Scheme.Modules.pushforward b).map
        (((godementTotalPlusUnit W).app ((Scheme.Modules.pullback b).mapCochainComplexPlus.obj
          ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K))).hom.f n)) ≫
      (Scheme.Modules.pushforward b).map
        (((godementTotalPlus W).map (openTotalBridge a b f j h K)).hom.f n) := by
  rw [← Category.assoc, open_component_first_square, Category.assoc,
    open_component_second_square]
  simp only [Category.assoc]

lemma open_unit_span_factorized (K : CochainComplex.Plus X.Modules) :
    ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.map
        ((Plus.pullbackPushforwardUnit f).app K) ≫
      ((Scheme.Modules.pushforward f).mapCochainComplexPlus ⋙
        (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus).map
          ((godementTotalPlusUnit U).app
            ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K))) ≫
      (openPullbackPushforwardComparison a b f j h K).hom ≫ openBaseChangeGlobalLeg a b f K =
    ((Plus.pullbackPushforwardUnit b).app
        ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K) ≫
      (Scheme.Modules.pushforward b).mapCochainComplexPlus.map
        ((godementTotalPlusUnit W).app ((Scheme.Modules.pullback b).mapCochainComplexPlus.obj
          ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K)))) ≫
      openBaseChangeLocalLeg a b f j h K := by
  apply ObjectProperty.hom_ext
  apply HomologicalComplex.Hom.ext
  funext n
  exact open_unit_span_component a b f j h K n

lemma open_unit_span (K : CochainComplex.Plus X.Modules) :
    restrictedPullbackPushforwardPlusUnit f j K ≫ (openPullbackPushforwardComparison a b f j h
      K).hom ≫
        openBaseChangeGlobalLeg a b f K =
      (pullbackPushforwardPlusUnit b).app
          ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K) ≫
        openBaseChangeLocalLeg a b f j h K := by
  rw [restrictedPullbackPushforwardPlusUnit_factor, pullbackPushforwardPlusUnit_app]
  exact open_unit_span_factorized a b f j h K

include h in
theorem pullbackPushforwardPlusUnit_restrict_quasiIso (K : CochainComplex.Plus X.Modules)
    (hK : QuasiIso ((pullbackPushforwardPlusUnit b).app
      ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K)).hom) :
    QuasiIso ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.map
      ((pullbackPushforwardPlusUnit f).app K)).hom := by
  exact Plus.quasiIso_of_span (restrictedPullbackPushforwardPlusUnit f j K)
    (openPullbackPushforwardComparison a b f j h K).hom (openBaseChangeGlobalLeg a b f K)
    ((pullbackPushforwardPlusUnit b).app ((Scheme.Modules.restrictFunctor
      j).mapCochainComplexPlus.obj K))
    (openBaseChangeLocalLeg a b f j h K) (open_unit_span a b f j h K)
    (openBaseChangeGlobalLeg_quasiIso a b f K) hK (openBaseChangeLocalLeg_quasiIso a b f j h K)

end Godement
end AlgebraicGeometry.Scheme.Modules
