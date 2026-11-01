/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.FiniteTracePairing.Compatibility

/-!
# The original finite trace pairing through an open Cartesian square

The module lift retains the original finite/open comparison. Its completion
map is finite and may ramify. The same finite comparison and original Ext
adjunctions keep source, compact module and abelian Ext worlds independent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u wX wY

section OpenTransferPairing

universe uC vC uD vD uE vE uF vF wU wV

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{wV} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasExt.{wU} D]
  {E : Type uE} [Category.{vE} E] [Abelian E] [HasExt.{wY} E]
  {F : Type uF} [Category.{vF} F] [Abelian F] [HasExt.{wX} F]
  (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (I : D ⥤ C) [I.Additive] [PreservesFiniteLimits I] [PreservesFiniteColimits I]
  (JX : D ⥤ F) [JX.Additive] [PreservesFiniteLimits JX] [PreservesFiniteColimits JX]
  (JY : C ⥤ E) [JY.Additive] [PreservesFiniteLimits JY] [PreservesFiniteColimits JY]
  (Dp : E ⥤ F) [Dp.Additive] [PreservesFiniteLimits Dp] [PreservesFiniteColimits Dp]

private theorem _finiteOpen_transfer_pairing
    (adj : L ⊣ I) (γ : L ⋙ JX ≅ JY ⋙ Dp) (SX : F) (SY : E)
    (U : ∀ (M : E) (q : ℕ), Ext.{wX} SX (Dp.obj M) q ≃+ Ext.{wY} SY M q)
    (hU : ∀ {M N : E} {r s t : ℕ}
      (c : Ext.{wX} SX (Dp.obj M) r) (x : Ext.{wY} M N s) (h : r + s = t),
      U N t (c.comp (Ext.mapExactFunctor.{wY, wX} Dp x) h) = (U M r c).comp x h)
    (EX : ∀ (P : C) (q : ℕ),
      Ext.{wX} SX (JX.obj (L.obj P)) q ≃+ Ext.{wY} SY (JY.obj P) q)
    (hEX : ∀ P q c, EX P q c =
      U (JY.obj P) q (c.comp (Ext.mk₀ (γ.hom.app P)) (add_zero q)))
    (N : D) (N' : C) (ρ : I.obj N ≅ N')
    {P : C} {r s t : ℕ} (h : r + s = t)
    (EY : Ext.{wU} (L.obj P) N s → Ext.{wV} P N' s)
    (hEY : ∀ e, EY e =
      (Adjunction.extEquiv.{wV, wU} adj e).comp (Ext.mk₀ ρ.hom) (add_zero s))
    (T : Ext.{wY} SY (JY.obj N') t → Ext.{wX} SX (JX.obj N) t)
    (hT : ∀ b, T b = ((EX (I.obj N) t).symm
      (b.comp (Ext.mk₀ (JY.map ρ.inv)) (add_zero t))).comp
        (Ext.mk₀ (JX.map (adj.counit.app N))) (add_zero t))
    (c : Ext.{wX} SX (JX.obj (L.obj P)) r) (e : Ext.{wU} (L.obj P) N s) :
    T (Functor.extPairing.{wV, wY} JY SY (EX P r c) (EY e) h) =
      Functor.extPairing.{wU, wX} JX SX c e h := by
  let a : Ext.{wV} P (I.obj N) s := Adjunction.extEquiv.{wV, wU} adj e
  let c₀ := c.comp (Ext.mk₀ (γ.hom.app P)) (add_zero r)
  let bK := Functor.extPairing.{wV, wX} (JY ⋙ Dp) SX c₀ a h
  let bY := Functor.extPairing.{wV, wY} JY SY (EX P r c) a h
  have hp := Functor.extPairing_eq_comp_counit.{wV, wU, wX}
    (P := L) (Q := JX) (K := JY ⋙ Dp) (τ := γ.symm) adj c e h
  simp only [Functor.extPairingCompAddEquiv_apply, Iso.symm_inv, Iso.symm_hom] at hp
  have hcomp : Ext.mapExactFunctor.{wV, wX} (JY ⋙ Dp) a =
      Ext.mapExactFunctor.{wY, wX} Dp (Ext.mapExactFunctor.{wV, wY} JY a) :=
    Ext.comp_mapExactFunctor.{wV, wY, wX} a JY Dp
  have he : U (JY.obj (I.obj N)) t bK = bY := by
    change U (JY.obj (I.obj N)) t
        (c₀.comp (Ext.mapExactFunctor.{wV, wX} (JY ⋙ Dp) a) h) =
      (EX P r c).comp (Ext.mapExactFunctor.{wV, wY} JY a) h
    rw [hcomp, hU, hEX]
  have hEXinv : EX (I.obj N) t
      (bK.comp (Ext.mk₀ (γ.inv.app (I.obj N))) (add_zero t)) = bY := by
    rw [hEX, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
      Iso.inv_hom_id_app, Ext.comp_mk₀_id]
    exact he
  have hi : (EX (I.obj N) t).symm bY =
      bK.comp (Ext.mk₀ (γ.inv.app (I.obj N))) (add_zero t) :=
    (congrArg (EX (I.obj N) t).symm hEXinv).symm.trans
      ((EX (I.obj N) t).symm_apply_apply _)
  have hroot :
      (Functor.extPairing.{wV, wY} JY SY (EX P r c) (EY e) h).comp
        (Ext.mk₀ (JY.map ρ.inv)) (add_zero t) = bY := by
    rw [hEY, Functor.extPairing_comp_mk₀.{wV, wY},
      Ext.comp_assoc_of_third_deg_zero.{wY}, Ext.mk₀_comp_mk₀.{wY},
      ← JY.map_comp, Iso.hom_inv_id, JY.map_id, Ext.comp_mk₀_id.{wY}]
  rw [hT, hroot, hi, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  exact hp.symm

end OpenTransferPairing

private theorem _finiteOpen_original_counit_comparison
    {A B : Type*} [Category* A] [Category* B]
    {L F : A ⥤ B} {R : B ⥤ A} (a : L ⊣ R) (κ : L ≅ F) (N : B) :
    κ.hom.app (R.obj N) ≫ (a.ofNatIsoLeft κ).counit.app N = a.counit.app N := by
  change κ.hom.app (R.obj N) ≫ κ.inv.app (R.obj N) ≫ a.counit.app N = _
  rw [Iso.hom_inv_id_app_assoc]

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard moduleSheafExtZModModule

private theorem _finiteOpen_roots_counit_underlying
    {V U : Scheme.{u}} (g : V ⟶ U) [Etale g] [IsFinite g]
    (m d : ℕ) (hd : ∀ x : U, g.finrank x = d) :
    (SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod m)))).map
        ((moduleLowerShriekAdjunction g (ULift.{u + 1} (ZMod m))).counit.app
          (moduleRootsOfUnity U m)) ≫ (moduleRootsOfUnityUnderlyingIso U m).hom =
      ((SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod m)))).map
          ((moduleFiniteEtaleLowerShriekDirectImageIso g m d hd).hom.app
            ((moduleInverseImage g (ULift.{u + 1} (ZMod m))).obj
              (moduleRootsOfUnity U m))) ≫
        (moduleDirectImageUnderlyingIso g (ULift.{u + 1} (ZMod m))).hom.app
          ((moduleInverseImage g (ULift.{u + 1} (ZMod m))).obj
            (moduleRootsOfUnity U m))) ≫
      (directImage g).map
        ((moduleInverseImageUnderlyingIso (ULift.{u + 1} (ZMod m)) g).hom.app
            (moduleRootsOfUnity U m) ≫
          (inverseImage g).map (moduleRootsOfUnityUnderlyingIso U m).hom) ≫
      (finiteEtaleSheafTrace (Scheme.FiniteEtale.mk g) d hd).app
        (GroupCohomology.Kummer.Coefficients.mu U m) := by
  let Λ := ULift.{u + 1} (ZMod m)
  let UU := SheafOfModules.toSheaf (constantRing U Λ)
  have hk := _finiteOpen_original_counit_comparison
    (moduleLowerShriekAdjunction g Λ) (moduleFiniteEtaleLowerShriekDirectImageIso g m d hd)
    (moduleRootsOfUnity U m)
  have hc := moduleFiniteEtaleDirectImageAdjunction_counit_underlying g m d hd
    (moduleRootsOfUnity U m)
  change UU.map (((moduleLowerShriekAdjunction g Λ).ofNatIsoLeft
      (moduleFiniteEtaleLowerShriekDirectImageIso g m d hd)).counit.app
      (moduleRootsOfUnity U m)) = _ at hc
  have ht := (finiteEtaleSheafTrace (Scheme.FiniteEtale.mk g) d hd).naturality
    (moduleRootsOfUnityUnderlyingIso U m).hom
  dsimp only [Functor.comp_map, Functor.id_map] at ht
  rw [← hk, UU.map_comp, hc]
  simp only [Category.assoc]
  rw [← ht, (directImage g).map_comp]
  simp only [Over.mk_hom, Category.assoc]
  rfl

section FiniteCartesianOpen

variable {V U YC XC : Scheme.{u}} (p : YC ⟶ XC) [IsFinite p]
  (g : V ⟶ U) (jU : U ⟶ XC) [IsOpenImmersion jU]
  (jV : V ⟶ YC) [IsOpenImmersion jV] (h : IsPullback jV g p jU) (m : ℕ)

/-- The original abelian finite/open comparison, transported through the
selected module coefficient isomorphisms and functor associators. -/
def finiteOpenModuleUnderlyingIso :
    (moduleDirectImage g (ULift.{u + 1} (ZMod m)) ⋙
        moduleLowerShriek jU (ULift.{u + 1} (ZMod m))) ⋙
      SheafOfModules.toSheaf (constantRing XC (ULift.{u + 1} (ZMod m))) ≅
    (moduleLowerShriek jV (ULift.{u + 1} (ZMod m)) ⋙
        moduleDirectImage p (ULift.{u + 1} (ZMod m))) ⋙
      SheafOfModules.toSheaf (constantRing XC (ULift.{u + 1} (ZMod m))) :=
  let Λ := ULift.{u + 1} (ZMod m)
  let QX := SheafOfModules.toSheaf (constantRing XC Λ)
  let QU := SheafOfModules.toSheaf (constantRing U Λ)
  let QY := SheafOfModules.toSheaf (constantRing YC Λ)
  let QV := SheafOfModules.toSheaf (constantRing V Λ)
  let Dg := moduleDirectImage g Λ
  let Dp := moduleDirectImage p Λ
  let JX := moduleLowerShriek jU Λ
  let JY := moduleLowerShriek jV Λ
  Functor.associator Dg JX QX ≪≫
    Functor.isoWhiskerLeft Dg (moduleLowerShriekUnderlyingIso jU Λ) ≪≫
    (Functor.associator Dg QU (etaleLowerShriek jU)).symm ≪≫
    Functor.isoWhiskerRight (moduleDirectImageUnderlyingIso g Λ) (etaleLowerShriek jU) ≪≫
    Functor.associator QV (directImage g) (etaleLowerShriek jU) ≪≫
    Functor.isoWhiskerLeft QV (finiteLowerShriekDirectImageIso p g jU jV h) ≪≫
    (Functor.associator QV (etaleLowerShriek jV) (directImage p)).symm ≪≫
    Functor.isoWhiskerRight (moduleLowerShriekUnderlyingIso jV Λ).symm (directImage p) ≪≫
    Functor.associator JY QY (directImage p) ≪≫
    Functor.isoWhiskerLeft JY (moduleDirectImageUnderlyingIso p Λ).symm ≪≫
    (Functor.associator JY Dp QX).symm

/-- The module lift of the SAME original finite/open comparison. Its underlying
isomorphism uses only the selected coefficient comparisons and the proved
abelian finite/open isomorphism; the completion is only required to be finite. -/
def moduleFiniteOpenDirectImageIso :
    moduleDirectImage g (ULift.{u + 1} (ZMod m)) ⋙
        moduleLowerShriek jU (ULift.{u + 1} (ZMod m)) ≅
      moduleLowerShriek jV (ULift.{u + 1} (ZMod m)) ⋙
        moduleDirectImage p (ULift.{u + 1} (ZMod m)) :=
  letI := moduleSheaf_uLiftZMod_toSheaf_full XC m
  let H := (Functor.whiskeringRight (ModuleSheaf V (ULift.{u + 1} (ZMod m)))
    (ModuleSheaf XC (ULift.{u + 1} (ZMod m))) (AbelianSheaf.{u, u + 1} XC)).obj
      (SheafOfModules.toSheaf (constantRing XC (ULift.{u + 1} (ZMod m))))
  H.preimageIso (finiteOpenModuleUnderlyingIso p g jU jV h m)

private theorem moduleFiniteOpenDirectImageIso_underlying :
    Functor.whiskerRight (moduleFiniteOpenDirectImageIso p g jU jV h m).hom
        (SheafOfModules.toSheaf (constantRing XC (ULift.{u + 1} (ZMod m)))) =
      (finiteOpenModuleUnderlyingIso p g jU jV h m).hom := by
  let := moduleSheaf_uLiftZMod_toSheaf_full XC m
  let H := (Functor.whiskeringRight (ModuleSheaf V (ULift.{u + 1} (ZMod m)))
    (ModuleSheaf XC (ULift.{u + 1} (ZMod m))) (AbelianSheaf.{u, u + 1} XC)).obj
      (SheafOfModules.toSheaf (constantRing XC (ULift.{u + 1} (ZMod m))))
  change H.map (H.preimage (finiteOpenModuleUnderlyingIso p g jU jV h m).hom) = _
  exact H.map_preimage _

/-- On every coefficient the module lift retains the original abelian
finite/open arrow under the selected underlying comparisons. -/
theorem moduleFiniteOpenDirectImageIso_underlying_app
    (P : ModuleSheaf V (ULift.{u + 1} (ZMod m))) :
    (SheafOfModules.toSheaf (constantRing XC (ULift.{u + 1} (ZMod m)))).map
        ((moduleFiniteOpenDirectImageIso p g jU jV h m).hom.app P) ≫
      (moduleDirectImageUnderlyingIso p (ULift.{u + 1} (ZMod m))).hom.app
        ((moduleLowerShriek jV (ULift.{u + 1} (ZMod m))).obj P) ≫
      (directImage p).map
        ((moduleLowerShriekUnderlyingIso jV (ULift.{u + 1} (ZMod m))).hom.app P) =
    (moduleLowerShriekUnderlyingIso jU (ULift.{u + 1} (ZMod m))).hom.app
        ((moduleDirectImage g (ULift.{u + 1} (ZMod m))).obj P) ≫
      (etaleLowerShriek jU).map
        ((moduleDirectImageUnderlyingIso g (ULift.{u + 1} (ZMod m))).hom.app P) ≫
      (finiteLowerShriekDirectImageMap p g jU jV h).app
        ((SheafOfModules.toSheaf (constantRing V (ULift.{u + 1} (ZMod m)))).obj P) := by
  have hwhole := NatTrans.congr_app
    (moduleFiniteOpenDirectImageIso_underlying p g jU jV h m) P
  simp only [finiteOpenModuleUnderlyingIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, finiteLowerShriekDirectImageIso_hom,
    Category.id_comp,
    Category.comp_id] at hwhole
  rw [hwhole]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← (directImage p).map_comp,
    Iso.inv_hom_id_app, (directImage p).map_id]
  dsimp only [Functor.comp_obj]
  rw [Category.comp_id]

variable [Etale g] (d : ℕ) (hd : ∀ x : U, g.finrank x = d)

/-- The SAME finite comparison followed by the module lift of the original
finite/open Cartesian comparison. The completion is only finite. -/
def moduleFiniteOpenLowerShriekIso :
    moduleLowerShriek g (ULift.{u + 1} (ZMod m)) ⋙
        moduleLowerShriek jU (ULift.{u + 1} (ZMod m)) ≅
      moduleLowerShriek jV (ULift.{u + 1} (ZMod m)) ⋙
        moduleDirectImage p (ULift.{u + 1} (ZMod m)) := by
  let : IsFinite g := MorphismProperty.of_isPullback h (inferInstance : IsFinite p)
  exact Functor.isoWhiskerRight (moduleFiniteEtaleLowerShriekDirectImageIso g m d hd)
      (moduleLowerShriek jU (ULift.{u + 1} (ZMod m))) ≪≫
    moduleFiniteOpenDirectImageIso p g jU jV h m

/-- The whole underlying coefficient square for the SAME finite comparison
followed by the original finite/open Cartesian comparison. -/
theorem moduleFiniteOpenLowerShriekIso_underlying_app
    (P : ModuleSheaf V (ULift.{u + 1} (ZMod m))) :
    let : IsFinite g := MorphismProperty.of_isPullback h (inferInstance : IsFinite p)
    (SheafOfModules.toSheaf (constantRing XC (ULift.{u + 1} (ZMod m)))).map
        ((moduleFiniteOpenLowerShriekIso p g jU jV h m d hd).hom.app P) ≫
      (moduleDirectImageUnderlyingIso p (ULift.{u + 1} (ZMod m))).hom.app
        ((moduleLowerShriek jV (ULift.{u + 1} (ZMod m))).obj P) ≫
      (directImage p).map
        ((moduleLowerShriekUnderlyingIso jV (ULift.{u + 1} (ZMod m))).hom.app P) =
    (moduleLowerShriekUnderlyingIso jU (ULift.{u + 1} (ZMod m))).hom.app
        ((moduleLowerShriek g (ULift.{u + 1} (ZMod m))).obj P) ≫
      (etaleLowerShriek jU).map
        ((SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod m)))).map
            ((moduleFiniteEtaleLowerShriekDirectImageIso g m d hd).hom.app P) ≫
          (moduleDirectImageUnderlyingIso g (ULift.{u + 1} (ZMod m))).hom.app P) ≫
      (finiteLowerShriekDirectImageMap p g jU jV h).app
        ((SheafOfModules.toSheaf (constantRing V (ULift.{u + 1} (ZMod m)))).obj P) := by
  let : IsFinite g := MorphismProperty.of_isPullback h (inferInstance : IsFinite p)
  let Λ := ULift.{u + 1} (ZMod m)
  have hn := (moduleLowerShriekUnderlyingIso jU Λ).hom.naturality
    ((moduleFiniteEtaleLowerShriekDirectImageIso g m d hd).hom.app P)
  dsimp only [Functor.comp_map] at hn
  simp only [moduleFiniteOpenLowerShriekIso, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  rw [moduleFiniteOpenDirectImageIso_underlying_app, reassoc_of% hn]

section OpenCompactExt

variable [HasExt.{wX} (ModuleSheaf XC (ULift.{u + 1} (ZMod m)))]
  [HasExt.{wY} (ModuleSheaf YC (ULift.{u + 1} (ZMod m)))]

local instance finiteOpen_completion_preservesFiniteColimits :
    PreservesFiniteColimits (moduleDirectImage p (ULift.{u + 1} (ZMod m))) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- Original compact Ext transport: the selected module Cartesian comparison
followed by the existing finite unit-Ext equivalence on the completion. -/
def moduleFiniteOpenLowerShriekCompactExtAddEquiv
    (P : ModuleSheaf V (ULift.{u + 1} (ZMod m))) (q : ℕ) :
    Ext.{wX} (moduleUnit XC (ULift.{u + 1} (ZMod m)))
        ((moduleLowerShriek jU (ULift.{u + 1} (ZMod m))).obj
          ((moduleLowerShriek g (ULift.{u + 1} (ZMod m))).obj P)) q ≃+
      Ext.{wY} (moduleUnit YC (ULift.{u + 1} (ZMod m)))
        ((moduleLowerShriek jV (ULift.{u + 1} (ZMod m))).obj P) q :=
  (((extFunctorObj (moduleUnit XC (ULift.{u + 1} (ZMod m))) q).mapIso
      ((moduleFiniteOpenLowerShriekIso p g jU jV h m d hd).app P)).addCommGroupIsoToAddEquiv).trans
    (moduleFiniteUnitExtAddEquiv p m
      ((moduleLowerShriek jV (ULift.{u + 1} (ZMod m))).obj P) q)

/-- Value of the whole comparison without unfolding the selected isomorphism. -/
theorem moduleFiniteOpenLowerShriekCompactExtAddEquiv_apply
    (P : ModuleSheaf V (ULift.{u + 1} (ZMod m))) (q : ℕ)
    (c : Ext.{wX} (moduleUnit XC (ULift.{u + 1} (ZMod m)))
      ((moduleLowerShriek jU (ULift.{u + 1} (ZMod m))).obj
        ((moduleLowerShriek g (ULift.{u + 1} (ZMod m))).obj P)) q) :
    moduleFiniteOpenLowerShriekCompactExtAddEquiv p g jU jV h m d hd P q c =
      moduleFiniteUnitExtAddEquiv p m
        ((moduleLowerShriek jV (ULift.{u + 1} (ZMod m))).obj P) q
        (c.comp (Ext.mk₀
          ((moduleFiniteOpenLowerShriekIso p g jU jV h m d hd).hom.app P)) (add_zero q)) := rfl

section OpenCompactCohomology

universe wAX wAY

variable [HasExt.{wAX} (AbelianSheaf.{u, u + 1} XC)]
  [HasExt.{wAY} (AbelianSheaf.{u, u + 1} YC)]

/-- The entire compact module comparison is the original abelian compact
comparison underneath, on every variable coefficient and class. -/
theorem moduleFiniteOpenLowerShriekCompactExtAddEquiv_cohomology
    (P : ModuleSheaf V (ULift.{u + 1} (ZMod m))) (q : ℕ)
    (c : Ext.{wX} (moduleUnit XC (ULift.{u + 1} (ZMod m)))
      ((moduleLowerShriek jU (ULift.{u + 1} (ZMod m))).obj
        ((moduleLowerShriek g (ULift.{u + 1} (ZMod m))).obj P)) q) :
    let : IsFinite g := MorphismProperty.of_isPullback h (inferInstance : IsFinite p)
    moduleLowerShriekCohomologyAddEquiv jV (ULift.{u + 1} (ZMod m)) P q
        (moduleFiniteOpenLowerShriekCompactExtAddEquiv p g jU jV h m d hd P q c) =
      CompactSupport.finiteDirectImageAddEquiv p g jU jV h
        ((SheafOfModules.toSheaf (constantRing V (ULift.{u + 1} (ZMod m)))).obj P) q
        (CompactSupport.H.map jU
          ((SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod m)))).map
              ((moduleFiniteEtaleLowerShriekDirectImageIso g m d hd).hom.app P) ≫
            (moduleDirectImageUnderlyingIso g (ULift.{u + 1} (ZMod m))).hom.app P) q
          (moduleLowerShriekCohomologyAddEquiv jU (ULift.{u + 1} (ZMod m))
            ((moduleLowerShriek g (ULift.{u + 1} (ZMod m))).obj P) q c)) := by
  let : IsFinite g := MorphismProperty.of_isPullback h (inferInstance : IsFinite p)
  let Λ := ULift.{u + 1} (ZMod m)
  let JY := moduleLowerShriek jV Λ
  let A := (moduleLowerShriek g Λ).obj P
  let γ := (moduleFiniteOpenLowerShriekIso p g jU jV h m d hd).hom.app P
  let c₀ := c.comp (Ext.mk₀ γ) (add_zero q)
  have hf := DFunLike.congr_fun
    (moduleFiniteUnitExtCohomology_square.{u, wX, wY, wAX, wAY}
      p m (JY.obj P) q) c₀
  change etaleModuleExtCohomologyAddEquivLargeScalars YC (constantRing YC Λ) (JY.obj P) q
      (moduleFiniteUnitExtAddEquiv p m (JY.obj P) q c₀) =
    Finite.finiteCohomologyDirectImageAddEquiv p
      ((SheafOfModules.toSheaf (constantRing YC Λ)).obj (JY.obj P)) q
      (Sheaf.H.map ((moduleDirectImageUnderlyingIso p Λ).hom.app (JY.obj P)) q
        (etaleModuleExtCohomologyAddEquivLargeScalars XC (constantRing XC Λ)
          ((moduleDirectImage p Λ).obj (JY.obj P)) q c₀)) at hf
  have hn := Finite.finiteCohomologyDirectImageAddEquiv_naturality p
    ((moduleLowerShriekUnderlyingIso jV Λ).hom.app P) q
    (Sheaf.H.map ((moduleDirectImageUnderlyingIso p Λ).hom.app (JY.obj P)) q
      (etaleModuleExtCohomologyAddEquivLargeScalars XC (constantRing XC Λ)
        ((moduleDirectImage p Λ).obj (JY.obj P)) q c₀))
  have hleft := (congrArg
    (Sheaf.H.map ((moduleLowerShriekUnderlyingIso jV Λ).hom.app P) q) hf).trans hn.symm
  have hγ := moduleFiniteOpenLowerShriekIso_underlying_app p g jU jV h m d hd P
  rw [moduleLowerShriekCohomologyAddEquiv_apply,
    moduleFiniteOpenLowerShriekCompactExtAddEquiv_apply]
  change Sheaf.H.map ((moduleLowerShriekUnderlyingIso jV Λ).hom.app P) q
      (etaleModuleExtCohomologyAddEquivLargeScalars YC (constantRing YC Λ) (JY.obj P) q
        (moduleFiniteUnitExtAddEquiv p m (JY.obj P) q c₀)) = _
  refine hleft.trans ?_
  rw [CompactSupport.finiteDirectImageAddEquiv_apply, CompactSupport.H.map_apply,
    moduleLowerShriekCohomologyAddEquiv_apply, moduleUnitExtAddEquiv_naturality]
  apply congrArg (Finite.finiteCohomologyDirectImageAddEquiv p
    ((etaleLowerShriek jV).obj
      ((SheafOfModules.toSheaf (constantRing V Λ)).obj P)) q)
  rw [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply, hγ]
  simp only [Sheaf.H.map_comp_apply]
  rfl

end OpenCompactCohomology

/-- The derived transfer uses the SAME finite/open compact comparison, the
original roots inverse-image map and the original lower-shriek counit. -/
def moduleFiniteOpenLowerShriekRootsTraceMap
    (hm : 0 < m) (hinv : IsUnit (m : Γ(U, ⊤))) :
    Ext.{wY} (moduleUnit YC (ULift.{u + 1} (ZMod m)))
        ((moduleLowerShriek jV (ULift.{u + 1} (ZMod m))).obj
          (moduleRootsOfUnity V m)) 2 →+
      Ext.{wX} (moduleUnit XC (ULift.{u + 1} (ZMod m)))
        ((moduleLowerShriek jU (ULift.{u + 1} (ZMod m))).obj
          (moduleRootsOfUnity U m)) 2 :=
  ((Ext.mk₀ ((moduleLowerShriek jU (ULift.{u + 1} (ZMod m))).map
      ((moduleLowerShriekAdjunction g (ULift.{u + 1} (ZMod m))).counit.app
        (moduleRootsOfUnity U m)))).postcomp
      (moduleUnit XC (ULift.{u + 1} (ZMod m))) (add_zero 2)).comp
    ((moduleFiniteOpenLowerShriekCompactExtAddEquiv p g jU jV h m d hd
      ((moduleInverseImage g (ULift.{u + 1} (ZMod m))).obj
        (moduleRootsOfUnity U m)) 2).symm.toAddMonoidHom.comp
      ((Ext.mk₀ ((moduleLowerShriek jV (ULift.{u + 1} (ZMod m))).map
        (moduleRootsOfUnityInverseImageIso g m hm hinv).inv)).postcomp
          (moduleUnit YC (ULift.{u + 1} (ZMod m))) (add_zero 2)))

private theorem moduleFiniteOpenLowerShriekRootsTraceMap_apply
    (hm : 0 < m) (hinv : IsUnit (m : Γ(U, ⊤)))
    (b : Ext.{wY} (moduleUnit YC (ULift.{u + 1} (ZMod m)))
      ((moduleLowerShriek jV (ULift.{u + 1} (ZMod m))).obj
        (moduleRootsOfUnity V m)) 2) :
    moduleFiniteOpenLowerShriekRootsTraceMap p g jU jV h m d hd hm hinv b =
      ((moduleFiniteOpenLowerShriekCompactExtAddEquiv p g jU jV h m d hd
        ((moduleInverseImage g (ULift.{u + 1} (ZMod m))).obj
          (moduleRootsOfUnity U m)) 2).symm
        (b.comp (Ext.mk₀ ((moduleLowerShriek jV (ULift.{u + 1} (ZMod m))).map
          (moduleRootsOfUnityInverseImageIso g m hm hinv).inv)) (add_zero 2))).comp
        (Ext.mk₀ ((moduleLowerShriek jU (ULift.{u + 1} (ZMod m))).map
          ((moduleLowerShriekAdjunction g (ULift.{u + 1} (ZMod m))).counit.app
            (moduleRootsOfUnity U m)))) (add_zero 2) := rfl

section IndependentOpenPairingWorlds

universe wU wV

variable [HasExt.{wU} (ModuleSheaf U (ULift.{u + 1} (ZMod m)))]
  [HasExt.{wV} (ModuleSheaf V (ULift.{u + 1} (ZMod m)))]

private theorem moduleFiniteOpenLowerShriekRootsTraceMap_pairing
    (hm : 0 < m) (hinv : IsUnit (m : Γ(U, ⊤)))
    (P : ModuleSheaf V (ULift.{u + 1} (ZMod m))) {r s : ℕ} (hrs : r + s = 2)
    (c : Ext.{wX} (moduleUnit XC (ULift.{u + 1} (ZMod m)))
      ((moduleLowerShriek jU (ULift.{u + 1} (ZMod m))).obj
        ((moduleLowerShriek g (ULift.{u + 1} (ZMod m))).obj P)) r)
    (e : Ext.{wU} ((moduleLowerShriek g (ULift.{u + 1} (ZMod m))).obj P)
      (moduleRootsOfUnity U m) s) :
    moduleFiniteOpenLowerShriekRootsTraceMap.{u, wX, wY}
        p g jU jV h m d hd hm hinv
        (moduleLowerShriekPairing.{wV, wY, u} jV (ULift.{u + 1} (ZMod m))
          (moduleFiniteOpenLowerShriekCompactExtAddEquiv.{u, wX, wY}
            p g jU jV h m d hd P r c)
          (moduleFiniteLowerShriekRootsExtAddEquiv.{u, wU, wV} g m hm hinv P s e) hrs) =
      moduleLowerShriekPairing.{wU, wX, u} jU (ULift.{u + 1} (ZMod m)) c e hrs := by
  apply _finiteOpen_transfer_pairing
    (moduleLowerShriek g (ULift.{u + 1} (ZMod m)))
    (moduleInverseImage g (ULift.{u + 1} (ZMod m)))
    (moduleLowerShriek jU (ULift.{u + 1} (ZMod m)))
    (moduleLowerShriek jV (ULift.{u + 1} (ZMod m)))
    (moduleDirectImage p (ULift.{u + 1} (ZMod m)))
    (moduleLowerShriekAdjunction g (ULift.{u + 1} (ZMod m)))
    (moduleFiniteOpenLowerShriekIso p g jU jV h m d hd)
    (moduleUnit XC (ULift.{u + 1} (ZMod m)))
    (moduleUnit YC (ULift.{u + 1} (ZMod m)))
    (moduleFiniteUnitExtAddEquiv.{u, wX, wY} p m)
    (fun c x h => by
      simpa only [Ext.id_mapExactFunctor] using
        (moduleFiniteUnitExtAddEquiv_pairing.{u, wX, wY, wY} p m c x h))
    (moduleFiniteOpenLowerShriekCompactExtAddEquiv.{u, wX, wY} p g jU jV h m d hd)
    (moduleFiniteOpenLowerShriekCompactExtAddEquiv_apply.{u, wX, wY} p g jU jV h m d hd)
    (moduleRootsOfUnity U m) (moduleRootsOfUnity V m)
    (moduleRootsOfUnityInverseImageIso g m hm hinv) hrs
    (moduleFiniteLowerShriekRootsExtAddEquiv.{u, wU, wV} g m hm hinv P s)
    (moduleFiniteLowerShriekRootsExtAddEquiv_apply.{u, wU, wV} g m hm hinv P s)
    (moduleFiniteOpenLowerShriekRootsTraceMap.{u, wX, wY} p g jU jV h m d hd hm hinv)
    (moduleFiniteOpenLowerShriekRootsTraceMap_apply.{u, wX, wY} p g jU jV h m d hd hm hinv)
    c e

end IndependentOpenPairingWorlds

section OpenTraceCohomology

universe wAX wAY

variable [HasExt.{wAX} (AbelianSheaf.{u, u + 1} XC)]
  [HasExt.{wAY} (AbelianSheaf.{u, u + 1} YC)]

/-- The entire derived module transfer is the ORIGINAL abelian compact roots
transfer underneath, before any Yoneda class is substituted. -/
theorem moduleFiniteOpenLowerShriekRootsTraceMap_cohomology
    (hm : 0 < m) (hinv : IsUnit (m : Γ(U, ⊤)))
    (b : Ext.{wY} (moduleUnit YC (ULift.{u + 1} (ZMod m)))
      ((moduleLowerShriek jV (ULift.{u + 1} (ZMod m))).obj
        (moduleRootsOfUnity V m)) 2) :
    CompactSupport.H.map jU (moduleRootsOfUnityUnderlyingIso U m).hom 2
        (moduleLowerShriekCohomologyAddEquiv jU (ULift.{u + 1} (ZMod m))
          (moduleRootsOfUnity U m) 2
          (moduleFiniteOpenLowerShriekRootsTraceMap p g jU jV h m d hd hm hinv b)) =
      CompactSupport.finiteRootsTraceMap p g jU jV h d hd m hm hinv 2
        (CompactSupport.H.map jV (moduleRootsOfUnityUnderlyingIso V m).hom 2
          (moduleLowerShriekCohomologyAddEquiv jV (ULift.{u + 1} (ZMod m))
            (moduleRootsOfUnity V m) 2 b)) := by
  let : IsFinite g := MorphismProperty.of_isPullback h (inferInstance : IsFinite p)
  let Λ := ULift.{u + 1} (ZMod m)
  let UU := SheafOfModules.toSheaf (constantRing U Λ)
  let VV := SheafOfModules.toSheaf (constantRing V Λ)
  let Q := (moduleInverseImage g Λ).obj (moduleRootsOfUnity U m)
  let ρ := moduleRootsOfUnityInverseImageIso g m hm hinv
  let b₀ := b.comp (Ext.mk₀ ((moduleLowerShriek jV Λ).map ρ.inv)) (add_zero 2)
  let c := (moduleFiniteOpenLowerShriekCompactExtAddEquiv p g jU jV h m d hd Q 2).symm b₀
  let a := (moduleInverseImageUnderlyingIso Λ g).hom.app (moduleRootsOfUnity U m) ≫
    (inverseImage g).map (moduleRootsOfUnityUnderlyingIso U m).hom
  let v := UU.map ((moduleFiniteEtaleLowerShriekDirectImageIso g m d hd).hom.app Q) ≫
    (moduleDirectImageUnderlyingIso g Λ).hom.app Q
  let cA := moduleLowerShriekCohomologyAddEquiv jU Λ
    ((moduleLowerShriek g Λ).obj Q) 2 c
  let bA := moduleLowerShriekCohomologyAddEquiv jV Λ (moduleRootsOfUnity V m) 2 b
  have he := moduleFiniteOpenLowerShriekCompactExtAddEquiv_cohomology p g jU jV h m d hd Q 2 c
  change moduleLowerShriekCohomologyAddEquiv jV Λ Q 2
      ((moduleFiniteOpenLowerShriekCompactExtAddEquiv p g jU jV h m d hd Q 2)
        ((moduleFiniteOpenLowerShriekCompactExtAddEquiv p g jU jV h m d hd Q 2).symm b₀)) =
    CompactSupport.finiteDirectImageAddEquiv p g jU jV h (VV.obj Q) 2
      (CompactSupport.H.map jU v 2 cA) at he
  rw [AddEquiv.apply_symm_apply] at he
  have hb : moduleLowerShriekCohomologyAddEquiv jV Λ Q 2 b₀ =
      CompactSupport.H.map jV (VV.map ρ.inv) 2 bA :=
    moduleLowerShriekCohomologyAddEquiv_naturality jV Λ ρ.inv 2 b
  have hr : VV.map ρ.inv ≫ a = (moduleRootsOfUnityUnderlyingIso V m).hom ≫
      (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso g m hm hinv).inv := by
    have hρ := moduleRootsOfUnityInverseImageIso_underlying g m hm hinv
    apply (cancel_mono
      (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso g m hm hinv).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hρ' : VV.map ρ.hom ≫ (moduleRootsOfUnityUnderlyingIso V m).hom =
        a ≫ (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso g m hm hinv).hom := by
      simpa only [a, Category.assoc] using hρ
    rw [← hρ', ← VV.map_comp_assoc, Iso.inv_hom_id, VV.map_id, Category.id_comp]
  have hcoho :
      CompactSupport.H.map jU ((directImage g).map a) 2
          (CompactSupport.H.map jU v 2 cA) =
        (CompactSupport.finiteDirectImageAddEquiv p g jU jV h
          ((inverseImage g).obj (GroupCohomology.Kummer.Coefficients.mu U m)) 2).symm
            (CompactSupport.H.map jV
              (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso g m hm hinv).inv 2
              (CompactSupport.H.map jV (moduleRootsOfUnityUnderlyingIso V m).hom 2 bA)) := by
    apply (CompactSupport.finiteDirectImageAddEquiv p g jU jV h
      ((inverseImage g).obj (GroupCohomology.Kummer.Coefficients.mu U m)) 2).injective
    rw [AddEquiv.apply_symm_apply]
    have hn := DFunLike.congr_fun
      (CompactSupport.finiteDirectImageAddEquiv_naturality p g jU jV h a 2)
      (CompactSupport.H.map jU v 2 cA)
    change CompactSupport.finiteDirectImageAddEquiv p g jU jV h
        ((inverseImage g).obj (GroupCohomology.Kummer.Coefficients.mu U m)) 2
        (CompactSupport.H.map jU ((directImage g).map a) 2
          (CompactSupport.H.map jU v 2 cA)) =
      CompactSupport.H.map jV a 2
        (CompactSupport.finiteDirectImageAddEquiv p g jU jV h (VV.obj Q) 2
          (CompactSupport.H.map jU v 2 cA)) at hn
    rw [hn, ← he, hb, ← CompactSupport.H.map_comp_apply, hr,
      CompactSupport.H.map_comp_apply]
  have hε := _finiteOpen_roots_counit_underlying g m d hd
  have hT := moduleFiniteOpenLowerShriekRootsTraceMap_apply.{u, wX, wY}
    p g jU jV h m d hd hm hinv b
  have hTcoho := congrArg
    (fun z : Ext.{wX} (moduleUnit XC Λ) ((moduleLowerShriek jU Λ).obj
        (moduleRootsOfUnity U m)) 2 =>
      (CompactSupport.H.map jU (moduleRootsOfUnityUnderlyingIso U m).hom 2
        (moduleLowerShriekCohomologyAddEquiv jU Λ (moduleRootsOfUnity U m) 2 z) :
          Sheaf.H.{wAX} ((etaleLowerShriek jU).obj
            (GroupCohomology.Kummer.Coefficients.mu U m)) 2)) hT
  have hN := congrArg
    (CompactSupport.H.map jU (moduleRootsOfUnityUnderlyingIso U m).hom 2)
    (moduleLowerShriekCohomologyAddEquiv_naturality jU Λ
      ((moduleLowerShriekAdjunction g Λ).counit.app (moduleRootsOfUnity U m)) 2 c)
  have hleft := hTcoho.trans hN
  have hεcoho := congrArg (fun z => (CompactSupport.H.map jU z 2) cA) hε
  simp only [CompactSupport.H.map_comp_apply] at hεcoho
  have hright := congrArg
    (CompactSupport.H.map jU
      ((finiteEtaleSheafTrace (Scheme.FiniteEtale.mk g) d hd).app
        (GroupCohomology.Kummer.Coefficients.mu U m)) 2) hcoho
  dsimp only [v, a, Q, Λ] at hright
  simp only [CompactSupport.H.map_comp_apply] at hright
  have hfinal := hleft.trans (hεcoho.trans hright)
  simpa only [Λ, CompactSupport.finiteRootsTraceMap, CompactSupport.finiteTraceMap,
    AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, bA] using hfinal

end OpenTraceCohomology

end OpenCompactExt

end FiniteCartesianOpen

section OpenFiniteTrace

universe wAX wAY

open Scheme.OverField GroupCohomology.Kummer.CoefficientBaseChange

variable {k : Type u} [Field k] [IsAlgClosed k]
  (C D : FScheme k) (hC : Curve.Properties C) (hD : Curve.Properties D)
  (p : D ⟶ C) [IsFinite p.left] [IsDominant p.left]
  (DX : Set C.left) (hfinX : DX.Finite) (hclosedX : ∀ x ∈ DX, IsClosed ({x} : Set C.left))
  (DY : Set D.left) (hfinY : DY.Finite) (hclosedY : ∀ x ∈ DY, IsClosed ({x} : Set D.left))
  {U V : Scheme.{u}} [Nonempty U] [Nonempty V]
  (jU : U ⟶ C.left) [IsOpenImmersion jU] (hDX : Set.range jU = DXᶜ)
  (jV : V ⟶ D.left) [IsOpenImmersion jV] (hDY : Set.range jV = DYᶜ)
  (g : V ⟶ U) [Etale g] (hsq : IsPullback jV g p.left jU)
  (n d : ℕ) (hd : ∀ x : U, g.finrank x = d)
  (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(C.left, ⊤)))
  [HasExt.{wX} (ModuleSheaf C.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wY} (ModuleSheaf D.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wAX} (AbelianSheaf.{u, u + 1} C.left)]
  [HasExt.{wAY} (AbelianSheaf.{u, u + 1} D.left)]

/-- The whole original open module transfer preserves normalized compact
trace. The finite completion may ramify; degree and positivity are derived
from the actual Cartesian completion by the original abelian trace law. -/
theorem moduleCompactSupportTrace_finiteOpenLowerShriekRootsTrace :
    (moduleCompactSupportTraceAddEquiv C hC DX hfinX hclosedX
        jU hDX n hn hunit hinv).toAddMonoidHom.comp
      (moduleFiniteOpenLowerShriekRootsTraceMap p.left g jU jV hsq n d hd hn
        (levelInvertible jU n hinv)) =
    (moduleCompactSupportTraceAddEquiv D hD DY hfinY hclosedY
      jV hDY n hn hunit (levelInvertible p.left n hinv)).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro b
  change moduleCompactSupportTraceAddEquiv C hC DX hfinX hclosedX jU hDX n hn hunit hinv
      (moduleFiniteOpenLowerShriekRootsTraceMap p.left g jU jV hsq n d hd hn
        (levelInvertible jU n hinv) b) =
    moduleCompactSupportTraceAddEquiv D hD DY hfinY hclosedY jV hDY n hn hunit
      (levelInvertible p.left n hinv) b
  rw [moduleCompactSupportTraceAddEquiv_apply, moduleCompactSupportTraceAddEquiv_apply,
    moduleFiniteOpenLowerShriekRootsTraceMap_cohomology p.left g jU jV hsq n d hd hn
      (levelInvertible jU n hinv)]
  exact DFunLike.congr_fun
    (Curves.compactSupportTraceAddEquiv_finiteRootsTrace hC hD p
      DX hfinX hclosedX DY hfinY hclosedY jU hDX jV hDY g hsq d hd n hn hunit hinv)
    (CompactSupport.H.map jV (moduleRootsOfUnityUnderlyingIso V n).hom 2
      (moduleLowerShriekCohomologyAddEquiv jV (ULift.{u + 1} (ZMod n))
        (moduleRootsOfUnity V n) 2 b))

section AllOpenPairingDegrees

universe wU wV

variable [HasExt.{wU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wV} (ModuleSheaf V (ULift.{u + 1} (ZMod n)))]

/-- The whole original normalized finite/open pairing square in every pair
of complementary degrees. All source, compact module and abelian Ext worlds
remain independent; no coprimality or étale-completion premise is added. -/
theorem moduleTracePairingLinearMap_finiteOpenLowerShriek
    (P : ModuleSheaf V (ULift.{u + 1} (ZMod n))) (r s : ℕ) (hrs : r + s = 2)
    (c : Ext.{wX} (moduleUnit C.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek jU (ULift.{u + 1} (ZMod n))).obj
        ((moduleLowerShriek g (ULift.{u + 1} (ZMod n))).obj P)) r)
    (e : Ext.{wU} ((moduleLowerShriek g (ULift.{u + 1} (ZMod n))).obj P)
      (moduleRootsOfUnity U n) s) :
    moduleTracePairingLinearMap.{u, wU, wX, wAX} C hC DX hfinX hclosedX
        jU hDX n hn hunit hinv ((moduleLowerShriek g (ULift.{u + 1} (ZMod n))).obj P)
        r s hrs c e =
      moduleTracePairingLinearMap.{u, wV, wY, wAY} D hD DY hfinY hclosedY
        jV hDY n hn hunit (levelInvertible p.left n hinv) P r s hrs
        (moduleFiniteOpenLowerShriekCompactExtAddEquiv.{u, wX, wY}
          p.left g jU jV hsq n d hd P r c)
        (moduleFiniteLowerShriekRootsExtAddEquiv.{u, wU, wV}
          g n hn (levelInvertible jU n hinv) P s e) := by
  rw [moduleTracePairingLinearMap_apply_apply, moduleTracePairingLinearMap_apply_apply,
    ← moduleFiniteOpenLowerShriekRootsTraceMap_pairing.{u, wX, wY, wU, wV}
      p.left g jU jV hsq n d hd hn (levelInvertible jU n hinv) P hrs c e]
  exact DFunLike.congr_fun
    (moduleCompactSupportTrace_finiteOpenLowerShriekRootsTrace.{u, wX, wY, wAX, wAY}
      C D hC hD p DX hfinX hclosedX DY hfinY hclosedY jU hDX jV hDY g hsq
      n d hd hn hunit hinv)
    (moduleLowerShriekPairing.{wV, wY, u} jV (ULift.{u + 1} (ZMod n))
      (moduleFiniteOpenLowerShriekCompactExtAddEquiv.{u, wX, wY}
        p.left g jU jV hsq n d hd P r c)
      (moduleFiniteLowerShriekRootsExtAddEquiv.{u, wU, wV}
        g n hn (levelInvertible jU n hinv) P s e) hrs)

end AllOpenPairingDegrees

end OpenFiniteTrace

end AlgebraicGeometry.Scheme.EtaleCohomology
