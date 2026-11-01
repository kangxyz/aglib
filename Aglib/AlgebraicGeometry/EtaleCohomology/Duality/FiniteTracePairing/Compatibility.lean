/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.FiniteTracePairing
public import Aglib.Algebra.Homology.DerivedCategory.Ext.PairingComposition

/-!
# Compatibility of the original finite trace pairing in all degrees

The original finite compact and source transports preserve the whole normalized
pairing. Source and compact Ext worlds stay independent. The proper comparison
uses only the already selected identity isomorphisms and finite comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u wX wY

section TransferPairing

universe uC vC uD vD wSX wSY

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [HasExt.{wSY} C] [HasExt.{wY} C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasExt.{wSX} D] [HasExt.{wX} D]
  (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (I : D ⥤ C) [I.Additive] [PreservesFiniteLimits I] [PreservesFiniteColimits I]
  (JX : D ⥤ D) [JX.Additive] [PreservesFiniteLimits JX] [PreservesFiniteColimits JX]
  (JY : C ⥤ C) [JY.Additive] [PreservesFiniteLimits JY] [PreservesFiniteColimits JY]

private theorem _compatibility_transfer_pairing
    (adj : L ⊣ I) (SX : D) (SY : C)
    (E : ∀ (P : C) (q : ℕ),
      Ext.{wX} SX (JX.obj (L.obj P)) q ≃+ Ext.{wY} SY (JY.obj P) q)
    (hE : ∀ {P Q : C} {r s t : ℕ}
      (c : Ext.{wX} SX (JX.obj (L.obj P)) r) (x : Ext.{wSY} P Q s)
      (h : r + s = t),
      E Q t (Functor.extPairing.{wSX, wX} JX SX c
          (Ext.mapExactFunctor.{wSY, wSX} L x) h) =
        Functor.extPairing.{wSY, wY} JY SY (E P r c) x h)
    (N : D) (N' : C) (ρ : I.obj N ≅ N')
    {P : C} {r s t : ℕ} (h : r + s = t)
    (EY : Ext.{wSX} (L.obj P) N s → Ext.{wSY} P N' s)
    (hEY : ∀ e, EY e = (Adjunction.extEquiv.{wSY, wSX} adj e).comp (Ext.mk₀ ρ.hom) (add_zero s))
    (T : Ext.{wY} SY (JY.obj N') t → Ext.{wX} SX (JX.obj N) t)
    (hT : ∀ b, T b =
      ((E (I.obj N) t).symm
        (b.comp (Ext.mk₀ (JY.map ρ.inv)) (add_zero t))).comp
          (Ext.mk₀ (JX.map (adj.counit.app N))) (add_zero t))
    (c : Ext.{wX} SX (JX.obj (L.obj P)) r) (e : Ext.{wSX} (L.obj P) N s) :
    T (Functor.extPairing.{wSY, wY} JY SY (E P r c) (EY e) h) =
      Functor.extPairing.{wSX, wX} JX SX c e h := by
  let a : Ext.{wSY} P (I.obj N) s := Adjunction.extEquiv.{wSY, wSX} adj e
  have hp := Functor.extPairing_eq_comp_counit.{wSY, wSX, wX}
    (P := L) (Q := JX) (K := L ⋙ JX) (τ := Iso.refl (L ⋙ JX))
    adj c e h
  simp only [Functor.extPairingCompAddEquiv_apply, Iso.refl_inv, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp] at hp
  have hc : c.comp (Ext.mk₀ (𝟙 ((L ⋙ JX).obj P))) (add_zero r) = c :=
    Ext.comp_mk₀_id.{wX} c
  rw [hc] at hp
  have hcomp : Ext.mapExactFunctor.{wSY, wX} (L ⋙ JX) a =
      Ext.mapExactFunctor.{wSX, wX} JX (Ext.mapExactFunctor.{wSY, wSX} L a) :=
    Ext.comp_mapExactFunctor.{wSY, wSX, wX} a L JX
  change Functor.extPairing.{wSX, wX} JX SX c e h =
    (c.comp (Ext.mapExactFunctor.{wSY, wX} (L ⋙ JX) a) h).comp
      (Ext.mk₀ (JX.map (adj.counit.app N))) (add_zero t) at hp
  rw [hcomp] at hp
  have hroot :
      (Functor.extPairing.{wSY, wY} JY SY (E P r c) (EY e) h).comp
        (Ext.mk₀ (JY.map ρ.inv)) (add_zero t) =
      Functor.extPairing.{wSY, wY} JY SY (E P r c) a h := by
    rw [hEY, Functor.extPairing_comp_mk₀.{wSY, wY},
      Ext.comp_assoc_of_third_deg_zero.{wY}, Ext.mk₀_comp_mk₀.{wY},
      ← JY.map_comp, Iso.hom_inv_id, JY.map_id, Ext.comp_mk₀_id.{wY}]
  rw [hT, hroot, ← hE c a h, AddEquiv.symm_apply_apply]
  exact hp.symm

end TransferPairing

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard moduleSheafExtZModModule

variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] (n : ℕ)
  [HasExt.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wY} (ModuleSheaf Y (ULift.{u + 1} (ZMod n)))]

local instance compatibilityDirectImage_preservesFiniteColimits :
    PreservesFiniteColimits (moduleDirectImage f (ULift.{u + 1} (ZMod n))) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

private theorem _compatibility_unit_comp
    {M N : ModuleSheaf Y (ULift.{u + 1} (ZMod n))} {r s t : ℕ}
    (c : Ext.{wX} (moduleUnit X (ULift.{u + 1} (ZMod n)))
      ((moduleDirectImage f (ULift.{u + 1} (ZMod n))).obj M) r)
    (e : Ext.{wY} M N s) (h : r + s = t) :
    moduleFiniteUnitExtAddEquiv f n N t
        (c.comp (e.mapExactFunctor (moduleDirectImage f (ULift.{u + 1} (ZMod n)))) h) =
      (moduleFiniteUnitExtAddEquiv f n M r c).comp e h := by
  let a := moduleInverseImageAdjunction f (ULift.{u + 1} (ZMod n))
  obtain ⟨c', rfl⟩ := a.extEquiv.surjective c
  rw [← a.extEquiv_naturality_right c' e h]
  change (Ext.mk₀ (moduleUnitInverseImageIso f n).inv).comp
      (a.extEquiv.symm (a.extEquiv (c'.comp e h))) (zero_add t) =
    ((Ext.mk₀ (moduleUnitInverseImageIso f n).inv).comp
      (a.extEquiv.symm (a.extEquiv c')) (zero_add r)).comp e h
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply,
    Ext.comp_assoc _ _ _ (zero_add r) h (by omega)]

section IndependentYonedaWorld

universe wS

variable [HasExt.{wS} (ModuleSheaf Y (ULift.{u + 1} (ZMod n)))]

/-- The original finite unit-Ext comparison preserves the Yoneda pairing
with an independent Ext world for the source class. -/
theorem moduleFiniteUnitExtAddEquiv_pairing
    {M N : ModuleSheaf Y (ULift.{u + 1} (ZMod n))} {r s t : ℕ}
    (c : Ext.{wX} (moduleUnit X (ULift.{u + 1} (ZMod n)))
      ((moduleDirectImage f (ULift.{u + 1} (ZMod n))).obj M) r)
    (e : Ext.{wS} M N s) (h : r + s = t) :
    moduleFiniteUnitExtAddEquiv.{u, wX, wY} f n N t
        (c.comp (Ext.mapExactFunctor.{wS, wX} (moduleDirectImage f (ULift.{u + 1} (ZMod n))) e) h) =
      (moduleFiniteUnitExtAddEquiv.{u, wX, wY} f n M r c).comp
        (Ext.mapExactFunctor.{wS, wY} (𝟭 (ModuleSheaf Y (ULift.{u + 1} (ZMod n)))) e) h := by
  let Λ := ULift.{u + 1} (ZMod n)
  let eY : Ext.{wY} M N s := Ext.mapExactFunctor.{wS, wY} (𝟭 (ModuleSheaf Y Λ)) e
  have he : Ext.mapExactFunctor.{wS, wX} (moduleDirectImage f Λ) e =
      Ext.mapExactFunctor.{wY, wX} (moduleDirectImage f Λ) eY :=
    Ext.comp_mapExactFunctor.{wS, wY, wX} e (𝟭 (ModuleSheaf Y Λ)) (moduleDirectImage f Λ)
  rw [he]
  exact _compatibility_unit_comp.{u, wX, wY} f n c
    (Ext.mapExactFunctor.{wS, wY} (𝟭 (ModuleSheaf Y Λ)) e) h

end IndependentYonedaWorld

section FiniteEtale

variable [Etale f] (d : ℕ) (hd : ∀ x : X, f.finrank x = d)

private theorem _compatibility_post_identity
    (P : ModuleSheaf Y (ULift.{u + 1} (ZMod n))) (q : ℕ)
    (c : Ext.{wX} (moduleUnit X (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek (𝟙 X) (ULift.{u + 1} (ZMod n))).obj
        ((moduleLowerShriek f (ULift.{u + 1} (ZMod n))).obj P)) q) :
    (moduleFiniteLowerShriekCompactExtAddEquiv f n d hd P q c).comp
        (Ext.mk₀ ((moduleLowerShriekIdIso (ULift.{u + 1} (ZMod n)) Y).hom.app P))
        (add_zero q) =
      moduleFiniteUnitExtAddEquiv f n P q
        ((c.comp (Ext.mk₀
            ((moduleLowerShriekIdIso (ULift.{u + 1} (ZMod n)) X).hom.app
              ((moduleLowerShriek f (ULift.{u + 1} (ZMod n))).obj P))) (add_zero q)).comp
          (Ext.mk₀ ((moduleFiniteEtaleLowerShriekDirectImageIso f n d hd).hom.app P))
          (add_zero q)) := by
  change ((moduleFiniteUnitExtAddEquiv f n P q
      ((c.comp (Ext.mk₀
          ((moduleLowerShriekIdIso (ULift.{u + 1} (ZMod n)) X).hom.app
            ((moduleLowerShriek f (ULift.{u + 1} (ZMod n))).obj P))) (add_zero q)).comp
        (Ext.mk₀ ((moduleFiniteEtaleLowerShriekDirectImageIso f n d hd).hom.app P))
        (add_zero q))).comp
      (Ext.mk₀ ((moduleLowerShriekIdIso (ULift.{u + 1} (ZMod n)) Y).inv.app P))
      (add_zero q)).comp
        (Ext.mk₀ ((moduleLowerShriekIdIso (ULift.{u + 1} (ZMod n)) Y).hom.app P))
        (add_zero q) = _
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Iso.inv_hom_id_app]
  simp only [Functor.id_obj, Ext.comp_mk₀_id]

section IndependentPairingWorlds

universe wSX wSY

variable [HasExt.{wSX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wSY} (ModuleSheaf Y (ULift.{u + 1} (ZMod n)))]

private theorem moduleFiniteLowerShriekCompactExtAddEquiv_pairing
    {P Q : ModuleSheaf Y (ULift.{u + 1} (ZMod n))} {r s t : ℕ}
    (c : Ext.{wX} (moduleUnit X (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek (𝟙 X) (ULift.{u + 1} (ZMod n))).obj
        ((moduleLowerShriek f (ULift.{u + 1} (ZMod n))).obj P)) r)
    (x : Ext.{wSY} P Q s) (h : r + s = t) :
    moduleFiniteLowerShriekCompactExtAddEquiv.{u, wX, wY} f n d hd Q t
        (moduleLowerShriekPairing.{wSX, wX, u} (𝟙 X) (ULift.{u + 1} (ZMod n)) c
          (Ext.mapExactFunctor.{wSY, wSX}
            (moduleLowerShriek f (ULift.{u + 1} (ZMod n))) x) h) =
      moduleLowerShriekPairing.{wSY, wY, u} (𝟙 Y) (ULift.{u + 1} (ZMod n))
        (moduleFiniteLowerShriekCompactExtAddEquiv.{u, wX, wY} f n d hd P r c) x h := by
  let Λ := ULift.{u + 1} (ZMod n)
  let JX := moduleLowerShriek (𝟙 X) Λ
  let JY := moduleLowerShriek (𝟙 Y) Λ
  let L := moduleLowerShriek f Λ
  let D := moduleDirectImage f Λ
  let iX := moduleLowerShriekIdIso Λ X
  let iY := moduleLowerShriekIdIso Λ Y
  let κ := moduleFiniteEtaleLowerShriekDirectImageIso f n d hd
  let c₀ := (c.comp (Ext.mk₀ (iX.hom.app (L.obj P))) (add_zero r)).comp
    (Ext.mk₀ (κ.hom.app P)) (add_zero r)
  let xX : Ext.{wSX} (L.obj P) (L.obj Q) s := Ext.mapExactFunctor.{wSY, wSX} L x
  let σ : L ⋙ JX ⟶ D := Functor.whiskerLeft L iX.hom ≫
    (Functor.rightUnitor L).hom ≫ κ.hom
  have hs : (c.comp (Ext.mk₀ (σ.app P)) (add_zero r)).comp
      (Ext.mapExactFunctor.{wSY, wX} D x) h =
    (c.comp (Ext.mapExactFunctor.{wSY, wX} (L ⋙ JX) x) h).comp
      (Ext.mk₀ (σ.app Q)) (add_zero t) :=
    Functor.extPairing_natTrans.{wSY, wX} σ c x h
  have hcomp :
      Ext.mapExactFunctor.{wSY, wX} (L ⋙ JX) x =
        Ext.mapExactFunctor.{wSX, wX} JX xX :=
    Ext.comp_mapExactFunctor.{wSY, wSX, wX} x L JX
  dsimp only [σ, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, Category.id_comp] at hs
  change (c.comp (Ext.mk₀ (iX.hom.app (L.obj P) ≫ κ.hom.app P)) (add_zero r)).comp
      (Ext.mapExactFunctor.{wSY, wX} D x) h =
    (c.comp (Ext.mapExactFunctor.{wSY, wX} (L ⋙ JX) x) h).comp
      (Ext.mk₀ (iX.hom.app (L.obj Q) ≫ κ.hom.app Q)) (add_zero t) at hs
  rw [hcomp] at hs
  have hsource :
      ((moduleLowerShriekPairing.{wSX, wX, u} (𝟙 X) Λ c xX h).comp
        (Ext.mk₀ (iX.hom.app (L.obj Q))) (add_zero t)).comp
          (Ext.mk₀ (κ.hom.app Q)) (add_zero t) =
      c₀.comp (Ext.mapExactFunctor.{wSY, wX} D x) h := by
    simpa only [moduleLowerShriekPairing, Functor.extPairing, c₀,
      Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀] using hs.symm
  have hy : ((moduleFiniteLowerShriekCompactExtAddEquiv.{u, wX, wY}
      f n d hd P r c).comp (Ext.mk₀ (iY.hom.app P)) (add_zero r)).comp
      (Ext.mapExactFunctor.{wSY, wY} (𝟭 (ModuleSheaf Y Λ)) x) h =
    (moduleLowerShriekPairing.{wSY, wY, u} (𝟙 Y) Λ
      (moduleFiniteLowerShriekCompactExtAddEquiv.{u, wX, wY} f n d hd P r c) x h).comp
      (Ext.mk₀ (iY.hom.app Q)) (add_zero t) :=
    Functor.extPairing_natTrans.{wSY, wY} iY.hom
      (moduleFiniteLowerShriekCompactExtAddEquiv.{u, wX, wY} f n d hd P r c) x h
  rw [_compatibility_post_identity.{u, wX, wY}] at hy
  apply (((extFunctorObj.{wY} (moduleUnit Y Λ) t).mapIso
    (iY.app Q)).addCommGroupIsoToAddEquiv).injective
  change (moduleFiniteLowerShriekCompactExtAddEquiv.{u, wX, wY} f n d hd Q t
      (moduleLowerShriekPairing.{wSX, wX, u} (𝟙 X) Λ c xX h)).comp
      (Ext.mk₀ (iY.hom.app Q)) (add_zero t) =
    (moduleLowerShriekPairing.{wSY, wY, u} (𝟙 Y) Λ
      (moduleFiniteLowerShriekCompactExtAddEquiv.{u, wX, wY} f n d hd P r c) x h).comp
      (Ext.mk₀ (iY.hom.app Q)) (add_zero t)
  rw [_compatibility_post_identity.{u, wX, wY}, hsource, ← hy]
  exact moduleFiniteUnitExtAddEquiv_pairing.{u, wX, wY, wSY} f n c₀ x h

end IndependentPairingWorlds

private theorem _compatibility_rootsTrace_apply
    (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    (b : Ext.{wY} (moduleUnit Y (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek (𝟙 Y) (ULift.{u + 1} (ZMod n))).obj
        (moduleRootsOfUnity Y n)) 2) :
    moduleFiniteLowerShriekRootsTraceMap.{u, wX, wY} f n d hd hn hinv b =
      ((moduleFiniteLowerShriekCompactExtAddEquiv.{u, wX, wY} f n d hd
          ((moduleInverseImage f (ULift.{u + 1} (ZMod n))).obj
            (moduleRootsOfUnity X n)) 2).symm
        (b.comp (Ext.mk₀ ((moduleLowerShriek (𝟙 Y) (ULift.{u + 1} (ZMod n))).map
          (moduleRootsOfUnityInverseImageIso f n hn hinv).inv)) (add_zero 2))).comp
        (Ext.mk₀ ((moduleLowerShriek (𝟙 X) (ULift.{u + 1} (ZMod n))).map
          ((moduleLowerShriekAdjunction f (ULift.{u + 1} (ZMod n))).counit.app
            (moduleRootsOfUnity X n)))) (add_zero 2) := rfl

section IndependentTracePairingWorlds

universe wSX wSY

variable [HasExt.{wSX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wSY} (ModuleSheaf Y (ULift.{u + 1} (ZMod n)))]

private theorem moduleFiniteLowerShriekRootsTraceMap_pairing
    (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    (P : ModuleSheaf Y (ULift.{u + 1} (ZMod n))) {r s : ℕ} (h : r + s = 2)
    (c : Ext.{wX} (moduleUnit X (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek (𝟙 X) (ULift.{u + 1} (ZMod n))).obj
        ((moduleLowerShriek f (ULift.{u + 1} (ZMod n))).obj P)) r)
    (e : Ext.{wSX} ((moduleLowerShriek f (ULift.{u + 1} (ZMod n))).obj P)
      (moduleRootsOfUnity X n) s) :
    moduleFiniteLowerShriekRootsTraceMap.{u, wX, wY} f n d hd hn hinv
        (moduleLowerShriekPairing.{wSY, wY, u} (𝟙 Y) (ULift.{u + 1} (ZMod n))
          (moduleFiniteLowerShriekCompactExtAddEquiv.{u, wX, wY} f n d hd P r c)
          (moduleFiniteLowerShriekRootsExtAddEquiv.{u, wSX, wSY} f n hn hinv P s e) h) =
      moduleLowerShriekPairing.{wSX, wX, u} (𝟙 X) (ULift.{u + 1} (ZMod n)) c e h := by
  exact _compatibility_transfer_pairing
    (moduleLowerShriek f (ULift.{u + 1} (ZMod n)))
    (moduleInverseImage f (ULift.{u + 1} (ZMod n)))
    (moduleLowerShriek (𝟙 X) (ULift.{u + 1} (ZMod n)))
    (moduleLowerShriek (𝟙 Y) (ULift.{u + 1} (ZMod n)))
    (moduleLowerShriekAdjunction f (ULift.{u + 1} (ZMod n)))
    (moduleUnit X (ULift.{u + 1} (ZMod n)))
    (moduleUnit Y (ULift.{u + 1} (ZMod n)))
    (moduleFiniteLowerShriekCompactExtAddEquiv.{u, wX, wY} f n d hd)
    (fun c x h => moduleFiniteLowerShriekCompactExtAddEquiv_pairing.{u, wX, wY, wSX, wSY}
      f n d hd c x h)
    (moduleRootsOfUnity X n) (moduleRootsOfUnity Y n)
    (moduleRootsOfUnityInverseImageIso f n hn hinv) h
    (moduleFiniteLowerShriekRootsExtAddEquiv.{u, wSX, wSY} f n hn hinv P s)
    (moduleFiniteLowerShriekRootsExtAddEquiv_apply.{u, wSX, wSY} f n hn hinv P s)
    (moduleFiniteLowerShriekRootsTraceMap.{u, wX, wY} f n d hd hn hinv)
    (_compatibility_rootsTrace_apply.{u, wX, wY} f n d hd hn hinv) c e

end IndependentTracePairingWorlds

end FiniteEtale

section ProperFiniteTrace

universe wAX wAY

open Scheme.OverField GroupCohomology.Kummer.CoefficientBaseChange

variable {k : Type u} [Field k] [IsAlgClosed k]
  (C D : FScheme k) (hC : Curve.Properties C) (hD : Curve.Properties D)
  (p : D ⟶ C) [IsFinite p.left] [IsDominant p.left] [Etale p.left]
  (n d : ℕ) (hd : ∀ x : C.left, p.left.finrank x = d)
  (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(C.left, ⊤)))
  [HasExt.{wX} (ModuleSheaf C.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wY} (ModuleSheaf D.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wAX} (AbelianSheaf.{u, u + 1} C.left)]
  [HasExt.{wAY} (AbelianSheaf.{u, u + 1} D.left)]

section PairingAllDegrees

universe wSX wSY

variable [HasExt.{wSX} (ModuleSheaf C.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wSY} (ModuleSheaf D.left (ULift.{u + 1} (ZMod n)))]

/-- The whole original pairing square in every pair of complementary degrees
uses the agreed literal finite transports and independent Ext worlds. -/
theorem moduleTracePairingLinearMap_finiteLowerShriek
    (P : ModuleSheaf D.left (ULift.{u + 1} (ZMod n)))
    (r s : ℕ) (h : r + s = 2)
    (c : Ext.{wX} (moduleUnit C.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek (𝟙 C.left) (ULift.{u + 1} (ZMod n))).obj
        ((moduleLowerShriek p.left (ULift.{u + 1} (ZMod n))).obj P)) r)
    (e : Ext.{wSX} ((moduleLowerShriek p.left (ULift.{u + 1} (ZMod n))).obj P)
      (moduleRootsOfUnity C.left n) s) :
    moduleTracePairingLinearMap.{u, wSX, wX, wAX} C hC ∅ Set.finite_empty (by simp)
        (𝟙 C.left) (by simp) n hn hunit hinv
        ((moduleLowerShriek p.left (ULift.{u + 1} (ZMod n))).obj P) r s h c e =
      moduleTracePairingLinearMap.{u, wSY, wY, wAY} D hD ∅ Set.finite_empty (by simp)
        (𝟙 D.left) (by simp) n hn hunit (levelInvertible p.left n hinv) P r s h
        (moduleFiniteLowerShriekCompactExtAddEquiv.{u, wX, wY} p.left n d hd P r c)
        (moduleFiniteLowerShriekRootsExtAddEquiv.{u, wSX, wSY} p.left n hn hinv P s e) := by
  rw [moduleTracePairingLinearMap_apply_apply, moduleTracePairingLinearMap_apply_apply,
    ← moduleFiniteLowerShriekRootsTraceMap_pairing.{u, wX, wY, wSX, wSY}
      p.left n d hd hn hinv P h c e]
  exact DFunLike.congr_fun
    (moduleCompactSupportTrace_finiteLowerShriekRootsTrace.{u, wX, wY, wAX, wAY}
      C D hC hD p n d hd hn hunit hinv)
    (moduleLowerShriekPairing.{wSY, wY, u} (𝟙 D.left) (ULift.{u + 1} (ZMod n))
      (moduleFiniteLowerShriekCompactExtAddEquiv.{u, wX, wY} p.left n d hd P r c)
      (moduleFiniteLowerShriekRootsExtAddEquiv.{u, wSX, wSY} p.left n hn hinv P s e) h)

end PairingAllDegrees

end ProperFiniteTrace

end AlgebraicGeometry.Scheme.EtaleCohomology
