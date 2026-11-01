/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.FinitePushforward
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Finite.ModuleComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Finite.ModuleTraceNormalization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.LowerShriekExt
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleComparisons
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleIdentityCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.Comparisons
public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.FinitePushforward
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootsOfUnityInverseImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.TracePairing
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.TracePullback

/-!
# Original finite-etale transports for the normalized pairing

The compact transport uses the original identity lower-shriek isomorphisms,
the same proved finite lower-shriek comparison, and the existing unit-Ext
comparison. The source transport is the original lower-shriek Ext adjunction
followed by the original roots comparison. All Ext worlds remain independent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u wX wY

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard moduleSheafExtZModModule

section IdentityUnderlying

variable {C : Type*} [Category C] {L R : C ⥤ C}

private theorem identity_left_norm_of_conjugate
    (a : L ⊣ R) (e : L ≅ 𝟭 C) (r : R ≅ 𝟭 C)
    (h : conjugateEquiv Adjunction.id a e.hom = r.inv) (M : C) :
    a.homEquiv M M (e.hom.app M) ≫ r.hom.app M = 𝟙 M := by
  have hu := unit_conjugateEquiv Adjunction.id a e.hom M
  rw [h] at hu
  change 𝟙 M ≫ r.inv.app M = a.homEquiv M M (e.hom.app M) at hu
  rw [Category.id_comp] at hu
  rw [← hu, r.inv_hom_id_app]
  dsimp only [Functor.id_obj]

variable {D : Type*} [Category D] {L' R' : D ⥤ D} (U : C ⥤ D)

private theorem underlying_identity_of_norms
    (a : L ⊣ R) (b : L' ⊣ R')
    (e : L ⋙ U ≅ U ⋙ L') (r : R ⋙ U ≅ U ⋙ R')
    (hmate : (mateEquiv a b (TwoSquare.mk _ _ _ _ e.inv)).natTrans = r.hom)
    (l : L ≅ 𝟭 C) (l' : L' ≅ 𝟭 D)
    (i : R ≅ 𝟭 C) (i' : R' ≅ 𝟭 D) (M : C)
    (ha : a.homEquiv M M (l.hom.app M) ≫ i.hom.app M = 𝟙 M)
    (hb : b.homEquiv (U.obj M) (U.obj M) (l'.hom.app (U.obj M)) ≫
      i'.hom.app (U.obj M) = 𝟙 (U.obj M))
    (hr : U.map (i.inv.app M) ≫ r.hom.app M = i'.inv.app (U.obj M)) :
    U.map (l.hom.app M) = e.hom.app M ≫ l'.hom.app (U.obj M) := by
  have ha' : a.homEquiv M M (l.hom.app M) = i.inv.app M := by
    apply (cancel_mono (i.hom.app M)).mp
    rw [ha, i.inv_hom_id_app]
    dsimp only [Functor.id_obj]
  have hb' : b.homEquiv (U.obj M) (U.obj M) (l'.hom.app (U.obj M)) =
      i'.inv.app (U.obj M) := by
    apply (cancel_mono (i'.hom.app (U.obj M))).mp
    rw [hb, i'.inv_hom_id_app]
    dsimp only [Functor.id_obj]
  have h := underlying_homEquiv_of_mate a b (TwoSquare.mk _ _ _ _ e.inv)
    r.hom hmate M M (l.hom.app M)
  rw [ha', hr] at h
  have he : e.inv.app M ≫ U.map (l.hom.app M) = l'.hom.app (U.obj M) := by
    apply (b.homEquiv _ _).injective
    exact h.symm.trans hb'.symm
  apply (cancel_epi (e.inv.app M)).mp
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using he

end IdentityUnderlying

section IdentityExchange

variable {C : Type*} [Category C] {L I : C ⥤ C}

private theorem identity_unit_of_norm
    (a : L ⊣ I) (l : L ≅ 𝟭 C) (i : I ≅ 𝟭 C) (M : C)
    (h : a.homEquiv M M (l.hom.app M) ≫ i.hom.app M = 𝟙 M) :
    i.inv.app M ≫ I.map (l.inv.app M) = a.unit.app M := by
  apply (cancel_mono (I.map (l.hom.app M) ≫ i.hom.app M)).mp
  simp only [Category.assoc, ← I.map_comp_assoc, Iso.inv_hom_id_app,
    Functor.id_obj, CategoryTheory.Functor.map_id, Category.id_comp]
  simpa only [Adjunction.homEquiv_unit, Category.assoc] using h.symm

variable {D : Type*} [Category D] {L' I' : D ⥤ D}

private theorem identity_exchange_of_norms
    (a : L ⊣ I) (a' : L' ⊣ I') (F : D ⥤ C)
    (l : L ≅ 𝟭 C) (l' : L' ≅ 𝟭 D)
    (i : I ≅ 𝟭 C) (i' : I' ≅ 𝟭 D)
    (β : F ⋙ I ⟶ I' ⋙ F) [IsIso β]
    (γ : F ⋙ L ⟶ L' ⋙ F) (M : D)
    (hl : a.homEquiv (F.obj M) (F.obj M) (l.hom.app (F.obj M)) ≫
      i.hom.app (F.obj M) = 𝟙 (F.obj M))
    (hl' : a'.homEquiv M M (l'.hom.app M) ≫ i'.hom.app M = 𝟙 M)
    (hβ : β.app M ≫ F.map (i'.hom.app M) = i.hom.app (F.obj M))
    (hγ : a.homEquiv _ _ (γ.app M) ≫ β.app (L'.obj M) = F.map (a'.unit.app M)) :
    γ.app M = l.hom.app (F.obj M) ≫ F.map (l'.inv.app M) := by
  dsimp only [Functor.id_obj, Functor.comp_obj] at hl hl' hγ
  have hlh : a.homEquiv (F.obj M) (F.obj M) (l.hom.app (F.obj M)) =
      i.inv.app (F.obj M) := by
    apply (cancel_mono (i.hom.app (F.obj M))).mp
    rw [hl, Iso.inv_hom_id_app]
    dsimp only [Functor.id_obj]
  have hb : i.inv.app (F.obj M) ≫ β.app M = F.map (i'.inv.app M) := by
    apply (cancel_mono (F.map (i'.hom.app M))).mp
    simp only [Category.assoc, hβ, Iso.inv_hom_id_app, ← F.map_comp,
      Functor.id_obj, CategoryTheory.Functor.map_id]
  have hn := β.naturality (l'.inv.app M)
  dsimp only [Functor.comp_map, Functor.id_obj, Functor.comp_obj] at hn
  have hu := identity_unit_of_norm a' l' i' M hl'
  apply (a.homEquiv _ _).injective
  apply (cancel_mono (β.app (L'.obj M))).mp
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [hγ, Adjunction.homEquiv_naturality_right, hlh]
  simp only [Category.assoc]
  rw [hn, ← Category.assoc, hb, ← F.map_comp, hu]

end IdentityExchange

section NativeIdentity

variable (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u})

private theorem moduleInverseImageIdIso_hom_underlying
    (M : ModuleSheaf X Λ) :
    (SheafOfModules.toSheaf (constantRing X Λ)).map
        ((moduleInverseImageIdIso Λ X).hom.app M) =
      (moduleInverseImageUnderlyingIso Λ (𝟙 X)).hom.app M ≫
        (inverseImageId X).hom.app
          ((SheafOfModules.toSheaf (constantRing X Λ)).obj M) := by
  let U : ModuleSheaf X Λ ⥤ AbelianSheaf.{u, u + 1} X :=
    SheafOfModules.toSheaf (constantRing X Λ)
  have ha := identity_left_norm_of_conjugate
    (moduleInverseImageAdjunction (𝟙 X) Λ) (moduleInverseImageIdIso Λ X)
    (moduleDirectImageIdIso Λ X) (conjugateEquiv_moduleInverseImageIdIso_hom Λ X) M
  have hb := identity_left_norm_of_conjugate
    (inverseImageAdjunction (𝟙 X)) (inverseImageId X)
    (directImageIdIso X) (conjugateEquiv_inverseImageId_hom X) (U.obj M)
  have hr : U.map ((moduleDirectImageIdIso Λ X).inv.app M) ≫
        (moduleDirectImageUnderlyingIso (𝟙 X) Λ).hom.app M =
      (directImageIdIso X).inv.app (U.obj M) := by
    change U.map ((moduleDirectImageIdIso Λ X).inv.app M) ≫
      𝟙 ((directImage (𝟙 X)).obj (U.obj M)) = _
    erw [Category.comp_id]
    exact moduleDirectImageIdIso_inv_underlying Λ X M
  exact underlying_identity_of_norms U
    (moduleInverseImageAdjunction (𝟙 X) Λ) (inverseImageAdjunction (𝟙 X))
    (moduleInverseImageUnderlyingIso Λ (𝟙 X)) (moduleDirectImageUnderlyingIso (𝟙 X) Λ)
    (mate_moduleInverseImageUnderlyingIso_inv (Λ := Λ) (f := 𝟙 X))
    (moduleInverseImageIdIso Λ X) (inverseImageId X)
    (moduleDirectImageIdIso Λ X) (directImageIdIso X) M ha hb hr

private theorem moduleLowerShriekIdIso_hom_underlying
    (M : ModuleSheaf X Λ) :
    (SheafOfModules.toSheaf (constantRing X Λ)).map
        ((moduleLowerShriekIdIso Λ X).hom.app M) =
      (moduleLowerShriekUnderlyingIso (𝟙 X) Λ).hom.app M ≫
        (etaleLowerShriekIdIso X).hom.app
          ((SheafOfModules.toSheaf (constantRing X Λ)).obj M) := by
  let U : ModuleSheaf X Λ ⥤ AbelianSheaf.{u, u + 1} X :=
    SheafOfModules.toSheaf (constantRing X Λ)
  have ha := moduleLowerShriekIdIso_homEquiv Λ X M
  have hb := etaleLowerShriekIdIso_homEquiv X (U.obj M)
  have hp := moduleInverseImageIdIso_hom_underlying Λ X M
  have hr : U.map ((moduleInverseImageIdIso Λ X).inv.app M) ≫
        (moduleInverseImageUnderlyingIso Λ (𝟙 X)).hom.app M =
      (inverseImageId X).inv.app (U.obj M) := by
    apply (cancel_mono ((inverseImageId X).hom.app (U.obj M))).mp
    rw [Category.assoc, ← hp, ← U.map_comp, Iso.inv_hom_id_app,
      U.map_id, Iso.inv_hom_id_app]
    dsimp only [Functor.id_obj]
  exact underlying_identity_of_norms U
    (moduleLowerShriekAdjunction (𝟙 X) Λ) (etaleLowerShriekAdjunction (𝟙 X))
    (moduleLowerShriekUnderlyingIso (𝟙 X) Λ) (moduleInverseImageUnderlyingIso Λ (𝟙 X))
    (mate_moduleLowerShriekUnderlyingIso_inv (𝟙 X) Λ)
    (moduleLowerShriekIdIso Λ X) (etaleLowerShriekIdIso X)
    (moduleInverseImageIdIso Λ X) (inverseImageId X) M ha hb hr

end NativeIdentity

section NativeIdentityExchange

variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]
  (h : IsPullback (𝟙 Y) f f (𝟙 X))

private theorem finiteLowerShriekDirectImageMap_identity
    (F : AbelianSheaf.{u, u + 1} Y) :
    (finiteLowerShriekDirectImageMap f f (𝟙 X) (𝟙 Y) h).app F =
      (etaleLowerShriekIdIso X).hom.app ((directImage f).obj F) ≫
        (directImage f).map ((etaleLowerShriekIdIso Y).inv.app F) := by
  let β := baseChangeMap f f (𝟙 X) (𝟙 Y) h.w.symm
  let : IsIso β := Finite.finiteBaseChange_isIso f f (𝟙 X) (𝟙 Y) h
  have hu := NatTrans.congr_app (finiteLowerShriekDirectImageMap_unit f f (𝟙 X) (𝟙 Y) h) F
  simp only [NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Category.id_comp] at hu
  have hr := finiteOpenRestrictionIso_inv_baseChange_app f f (𝟙 X) (𝟙 Y) h F
  have hg := (congrArg (fun a => a ≫ β.app ((etaleLowerShriek (𝟙 Y)).obj F)) hu).trans hr
  exact identity_exchange_of_norms
    (etaleLowerShriekAdjunction (𝟙 X)) (etaleLowerShriekAdjunction (𝟙 Y))
    (directImage f) (etaleLowerShriekIdIso X) (etaleLowerShriekIdIso Y)
    (inverseImageId X) (inverseImageId Y) β
    (finiteLowerShriekDirectImageMap f f (𝟙 X) (𝟙 Y) h) F
    (etaleLowerShriekIdIso_homEquiv X ((directImage f).obj F))
    (etaleLowerShriekIdIso_homEquiv Y F)
    (baseChangeMap_id f h.w.symm F) hg

end NativeIdentityExchange

section IdentityCompactCohomology

universe vX vY

variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]
  (h : IsPullback (𝟙 Y) f f (𝟙 X))
  [HasExt.{vX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{vY} (AbelianSheaf.{u, u + 1} Y)]

private theorem finiteDirectImageAddEquiv_identity_normalization
    (F : AbelianSheaf.{u, u + 1} Y) (q : ℕ)
    (c : CompactSupport.H (𝟙 X) ((directImage f).obj F) q) :
    Sheaf.H.map ((etaleLowerShriekIdIso Y).hom.app F) q
        (CompactSupport.finiteDirectImageAddEquiv f f (𝟙 X) (𝟙 Y) h F q c) =
      Finite.finiteCohomologyDirectImageAddEquiv f F q
        (Sheaf.H.map ((etaleLowerShriekIdIso X).hom.app ((directImage f).obj F)) q c) := by
  rw [CompactSupport.finiteDirectImageAddEquiv_apply]
  have hn := Finite.finiteCohomologyDirectImageAddEquiv_naturality f
    ((etaleLowerShriekIdIso Y).hom.app F) q
    (Sheaf.H.map ((finiteLowerShriekDirectImageMap f f (𝟙 X) (𝟙 Y) h).app F) q c)
  rw [← hn, ← Sheaf.H.map_comp_apply, finiteLowerShriekDirectImageMap_identity f h F]
  simp only [Category.assoc, ← (directImage f).map_comp, Iso.inv_hom_id_app,
    Functor.id_obj, CategoryTheory.Functor.map_id, Category.comp_id]

end IdentityCompactCohomology

section TwoAdjunctionYoneda

universe wC wD

variable {C : Type*} [Category C] [Abelian C] [HasExt.{wC} C]
  {D : Type*} [Category D] [Abelian D] [HasExt.{wD} D]
  (I : C ⥤ D) [I.Additive] [PreservesFiniteLimits I] [PreservesFiniteColimits I]
  (F : D ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The two original adjunction formulas and Yoneda composition give the
complete pairing identity without an additional Frobenius equation. -/
private theorem twoAdjunctionYoneda
    (a : I ⊣ F) (b : F ⊣ I) {U N : C} {P : D} {r s t : ℕ}
    (e : Ext.{wC} U (F.obj P) r) (x : Ext.{wC} (F.obj P) N s) (h : r + s = t) :
    e.comp x h =
      (a.extEquiv ((a.extEquiv.symm e).comp (b.extEquiv x) h)).comp
        (Ext.mk₀ (b.counit.app N)) (add_zero t) := by
  obtain ⟨e', rfl⟩ := a.extEquiv.surjective e
  obtain ⟨x', rfl⟩ := b.extEquiv.symm.surjective x
  simp only [AddEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]
  rw [Adjunction.extEquiv_symm_apply, ← Ext.comp_assoc_of_third_deg_zero,
    ← a.extEquiv_naturality_right]

end TwoAdjunctionYoneda

section ModuleIdentityCohomology

universe wM wA

variable (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u})
  [HasExt.{wM} (ModuleSheaf X Λ)] [HasExt.{wA} (AbelianSheaf.{u, u + 1} X)]

private theorem moduleLowerShriekCohomologyAddEquiv_identity
    (M : ModuleSheaf X Λ) (q : ℕ)
    (c : Ext.{wM} (moduleUnit X Λ) ((moduleLowerShriek (𝟙 X) Λ).obj M) q) :
    Sheaf.H.map ((etaleLowerShriekIdIso X).hom.app
        ((SheafOfModules.toSheaf (constantRing X Λ)).obj M)) q
        (moduleLowerShriekCohomologyAddEquiv (𝟙 X) Λ M q c) =
      etaleModuleExtCohomologyAddEquivLargeScalars X (constantRing X Λ) M q
        (c.comp (Ext.mk₀ ((moduleLowerShriekIdIso Λ X).hom.app M)) (add_zero q)) := by
  have h := moduleLowerShriekIdIso_hom_underlying Λ X M
  rw [moduleLowerShriekCohomologyAddEquiv_apply, ← Sheaf.H.map_comp_apply, ← h,
    moduleUnitExtAddEquiv_naturality]

end ModuleIdentityCohomology

section OriginalAdjointCoefficient

variable {C : Type*} [Category C] {D : Type*} [Category D]
  {L F : C ⥤ D} {R : D ⥤ C}

private theorem original_morphism_eq_comparison_counit
    (a : L ⊣ R) (e : L ≅ F) {P : C} {N : D} (x : L.obj P ⟶ N) :
    e.hom.app P ≫ F.map (a.homEquiv P N x) ≫
        (a.ofNatIsoLeft e).counit.app N = x := by
  have hn := e.hom.naturality (a.homEquiv P N x)
  have hx := (a.homEquiv P N).symm_apply_apply x
  change L.map (a.homEquiv P N x) ≫ a.counit.app N = x at hx
  change e.hom.app P ≫ F.map (a.homEquiv P N x) ≫ e.inv.app (R.obj N) ≫
    a.counit.app N = x
  rw [← reassoc_of% hn, Iso.hom_inv_id_app_assoc]
  exact hx

private theorem original_counit_eq_comparison_counit
    (a : L ⊣ R) (e : L ≅ F) (N : D) :
    e.hom.app (R.obj N) ≫ (a.ofNatIsoLeft e).counit.app N = a.counit.app N := by
  change e.hom.app (R.obj N) ≫ e.inv.app (R.obj N) ≫ a.counit.app N = _
  rw [Iso.hom_inv_id_app_assoc]

end OriginalAdjointCoefficient

variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] (n : ℕ)
  [HasExt.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wY} (ModuleSheaf Y (ULift.{u + 1} (ZMod n)))]

local instance finitePairingDirectImage_preservesFiniteColimits :
    PreservesFiniteColimits (moduleDirectImage f (ULift.{u + 1} (ZMod n))) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

private theorem moduleFiniteUnitExtAddEquiv_comp
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

section FiniteLowerShriek

variable [Etale f]

omit [IsFinite f] in
/-- The source-Ext comparison is EXACTLY the original lower-shriek adjunction
followed by the original roots inverse-image isomorphism. -/
def moduleFiniteLowerShriekRootsExtAddEquiv
    (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    (P : ModuleSheaf Y (ULift.{u + 1} (ZMod n))) (s : ℕ) :
    Ext.{wX} ((moduleLowerShriek f (ULift.{u + 1} (ZMod n))).obj P)
        (moduleRootsOfUnity X n) s ≃+
      Ext.{wY} P (moduleRootsOfUnity Y n) s :=
  (moduleLowerShriekExtEquiv f (ULift.{u + 1} (ZMod n)) P
      (moduleRootsOfUnity X n) s).trans
    (((extFunctorObj P s).mapIso
      (moduleRootsOfUnityInverseImageIso f n hn hinv)).addCommGroupIsoToAddEquiv)

omit [IsFinite f] in
/-- The whole forward source map retains the original Ext adjunction and
original roots coefficient morphism, with no trace or cohomology premise. -/
theorem moduleFiniteLowerShriekRootsExtAddEquiv_apply
    (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    (P : ModuleSheaf Y (ULift.{u + 1} (ZMod n))) (s : ℕ)
    (e : Ext.{wX} ((moduleLowerShriek f (ULift.{u + 1} (ZMod n))).obj P)
      (moduleRootsOfUnity X n) s) :
    moduleFiniteLowerShriekRootsExtAddEquiv f n hn hinv P s e =
      (moduleLowerShriekExtEquiv f (ULift.{u + 1} (ZMod n)) P
          (moduleRootsOfUnity X n) s e).comp
        (Ext.mk₀ (moduleRootsOfUnityInverseImageIso f n hn hinv).hom) (add_zero s) := rfl

omit [IsFinite f] in
/-- Degree zero is the exact original adjunction transpose followed by roots transport. -/
theorem moduleFiniteLowerShriekRootsExtAddEquiv_mk₀
    (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    (P : ModuleSheaf Y (ULift.{u + 1} (ZMod n)))
    (a : (moduleLowerShriek f (ULift.{u + 1} (ZMod n))).obj P ⟶ moduleRootsOfUnity X n) :
    moduleFiniteLowerShriekRootsExtAddEquiv f n hn hinv P 0 (Ext.mk₀ a) =
      Ext.mk₀ ((moduleLowerShriekAdjunction f (ULift.{u + 1} (ZMod n))).homEquiv _ _ a ≫
        (moduleRootsOfUnityInverseImageIso f n hn hinv).hom) := by
  rw [moduleFiniteLowerShriekRootsExtAddEquiv_apply, moduleLowerShriekExtEquiv_mk₀,
    Ext.mk₀_comp_mk₀]

variable (d : ℕ) (hd : ∀ x : X, f.finrank x = d)

omit [HasExt.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wY} (ModuleSheaf Y (ULift.{u + 1} (ZMod n)))] in
private theorem moduleFiniteLowerShriek_counit_roots_underlying :
    (SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).map
        ((moduleLowerShriekAdjunction f (ULift.{u + 1} (ZMod n))).counit.app
          (moduleRootsOfUnity X n)) ≫ (moduleRootsOfUnityUnderlyingIso X n).hom =
      ((SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).map
          ((moduleFiniteEtaleLowerShriekDirectImageIso f n d hd).hom.app
            ((moduleInverseImage f (ULift.{u + 1} (ZMod n))).obj
              (moduleRootsOfUnity X n))) ≫
        (moduleDirectImageUnderlyingIso f (ULift.{u + 1} (ZMod n))).hom.app
          ((moduleInverseImage f (ULift.{u + 1} (ZMod n))).obj
            (moduleRootsOfUnity X n))) ≫
      (directImage f).map
        ((moduleInverseImageUnderlyingIso (ULift.{u + 1} (ZMod n)) f).hom.app
            (moduleRootsOfUnity X n) ≫
          (inverseImage f).map (moduleRootsOfUnityUnderlyingIso X n).hom) ≫
      (finiteEtaleSheafTrace (Scheme.FiniteEtale.mk f) d hd).app
        (GroupCohomology.Kummer.Coefficients.mu X n) := by
  let Λ := ULift.{u + 1} (ZMod n)
  let U : ModuleSheaf X Λ ⥤ AbelianSheaf.{u, u + 1} X :=
    SheafOfModules.toSheaf (constantRing X Λ)
  have hk := original_counit_eq_comparison_counit
    (moduleLowerShriekAdjunction f Λ) (moduleFiniteEtaleLowerShriekDirectImageIso f n d hd)
    (moduleRootsOfUnity X n)
  have hc := moduleFiniteEtaleDirectImageAdjunction_counit_underlying f n d hd
    (moduleRootsOfUnity X n)
  change U.map (((moduleLowerShriekAdjunction f Λ).ofNatIsoLeft
      (moduleFiniteEtaleLowerShriekDirectImageIso f n d hd)).counit.app
      (moduleRootsOfUnity X n)) = _ at hc
  have ht := (finiteEtaleSheafTrace (Scheme.FiniteEtale.mk f) d hd).naturality
    (moduleRootsOfUnityUnderlyingIso X n).hom
  dsimp only [Functor.comp_map, Functor.id_map] at ht
  rw [← hk, U.map_comp, hc]
  simp only [Category.assoc]
  rw [← ht, (directImage f).map_comp]
  simp only [Category.assoc]
  rfl

/-- Compact degree-q transport in the proper identity-open case uses the
original two identity comparisons, the SAME finite f!→f* comparison, and the
existing finite unit-Ext comparison. The Ext worlds remain independent. -/
def moduleFiniteLowerShriekCompactExtAddEquiv
    (P : ModuleSheaf Y (ULift.{u + 1} (ZMod n))) (q : ℕ) :
    Ext.{wX} (moduleUnit X (ULift.{u + 1} (ZMod n)))
        ((moduleLowerShriek (𝟙 X) (ULift.{u + 1} (ZMod n))).obj
          ((moduleLowerShriek f (ULift.{u + 1} (ZMod n))).obj P)) q ≃+
      Ext.{wY} (moduleUnit Y (ULift.{u + 1} (ZMod n)))
        ((moduleLowerShriek (𝟙 Y) (ULift.{u + 1} (ZMod n))).obj P) q :=
  (((extFunctorObj (moduleUnit X (ULift.{u + 1} (ZMod n))) q).mapIso
      ((moduleLowerShriekIdIso (ULift.{u + 1} (ZMod n)) X).app
        ((moduleLowerShriek f (ULift.{u + 1} (ZMod n))).obj P))).addCommGroupIsoToAddEquiv).trans
    ((((extFunctorObj (moduleUnit X (ULift.{u + 1} (ZMod n))) q).mapIso
        ((moduleFiniteEtaleLowerShriekDirectImageIso f n d hd).app
          P)).addCommGroupIsoToAddEquiv).trans
      ((moduleFiniteUnitExtAddEquiv f n P q).trans
        (((extFunctorObj (moduleUnit Y (ULift.{u + 1} (ZMod n))) q).mapIso
          ((moduleLowerShriekIdIso (ULift.{u + 1} (ZMod n)) Y).symm.app
            P)).addCommGroupIsoToAddEquiv)))

private theorem moduleFiniteLowerShriekCompactExtAddEquiv_post_identity
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

private theorem moduleFiniteLowerShriekCompactExtAddEquiv_naturality
    {P Q : ModuleSheaf Y (ULift.{u + 1} (ZMod n))} (a : P ⟶ Q) (q : ℕ)
    (c : Ext.{wX} (moduleUnit X (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek (𝟙 X) (ULift.{u + 1} (ZMod n))).obj
        ((moduleLowerShriek f (ULift.{u + 1} (ZMod n))).obj P)) q) :
    moduleFiniteLowerShriekCompactExtAddEquiv f n d hd Q q
        (c.comp (Ext.mk₀ ((moduleLowerShriek (𝟙 X) (ULift.{u + 1} (ZMod n))).map
          ((moduleLowerShriek f (ULift.{u + 1} (ZMod n))).map a))) (add_zero q)) =
      (moduleFiniteLowerShriekCompactExtAddEquiv f n d hd P q c).comp
        (Ext.mk₀ ((moduleLowerShriek (𝟙 Y) (ULift.{u + 1} (ZMod n))).map a)) (add_zero q) := by
  let Λ := ULift.{u + 1} (ZMod n)
  let JX := moduleLowerShriek (𝟙 X) Λ
  let JY := moduleLowerShriek (𝟙 Y) Λ
  let L := moduleLowerShriek f Λ
  let D := moduleDirectImage f Λ
  let iX := moduleLowerShriekIdIso Λ X
  let iY := moduleLowerShriekIdIso Λ Y
  let κ := moduleFiniteEtaleLowerShriekDirectImageIso f n d hd
  have hx := iX.hom.naturality (L.map a)
  have hy := iY.hom.naturality a
  have hk := κ.hom.naturality a
  dsimp only [Functor.comp_map, Functor.id_map] at hx hy hk
  have hs :
      ((c.comp (Ext.mk₀ (JX.map (L.map a))) (add_zero q)).comp
        (Ext.mk₀ (iX.hom.app (L.obj Q))) (add_zero q)).comp
          (Ext.mk₀ (κ.hom.app Q)) (add_zero q) =
      ((c.comp (Ext.mk₀ (iX.hom.app (L.obj P))) (add_zero q)).comp
        (Ext.mk₀ (κ.hom.app P)) (add_zero q)).comp
          (Ext.mk₀ (D.map a)) (add_zero q) := by
    simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
    rw [hx, Category.assoc, hk]
    simp only [Category.assoc]
    rfl
  have hr :
      ((moduleFiniteLowerShriekCompactExtAddEquiv f n d hd P q c).comp
        (Ext.mk₀ (JY.map a)) (add_zero q)).comp
          (Ext.mk₀ (iY.hom.app Q)) (add_zero q) =
      (moduleFiniteUnitExtAddEquiv f n P q
        ((c.comp (Ext.mk₀ (iX.hom.app (L.obj P))) (add_zero q)).comp
          (Ext.mk₀ (κ.hom.app P)) (add_zero q))).comp (Ext.mk₀ a) (add_zero q) := by
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, hy,
      ← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero,
      moduleFiniteLowerShriekCompactExtAddEquiv_post_identity]
  apply (((extFunctorObj (moduleUnit Y Λ) q).mapIso
    (iY.app Q)).addCommGroupIsoToAddEquiv).injective
  change (moduleFiniteLowerShriekCompactExtAddEquiv f n d hd Q q
      (c.comp (Ext.mk₀ (JX.map (L.map a))) (add_zero q))).comp
        (Ext.mk₀ (iY.hom.app Q)) (add_zero q) =
    ((moduleFiniteLowerShriekCompactExtAddEquiv f n d hd P q c).comp
      (Ext.mk₀ (JY.map a)) (add_zero q)).comp
        (Ext.mk₀ (iY.hom.app Q)) (add_zero q)
  rw [moduleFiniteLowerShriekCompactExtAddEquiv_post_identity, hr, hs]
  exact DFunLike.congr_fun (moduleFiniteUnitExtAddEquiv_naturality f n a q)
    ((c.comp (Ext.mk₀ (iX.hom.app (L.obj P))) (add_zero q)).comp
      (Ext.mk₀ (κ.hom.app P)) (add_zero q))

/-- The actual compact roots transfer uses the inverse of the original finite
cohomology comparison, roots transport and original lower-shriek counit. -/
def moduleFiniteLowerShriekRootsTraceMap
    (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) :
    Ext.{wY} (moduleUnit Y (ULift.{u + 1} (ZMod n)))
        ((moduleLowerShriek (𝟙 Y) (ULift.{u + 1} (ZMod n))).obj
          (moduleRootsOfUnity Y n)) 2 →+
      Ext.{wX} (moduleUnit X (ULift.{u + 1} (ZMod n)))
        ((moduleLowerShriek (𝟙 X) (ULift.{u + 1} (ZMod n))).obj
          (moduleRootsOfUnity X n)) 2 :=
  ((Ext.mk₀ ((moduleLowerShriek (𝟙 X) (ULift.{u + 1} (ZMod n))).map
      ((moduleLowerShriekAdjunction f (ULift.{u + 1} (ZMod n))).counit.app
        (moduleRootsOfUnity X n)))).postcomp
      (moduleUnit X (ULift.{u + 1} (ZMod n))) (add_zero 2)).comp
    ((moduleFiniteLowerShriekCompactExtAddEquiv f n d hd
      ((moduleInverseImage f (ULift.{u + 1} (ZMod n))).obj
        (moduleRootsOfUnity X n)) 2).symm.toAddMonoidHom.comp
      ((Ext.mk₀ ((moduleLowerShriek (𝟙 Y) (ULift.{u + 1} (ZMod n))).map
        (moduleRootsOfUnityInverseImageIso f n hn hinv).inv)).postcomp
          (moduleUnit Y (ULift.{u + 1} (ZMod n))) (add_zero 2)))

section PairingZero

universe wSX wSY

variable [HasExt.{wSX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wSY} (ModuleSheaf Y (ULift.{u + 1} (ZMod n)))]

private theorem moduleFiniteLowerShriekRootsTraceMap_pairing_zero
    (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    (P : ModuleSheaf Y (ULift.{u + 1} (ZMod n)))
    (c : Ext.{wX} (moduleUnit X (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek (𝟙 X) (ULift.{u + 1} (ZMod n))).obj
        ((moduleLowerShriek f (ULift.{u + 1} (ZMod n))).obj P)) 2)
    (e : Ext.{wSX} ((moduleLowerShriek f (ULift.{u + 1} (ZMod n))).obj P)
      (moduleRootsOfUnity X n) 0) :
    moduleFiniteLowerShriekRootsTraceMap.{u, wX, wY} f n d hd hn hinv
        (moduleLowerShriekPairing.{wSY, wY, u} (𝟙 Y) (ULift.{u + 1} (ZMod n))
          (moduleFiniteLowerShriekCompactExtAddEquiv.{u, wX, wY} f n d hd P 2 c)
          (moduleFiniteLowerShriekRootsExtAddEquiv.{u, wSX, wSY} f n hn hinv P 0 e) (add_zero 2)) =
      moduleLowerShriekPairing.{wSX, wX, u} (𝟙 X) (ULift.{u + 1} (ZMod n)) c e (add_zero 2) := by
  let Λ := ULift.{u + 1} (ZMod n)
  let JX := moduleLowerShriek (𝟙 X) Λ
  let JY := moduleLowerShriek (𝟙 Y) Λ
  let L := moduleLowerShriek f Λ
  let Q := (moduleInverseImage f Λ).obj (moduleRootsOfUnity X n)
  let ι := moduleRootsOfUnityInverseImageIso f n hn hinv
  obtain ⟨x, rfl⟩ := (Ext.mk₀_bijective (L.obj P) (moduleRootsOfUnity X n)).surjective e
  let b := (moduleLowerShriekAdjunction f Λ).homEquiv P (moduleRootsOfUnity X n) x
  have hx := ((moduleLowerShriekAdjunction f Λ).homEquiv P
    (moduleRootsOfUnity X n)).symm_apply_apply x
  change L.map b ≫ (moduleLowerShriekAdjunction f Λ).counit.app
    (moduleRootsOfUnity X n) = x at hx
  rw [moduleFiniteLowerShriekRootsExtAddEquiv_mk₀]
  change moduleFiniteLowerShriekRootsTraceMap.{u, wX, wY} f n d hd hn hinv
      (moduleLowerShriekPairing.{wSY, wY, u} (𝟙 Y) Λ
        (moduleFiniteLowerShriekCompactExtAddEquiv.{u, wX, wY} f n d hd P 2 c)
        (Ext.mk₀ (b ≫ ι.hom)) (add_zero 2)) =
    moduleLowerShriekPairing.{wSX, wX, u} (𝟙 X) Λ c (Ext.mk₀ x) (add_zero 2)
  simp only [moduleLowerShriekPairing, Functor.extPairing_mk₀_right]
  change ((moduleFiniteLowerShriekCompactExtAddEquiv.{u, wX, wY} f n d hd Q 2).symm
      (((moduleFiniteLowerShriekCompactExtAddEquiv.{u, wX, wY} f n d hd P 2 c).comp
        (Ext.mk₀ (JY.map (b ≫ ι.hom))) (add_zero 2)).comp
          (Ext.mk₀ (JY.map ι.inv)) (add_zero 2))).comp
      (Ext.mk₀ (JX.map ((moduleLowerShriekAdjunction f Λ).counit.app
        (moduleRootsOfUnity X n)))) (add_zero 2) =
    c.comp (Ext.mk₀ (JX.map x)) (add_zero 2)
  have hb :
      ((moduleFiniteLowerShriekCompactExtAddEquiv.{u, wX, wY} f n d hd P 2 c).comp
        (Ext.mk₀ (JY.map (b ≫ ι.hom))) (add_zero 2)).comp
          (Ext.mk₀ (JY.map ι.inv)) (add_zero 2) =
      (moduleFiniteLowerShriekCompactExtAddEquiv.{u, wX, wY} f n d hd P 2 c).comp
        (Ext.mk₀ (JY.map b)) (add_zero 2) := by
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, ← JY.map_comp,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hb, ← moduleFiniteLowerShriekCompactExtAddEquiv_naturality.{u, wX, wY} f n d hd b 2 c,
    AddEquiv.symm_apply_apply, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀, ← JX.map_comp, hx]

end PairingZero

section CompactExtCohomology

universe wAX wAY

variable [HasExt.{wAX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{wAY} (AbelianSheaf.{u, u + 1} Y)]

private theorem moduleFiniteLowerShriekCompactExtAddEquiv_cohomology
    (h : IsPullback (𝟙 Y) f f (𝟙 X))
    (P : ModuleSheaf Y (ULift.{u + 1} (ZMod n))) (q : ℕ)
    (c : Ext.{wX} (moduleUnit X (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek (𝟙 X) (ULift.{u + 1} (ZMod n))).obj
        ((moduleLowerShriek f (ULift.{u + 1} (ZMod n))).obj P)) q) :
    moduleLowerShriekCohomologyAddEquiv (𝟙 Y) (ULift.{u + 1} (ZMod n)) P q
        (moduleFiniteLowerShriekCompactExtAddEquiv f n d hd P q c) =
      CompactSupport.finiteDirectImageAddEquiv f f (𝟙 X) (𝟙 Y) h
        ((SheafOfModules.toSheaf (constantRing Y (ULift.{u + 1} (ZMod n)))).obj P) q
        (CompactSupport.H.map (𝟙 X)
          ((SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).map
              ((moduleFiniteEtaleLowerShriekDirectImageIso f n d hd).hom.app P) ≫
            (moduleDirectImageUnderlyingIso f (ULift.{u + 1} (ZMod n))).hom.app P) q
          (moduleLowerShriekCohomologyAddEquiv (𝟙 X) (ULift.{u + 1} (ZMod n))
            ((moduleLowerShriek f (ULift.{u + 1} (ZMod n))).obj P) q c)) := by
  let Λ := ULift.{u + 1} (ZMod n)
  let U : ModuleSheaf X Λ ⥤ AbelianSheaf.{u, u + 1} X :=
    SheafOfModules.toSheaf (constantRing X Λ)
  let V : ModuleSheaf Y Λ ⥤ AbelianSheaf.{u, u + 1} Y :=
    SheafOfModules.toSheaf (constantRing Y Λ)
  let A := (moduleLowerShriek f Λ).obj P
  let c₀ := c.comp (Ext.mk₀ ((moduleLowerShriekIdIso Λ X).hom.app A)) (add_zero q)
  let c₁ := c₀.comp
    (Ext.mk₀ ((moduleFiniteEtaleLowerShriekDirectImageIso f n d hd).hom.app P)) (add_zero q)
  let v := U.map ((moduleFiniteEtaleLowerShriekDirectImageIso f n d hd).hom.app P) ≫
    (moduleDirectImageUnderlyingIso f Λ).hom.app P
  have hx := moduleLowerShriekCohomologyAddEquiv_identity Λ X A q c
  have hy := moduleLowerShriekCohomologyAddEquiv_identity Λ Y P q
    (moduleFiniteLowerShriekCompactExtAddEquiv f n d hd P q c)
  have hp := moduleFiniteLowerShriekCompactExtAddEquiv_post_identity f n d hd P q c
  have hf := DFunLike.congr_fun
    (moduleFiniteUnitExtCohomology_square f n P q) c₁
  change etaleModuleExtCohomologyAddEquivLargeScalars Y (constantRing Y Λ) P q
      (moduleFiniteUnitExtAddEquiv f n P q c₁) =
    Finite.finiteCohomologyDirectImageAddEquiv f (V.obj P) q
      (Sheaf.H.map ((moduleDirectImageUnderlyingIso f Λ).hom.app P) q
        (etaleModuleExtCohomologyAddEquivLargeScalars X (constantRing X Λ)
          ((moduleDirectImage f Λ).obj P) q c₁)) at hf
  have hnat := (etaleLowerShriekIdIso X).hom.naturality v
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj] at hnat
  apply ((Sheaf.functorH Y.smallEtaleTopology q).mapIso
    ((etaleLowerShriekIdIso Y).app (V.obj P))).addCommGroupIsoToAddEquiv.injective
  change Sheaf.H.map ((etaleLowerShriekIdIso Y).hom.app (V.obj P)) q
      (moduleLowerShriekCohomologyAddEquiv (𝟙 Y) Λ P q
        (moduleFiniteLowerShriekCompactExtAddEquiv f n d hd P q c)) =
    Sheaf.H.map ((etaleLowerShriekIdIso Y).hom.app (V.obj P)) q
      (CompactSupport.finiteDirectImageAddEquiv f f (𝟙 X) (𝟙 Y) h (V.obj P) q
        (CompactSupport.H.map (𝟙 X) v q
          (moduleLowerShriekCohomologyAddEquiv (𝟙 X) Λ A q c)))
  rw [hy, hp, hf, finiteDirectImageAddEquiv_identity_normalization f h]
  rw [CompactSupport.H.map_apply, ← Sheaf.H.map_comp_apply]
  erw [hnat]
  rw [Sheaf.H.map_comp_apply, hx]
  change Finite.finiteCohomologyDirectImageAddEquiv f (V.obj P) q
      (Sheaf.H.map ((moduleDirectImageUnderlyingIso f Λ).hom.app P) q
        (etaleModuleExtCohomologyAddEquivLargeScalars X (constantRing X Λ)
          ((moduleDirectImage f Λ).obj P) q c₁)) =
    Finite.finiteCohomologyDirectImageAddEquiv f (V.obj P) q
      (Sheaf.H.map v q
        (etaleModuleExtCohomologyAddEquivLargeScalars X (constantRing X Λ) A q c₀))
  rw [Sheaf.H.map_comp_apply, ← moduleUnitExtAddEquiv_naturality]

private theorem moduleFiniteLowerShriekRootsTraceMap_cohomology
    (h : IsPullback (𝟙 Y) f f (𝟙 X))
    (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    (b : Ext.{wY} (moduleUnit Y (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek (𝟙 Y) (ULift.{u + 1} (ZMod n))).obj
        (moduleRootsOfUnity Y n)) 2) :
    CompactSupport.H.map (𝟙 X) (moduleRootsOfUnityUnderlyingIso X n).hom 2
        (moduleLowerShriekCohomologyAddEquiv (𝟙 X) (ULift.{u + 1} (ZMod n))
          (moduleRootsOfUnity X n) 2
          (moduleFiniteLowerShriekRootsTraceMap f n d hd hn hinv b)) =
      CompactSupport.finiteRootsTraceMap f f (𝟙 X) (𝟙 Y) h d hd n hn hinv 2
        (CompactSupport.H.map (𝟙 Y) (moduleRootsOfUnityUnderlyingIso Y n).hom 2
          (moduleLowerShriekCohomologyAddEquiv (𝟙 Y) (ULift.{u + 1} (ZMod n))
            (moduleRootsOfUnity Y n) 2 b)) := by
  let Λ := ULift.{u + 1} (ZMod n)
  let U : ModuleSheaf X Λ ⥤ AbelianSheaf.{u, u + 1} X :=
    SheafOfModules.toSheaf (constantRing X Λ)
  let V : ModuleSheaf Y Λ ⥤ AbelianSheaf.{u, u + 1} Y :=
    SheafOfModules.toSheaf (constantRing Y Λ)
  let Q := (moduleInverseImage f Λ).obj (moduleRootsOfUnity X n)
  let e := moduleRootsOfUnityInverseImageIso f n hn hinv
  let b₀ := b.comp (Ext.mk₀ ((moduleLowerShriek (𝟙 Y) Λ).map e.inv)) (add_zero 2)
  let c := (moduleFiniteLowerShriekCompactExtAddEquiv f n d hd Q 2).symm b₀
  let a := (moduleInverseImageUnderlyingIso Λ f).hom.app (moduleRootsOfUnity X n) ≫
    (inverseImage f).map (moduleRootsOfUnityUnderlyingIso X n).hom
  let v := U.map ((moduleFiniteEtaleLowerShriekDirectImageIso f n d hd).hom.app Q) ≫
    (moduleDirectImageUnderlyingIso f Λ).hom.app Q
  let cA := moduleLowerShriekCohomologyAddEquiv (𝟙 X) Λ
    ((moduleLowerShriek f Λ).obj Q) 2 c
  let bA := moduleLowerShriekCohomologyAddEquiv (𝟙 Y) Λ (moduleRootsOfUnity Y n) 2 b
  have he := moduleFiniteLowerShriekCompactExtAddEquiv_cohomology f n d hd h Q 2 c
  change moduleLowerShriekCohomologyAddEquiv (𝟙 Y) Λ Q 2
      ((moduleFiniteLowerShriekCompactExtAddEquiv f n d hd Q 2)
        ((moduleFiniteLowerShriekCompactExtAddEquiv f n d hd Q 2).symm b₀)) =
    CompactSupport.finiteDirectImageAddEquiv f f (𝟙 X) (𝟙 Y) h (V.obj Q) 2
      (CompactSupport.H.map (𝟙 X) v 2 cA) at he
  rw [AddEquiv.apply_symm_apply] at he
  have hb : moduleLowerShriekCohomologyAddEquiv (𝟙 Y) Λ Q 2 b₀ =
      CompactSupport.H.map (𝟙 Y) (V.map e.inv) 2 bA :=
    moduleLowerShriekCohomologyAddEquiv_naturality (𝟙 Y) Λ e.inv 2 b
  have hr : V.map e.inv ≫ a = (moduleRootsOfUnityUnderlyingIso Y n).hom ≫
      (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso f n hn hinv).inv := by
    have h := moduleRootsOfUnityInverseImageIso_underlying f n hn hinv
    apply (cancel_mono
      (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso f n hn hinv).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have h' : V.map e.hom ≫ (moduleRootsOfUnityUnderlyingIso Y n).hom =
        a ≫ (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso f n hn hinv).hom := by
      simpa only [a, Category.assoc] using h
    rw [← h', ← V.map_comp_assoc, Iso.inv_hom_id, V.map_id, Category.id_comp]
  have hcoho :
      CompactSupport.H.map (𝟙 X) ((directImage f).map a) 2
          (CompactSupport.H.map (𝟙 X) v 2 cA) =
        (CompactSupport.finiteDirectImageAddEquiv f f (𝟙 X) (𝟙 Y) h
          ((inverseImage f).obj (GroupCohomology.Kummer.Coefficients.mu X n)) 2).symm
            (CompactSupport.H.map (𝟙 Y)
              (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso f n hn hinv).inv 2
              (CompactSupport.H.map (𝟙 Y) (moduleRootsOfUnityUnderlyingIso Y n).hom 2 bA)) := by
    apply (CompactSupport.finiteDirectImageAddEquiv f f (𝟙 X) (𝟙 Y) h
      ((inverseImage f).obj (GroupCohomology.Kummer.Coefficients.mu X n)) 2).injective
    rw [AddEquiv.apply_symm_apply]
    have hn := DFunLike.congr_fun
      (CompactSupport.finiteDirectImageAddEquiv_naturality f f (𝟙 X) (𝟙 Y) h a 2)
      (CompactSupport.H.map (𝟙 X) v 2 cA)
    change CompactSupport.finiteDirectImageAddEquiv f f (𝟙 X) (𝟙 Y) h
        ((inverseImage f).obj (GroupCohomology.Kummer.Coefficients.mu X n)) 2
        (CompactSupport.H.map (𝟙 X) ((directImage f).map a) 2
          (CompactSupport.H.map (𝟙 X) v 2 cA)) =
      CompactSupport.H.map (𝟙 Y) a 2
        (CompactSupport.finiteDirectImageAddEquiv f f (𝟙 X) (𝟙 Y) h (V.obj Q) 2
          (CompactSupport.H.map (𝟙 X) v 2 cA)) at hn
    rw [hn, ← he, hb, ← CompactSupport.H.map_comp_apply, hr,
      CompactSupport.H.map_comp_apply]
  change CompactSupport.H.map (𝟙 X) (moduleRootsOfUnityUnderlyingIso X n).hom 2
      (moduleLowerShriekCohomologyAddEquiv (𝟙 X) Λ (moduleRootsOfUnity X n) 2
        (c.comp (Ext.mk₀ ((moduleLowerShriek (𝟙 X) Λ).map
          ((moduleLowerShriekAdjunction f Λ).counit.app (moduleRootsOfUnity X n))))
          (add_zero 2))) = _
  rw [moduleLowerShriekCohomologyAddEquiv_naturality]
  change CompactSupport.H.map (𝟙 X) (moduleRootsOfUnityUnderlyingIso X n).hom 2
      (CompactSupport.H.map (𝟙 X)
        (U.map ((moduleLowerShriekAdjunction f Λ).counit.app (moduleRootsOfUnity X n))) 2 cA) = _
  rw [← CompactSupport.H.map_comp_apply,
    moduleFiniteLowerShriek_counit_roots_underlying f n d hd,
    CompactSupport.H.map_comp_apply, CompactSupport.H.map_comp_apply, hcoho]
  rfl

end CompactExtCohomology

end FiniteLowerShriek

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

/-- The whole original module transfer preserves normalized proper trace.
The identity-open square and its empty complements are canonical; no matching
completion-degree or coprimality assumption is added. -/
theorem moduleCompactSupportTrace_finiteLowerShriekRootsTrace :
    (moduleCompactSupportTraceAddEquiv C hC ∅ Set.finite_empty (by simp)
        (𝟙 C.left) (by simp) n hn hunit hinv).toAddMonoidHom.comp
      (moduleFiniteLowerShriekRootsTraceMap p.left n d hd hn hinv) =
    (moduleCompactSupportTraceAddEquiv D hD ∅ Set.finite_empty (by simp)
      (𝟙 D.left) (by simp) n hn hunit (levelInvertible p.left n hinv)).toAddMonoidHom := by
  let : Nonempty C.left := Curve.curveProperties_nonempty hC
  let : Nonempty D.left := Curve.curveProperties_nonempty hD
  let h := IsPullback.id_horiz p.left
  apply AddMonoidHom.ext
  intro b
  change moduleCompactSupportTraceAddEquiv C hC ∅ Set.finite_empty (by simp)
      (𝟙 C.left) (by simp) n hn hunit hinv
      (moduleFiniteLowerShriekRootsTraceMap p.left n d hd hn hinv b) =
    moduleCompactSupportTraceAddEquiv D hD ∅ Set.finite_empty (by simp)
      (𝟙 D.left) (by simp) n hn hunit (levelInvertible p.left n hinv) b
  rw [moduleCompactSupportTraceAddEquiv_apply, moduleCompactSupportTraceAddEquiv_apply,
    moduleFiniteLowerShriekRootsTraceMap_cohomology p.left n d hd h hn hinv]
  exact DFunLike.congr_fun
    (Curves.compactSupportTraceAddEquiv_finiteRootsTrace hC hD p
      ∅ Set.finite_empty (by simp) ∅ Set.finite_empty (by simp)
      (𝟙 C.left) (by simp) (𝟙 D.left) (by simp) p.left h d hd n hn hunit hinv)
    (CompactSupport.H.map (𝟙 D.left) (moduleRootsOfUnityUnderlyingIso D.left n).hom 2
      (moduleLowerShriekCohomologyAddEquiv (𝟙 D.left) (ULift.{u + 1} (ZMod n))
        (moduleRootsOfUnity D.left n) 2 b))

section PairingZero

universe wSX wSY

variable [HasExt.{wSX} (ModuleSheaf C.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wSY} (ModuleSheaf D.left (ULift.{u + 1} (ZMod n)))]

/-- The whole original pairing square in compact degree two and source degree
zero uses the agreed literal finite transports and independent Ext worlds. -/
theorem moduleTracePairingLinearMap_finiteLowerShriek_two_zero
    (P : ModuleSheaf D.left (ULift.{u + 1} (ZMod n)))
    (c : Ext.{wX} (moduleUnit C.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek (𝟙 C.left) (ULift.{u + 1} (ZMod n))).obj
        ((moduleLowerShriek p.left (ULift.{u + 1} (ZMod n))).obj P)) 2)
    (e : Ext.{wSX} ((moduleLowerShriek p.left (ULift.{u + 1} (ZMod n))).obj P)
      (moduleRootsOfUnity C.left n) 0) :
    moduleTracePairingLinearMap.{u, wSX, wX, wAX} C hC ∅ Set.finite_empty (by simp)
        (𝟙 C.left) (by simp) n hn hunit hinv
        ((moduleLowerShriek p.left (ULift.{u + 1} (ZMod n))).obj P) 2 0 (add_zero 2) c e =
      moduleTracePairingLinearMap.{u, wSY, wY, wAY} D hD ∅ Set.finite_empty (by simp)
        (𝟙 D.left) (by simp) n hn hunit (levelInvertible p.left n hinv) P 2 0 (add_zero 2)
        (moduleFiniteLowerShriekCompactExtAddEquiv.{u, wX, wY} p.left n d hd P 2 c)
        (moduleFiniteLowerShriekRootsExtAddEquiv.{u, wSX, wSY} p.left n hn hinv P 0 e) := by
  rw [moduleTracePairingLinearMap_apply_apply, moduleTracePairingLinearMap_apply_apply,
    ← moduleFiniteLowerShriekRootsTraceMap_pairing_zero.{u, wX, wY, wSX, wSY}
      p.left n d hd hn hinv P c e]
  exact DFunLike.congr_fun
    (moduleCompactSupportTrace_finiteLowerShriekRootsTrace.{u, wX, wY, wAX, wAY}
      C D hC hD p n d hd hn hunit hinv)
    (moduleLowerShriekPairing.{wSY, wY, u} (𝟙 D.left) (ULift.{u + 1} (ZMod n))
      (moduleFiniteLowerShriekCompactExtAddEquiv.{u, wX, wY} p.left n d hd P 2 c)
      (moduleFiniteLowerShriekRootsExtAddEquiv.{u, wSX, wSY} p.left n hn hinv P 0 e) (add_zero 2))

end PairingZero

end ProperFiniteTrace

end AlgebraicGeometry.Scheme.EtaleCohomology
