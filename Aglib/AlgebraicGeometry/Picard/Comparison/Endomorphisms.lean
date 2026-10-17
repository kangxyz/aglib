/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Linear
public import Aglib.AlgebraicGeometry.Modules.Invertible.Trivialization
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor

/-!
# Global scalars, pullback and endomorphisms of line bundles

For a scheme `X`, a global function `a ∈ Γ(X, ⊤)` acts on every module sheaf `M` by the
module-linear endomorphism `globalScalarEndomorphism X M a`. This file proves the three facts
about these scalars that the rigidification of the Picard functor uses (Kleiman, *The Picard
scheme*, arXiv:math/0504020v1, proofs of Lemmas 2.9 and 2.10, p. 19):

* pullback along `f : X ⟶ Y` carries multiplication by `a` to multiplication by
  `f.appTop a` (`pullback_map_globalScalarEndomorphism`), and pushforward carries
  multiplication by `f.appTop a` to multiplication by `a`
  (`pushforward_map_globalScalarEndomorphism`);
* every endomorphism of the structure module is multiplication by its value at `1`
  (`eq_unitMul_unitHomGlobalSectionsEquiv`), and on a module isomorphic to the structure
  module distinct global functions act differently (`globalScalarEndomorphism_injective_of_iso`);
* every endomorphism of a locally rank-one module sheaf is multiplication by a global
  function (`exists_eq_globalScalarEndomorphism_of_isLocallyRankOne`).

`globalScalarIso X M a` is the automorphism given by a global unit `a`. No hypothesis on the
schemes or morphisms is used. The declarations are general module-sheaf facts; their
natural owners are `Aglib.AlgebraicGeometry.Modules.Linear` (the scalar statements) and the
`Invertible` family (the line-bundle statement).
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X Y : Scheme.{u}}

/-- Composition of global scalar endomorphisms is multiplication of the scalars. -/
theorem globalScalarEndomorphism_mul (M : X.Modules) (a b : Γ(X, ⊤)) :
    globalScalarEndomorphism X M (a * b) =
      globalScalarEndomorphism X M a ≫ globalScalarEndomorphism X M b := by
  change (globalScalarCenter X (a * b)).app M = _
  rw [map_mul]
  exact CatCenter.mul_app _ _ _

@[simp]
theorem globalScalarEndomorphism_one (M : X.Modules) :
    globalScalarEndomorphism X M 1 = 𝟙 M := by
  change (globalScalarCenter X 1).app M = _
  rw [map_one]
  rfl

/-- Multiplication by a global unit, as an automorphism of a module sheaf. -/
@[simps]
def globalScalarIso (M : X.Modules) (a : (Γ(X, ⊤))ˣ) : M ≅ M where
  hom := globalScalarEndomorphism X M a
  inv := globalScalarEndomorphism X M ↑a⁻¹
  hom_inv_id := by rw [← globalScalarEndomorphism_mul, Units.mul_inv, globalScalarEndomorphism_one]
  inv_hom_id := by rw [← globalScalarEndomorphism_mul, Units.inv_mul, globalScalarEndomorphism_one]

/-- Global scalar endomorphisms are central: conjugation by an isomorphism preserves them. -/
theorem globalScalarEndomorphism_conj {M N : X.Modules} (e : M ≅ N) (a : Γ(X, ⊤)) :
    globalScalarEndomorphism X M a = e.hom ≫ globalScalarEndomorphism X N a ≫ e.inv := by
  have h : e.hom ≫ globalScalarEndomorphism X N a = globalScalarEndomorphism X M a ≫ e.hom :=
    (globalScalarCenter X a).naturality e.hom
  rw [reassoc_of% h, e.hom_inv_id, Category.comp_id]

variable (f : X ⟶ Y)

/-- Pushforward carries multiplication by `f.appTop a` to multiplication by `a`, because the
`Γ(Y, U)`-module structure of `f_* N` is restriction of scalars along `f.app U`. -/
theorem pushforward_map_globalScalarEndomorphism (N : X.Modules) (a : Γ(Y, ⊤)) :
    (pushforward f).map (globalScalarEndomorphism X N (f.appTop a)) =
      globalScalarEndomorphism Y ((pushforward f).obj N) a := by
  ext U x
  refine (globalScalarEndomorphism_app X N (f.appTop a) (f ⁻¹ᵁ U) x).trans ?_
  refine Eq.trans ?_ (globalScalarEndomorphism_app Y ((pushforward f).obj N) a U x).symm
  change _ = f.app U (Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a) •
    (show Γ(N, f ⁻¹ᵁ U) from x)
  congr 1
  have h := Scheme.Hom.naturality f (homOfLE (le_top : U ≤ ⊤)).op
  have h2 := congrArg (fun φ => φ.hom a) h
  simp only [CommRingCat.comp_apply] at h2
  rw [h2]
  rfl

/-- Pullback carries multiplication by `a` to multiplication by `f.appTop a`. The two maps
have the same adjoint transpose `M ⟶ f_* f^* M` by naturality of the adjunction unit and of
global scalars. -/
theorem pullback_map_globalScalarEndomorphism (M : Y.Modules) (a : Γ(Y, ⊤)) :
    (pullback f).map (globalScalarEndomorphism Y M a) =
      globalScalarEndomorphism X ((pullback f).obj M) (f.appTop a) := by
  apply ((pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    pushforward_map_globalScalarEndomorphism]
  have h1 := (pullbackPushforwardAdjunction f).unit.naturality (globalScalarEndomorphism Y M a)
  have h2 := (globalScalarCenter Y a).naturality ((pullbackPushforwardAdjunction f).unit.app M)
  simp only [Functor.id_map, Functor.comp_map] at h1 h2
  rw [← h1]
  exact h2.symm

-- `X.Modules` and `SheafOfModules X.ringCatSheaf` are the same category under different
-- instance paths; relaxing instance transparency lets the unit-module lemmas apply.
set_option backward.isDefEq.respectTransparency false in
/-- Evaluating multiplication by `a` on the structure module at `1` returns `a`. -/
theorem unitHomGlobalSectionsEquiv_unitMul (a : Γ(X, ⊤)) :
    unitHomGlobalSectionsEquiv X _ (unitMul X a) = a := by
  rw [unitHomGlobalSectionsEquiv_apply, unitMul_app]
  change 1 * (X.presheaf.map (𝟙 (op ⊤))).hom a = a
  rw [CategoryTheory.Functor.map_id, one_mul]
  rfl

-- `X.Modules` and `SheafOfModules X.ringCatSheaf` are the same category under different
-- instance paths; relaxing instance transparency lets the unit-module lemmas apply.
set_option backward.isDefEq.respectTransparency false in
/-- Every endomorphism of the structure module is multiplication by its value at `1`. -/
theorem eq_unitMul_unitHomGlobalSectionsEquiv
    (c : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ SheafOfModules.unit X.ringCatSheaf) :
    c = unitMul X (unitHomGlobalSectionsEquiv X _ c) := by
  apply (unitHomGlobalSectionsEquiv X _).injective
  rw [unitHomGlobalSectionsEquiv_unitMul]

/-- On a module sheaf isomorphic to the structure module, global functions act faithfully. -/
theorem globalScalarEndomorphism_injective_of_iso {M : X.Modules}
    (e : M ≅ SheafOfModules.unit X.ringCatSheaf) :
    Function.Injective (globalScalarEndomorphism X M) := by
  intro a b hab
  have h : globalScalarEndomorphism X (SheafOfModules.unit X.ringCatSheaf) a =
      globalScalarEndomorphism X (SheafOfModules.unit X.ringCatSheaf) b := by
    rw [globalScalarEndomorphism_conj e.symm a, globalScalarEndomorphism_conj e.symm b, hab]
  rw [globalScalarEndomorphism_unit, globalScalarEndomorphism_unit] at h
  rw [← unitHomGlobalSectionsEquiv_unitMul a, ← unitHomGlobalSectionsEquiv_unitMul b, h]

-- `X.Modules` and `SheafOfModules X.ringCatSheaf` are the same category under different
-- instance paths; relaxing instance transparency lets the unit-module lemmas apply.
set_option backward.isDefEq.respectTransparency false in
/-- Multiplication by the value at `1` of an endomorphism of the structure module is that
endomorphism. -/
theorem globalScalarEndomorphism_unitHomGlobalSectionsEquiv
    (c : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ SheafOfModules.unit X.ringCatSheaf) :
    globalScalarEndomorphism X _ (unitHomGlobalSectionsEquiv X _ c) = c := by
  rw [globalScalarEndomorphism_unit, ← eq_unitMul_unitHomGlobalSectionsEquiv]

-- `X.Modules` and `SheafOfModules X.ringCatSheaf` are the same category under different
-- instance paths; relaxing instance transparency lets the unit-module lemmas apply.
set_option backward.isDefEq.respectTransparency false in
/-- The global unit by which an automorphism of the structure module multiplies: its value
at `1`, with inverse the value of the inverse automorphism at `1`. -/
def unitIsoGlobalUnit
    (d : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ≅ SheafOfModules.unit X.ringCatSheaf) :
    (Γ(X, ⊤))ˣ where
  val := unitHomGlobalSectionsEquiv X _ d.hom
  inv := unitHomGlobalSectionsEquiv X _ d.inv
  val_inv := by
    apply globalScalarEndomorphism_injective_of_iso (Iso.refl _)
    rw [globalScalarEndomorphism_mul, globalScalarEndomorphism_unitHomGlobalSectionsEquiv,
      globalScalarEndomorphism_unitHomGlobalSectionsEquiv, d.hom_inv_id,
      globalScalarEndomorphism_one]
  inv_val := by
    apply globalScalarEndomorphism_injective_of_iso (Iso.refl _)
    rw [globalScalarEndomorphism_mul, globalScalarEndomorphism_unitHomGlobalSectionsEquiv,
      globalScalarEndomorphism_unitHomGlobalSectionsEquiv, d.inv_hom_id,
      globalScalarEndomorphism_one]

theorem unitIsoGlobalUnit_val
    (d : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ≅ SheafOfModules.unit X.ringCatSheaf) :
    (unitIsoGlobalUnit d : Γ(X, ⊤)) = unitHomGlobalSectionsEquiv X _ d.hom := rfl

/-- Multiplication by `unitIsoGlobalUnit d` on the structure module is `d`. -/
theorem globalScalarEndomorphism_unitIsoGlobalUnit
    (d : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ≅ SheafOfModules.unit X.ringCatSheaf) :
    globalScalarEndomorphism X _ (unitIsoGlobalUnit d) = d.hom :=
  globalScalarEndomorphism_unitHomGlobalSectionsEquiv d.hom

-- `X.Modules` and `SheafOfModules X.ringCatSheaf` are the same category under different
-- instance paths, and `X.sheaf` is a `TopCat.Sheaf`; relaxing instance transparency lets the
-- chart, gluing and separatedness lemmas apply.
set_option backward.isDefEq.respectTransparency false in
/-- **Endomorphisms of line bundles are global scalars.** Every endomorphism of a locally
rank-one module sheaf is multiplication by a global function. On a unit chart the
endomorphism is multiplication by the coordinate of the image of the chart generator; these
local functions agree on overlaps and glue in the structure sheaf. -/
theorem exists_eq_globalScalarEndomorphism_of_isLocallyRankOne {M : X.Modules}
    (hM : Invertible.IsLocallyRankOne X M) (φ : M ⟶ M) :
    ∃ r : Γ(X, ⊤), φ = globalScalarEndomorphism X M r := by
  rw [Invertible.isLocallyRankOne_iff_local_unit] at hM
  choose U hxU e using hM
  let c : ∀ x (V : X.Opens) (h : V ≤ U x), Γ(M, V) ≃ₗ[Γ(X, V)] Γ(X, V) := fun x V h =>
    Invertible.chartSectionEquiv X M (U x) (e x).some V h
  let g : ∀ x, Γ(M, U x) := fun x => Invertible.chartGenerator X M (U x) (e x).some
  let r : ∀ x, Γ(X, U x) := fun x => c x (U x) le_rfl (φ.app (U x) (g x))
  have hsymm : ∀ x (V : X.Opens) (h : V ≤ U x) (b : Γ(X, V)),
      (c x V h).symm b = b • (c x V h).symm 1 := by
    intro x V h b
    conv_lhs => rw [← mul_one b, ← smul_eq_mul, LinearEquiv.map_smul]
  have hloc : ∀ x (V : X.Opens) (h : V ≤ U x) (t : Γ(M, V)),
      φ.app V t = X.presheaf.map (homOfLE h).op (r x) • t := by
    intro x V h t
    have hg : M.presheaf.map (homOfLE h).op (g x) = (c x V h).symm 1 :=
      Invertible.chartGenerator_restrict X M (U x) (e x).some V h
    have ht : t = c x V h t • (c x V h).symm 1 := by
      rw [← hsymm, LinearEquiv.symm_apply_apply]
    have hφg : φ.app (U x) (g x) = r x • g x := by
      have h1 : φ.app (U x) (g x) = (c x (U x) le_rfl).symm (r x) :=
        ((c x (U x) le_rfl).symm_apply_apply _).symm
      rw [h1, hsymm]
      rfl
    have hnat : φ.app V (M.presheaf.map (homOfLE h).op (g x)) =
        M.presheaf.map (homOfLE h).op (φ.app (U x) (g x)) :=
      NatTrans.naturality_apply φ.mapPresheaf (homOfLE h).op (g x)
    conv_lhs => rw [ht, Hom.app_smul, ← hg, hnat, hφg, map_smul]
    conv_rhs => rw [ht]
    rw [smul_smul, smul_smul, mul_comm, hg]
  have hres : ∀ {V W Z : X.Opens} (h₁ : V ≤ W) (h₂ : W ≤ Z) (a : Γ(X, Z)),
      X.presheaf.map (homOfLE h₁).op (X.presheaf.map (homOfLE h₂).op a) =
        X.presheaf.map (homOfLE (h₁.trans h₂)).op a := by
    intro V W Z h₁ h₂ a
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 U r := by
    intro x y
    let V := U x ⊓ U y
    have h1 := hloc x V inf_le_left ((c x V inf_le_left).symm 1)
    have h2 := hloc y V inf_le_right ((c x V inf_le_left).symm 1)
    have h3 := congrArg (c x V inf_le_left) (h1.symm.trans h2)
    rw [LinearEquiv.map_smul, LinearEquiv.map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul,
      smul_eq_mul, mul_one, mul_one] at h3
    exact h3
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' U ⊤ (fun x => homOfLE le_top)
    (fun y _ => Opens.mem_iSup.mpr ⟨y, hxU y⟩) r hcompat
  let s' : Γ(X, ⊤) := s
  have hs' : ∀ x, X.presheaf.map (homOfLE (le_top : U x ≤ ⊤)).op s' = r x := hs
  refine ⟨s', ?_⟩
  ext V t
  refine Eq.trans ?_ (globalScalarEndomorphism_app X M s' V t).symm
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩ (fun x => V ⊓ U x) V
    (fun x => homOfLE inf_le_left) (fun y hy => Opens.mem_iSup.mpr ⟨y, ⟨hy, hxU y⟩⟩)
  intro x
  have hn := NatTrans.naturality_apply φ.mapPresheaf (homOfLE (inf_le_left : V ⊓ U x ≤ V)).op t
  refine hn.symm.trans ?_
  refine (hloc x (V ⊓ U x) inf_le_right _).trans ?_
  refine Eq.trans ?_ (map_smul M (homOfLE (inf_le_left : V ⊓ U x ≤ V)) _ t).symm
  congr 1
  rw [hres, ← hs' x, hres]

end AlgebraicGeometry.Scheme.Modules
