/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Pseudofunctor
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Aglib.Algebra.Category.ModuleCat.BaseChange

/-!
# Descent data for modules as coalgebras

Mathlib's extension-of-scalars pseudofunctor
`CommRingCat.moduleCatExtendScalarsPseudofunctor` lives on `LocallyDiscrete CommRingCat`.
Precomposing it with `unopUnop CommRingCat` gives
`CommRingCat.moduleCatExtendScalarsPseudofunctorOpOp`, a pseudofunctor on
`LocallyDiscrete CommRingCatᵒᵖᵒᵖ`, which is the shape required by Mathlib's descent
predicates for the site category `CommRingCatᵒᵖ`.

For a ring map `f : A ⟶ B`, a descent datum along the single morphism `f.op` in
`CommRingCatᵒᵖ` (Mathlib's `Pseudofunctor.DescentData`, indexed by `PUnit`) determines a
coalgebra for the comonad of the adjunction `extendScalars f ⊣ restrictScalars f`. Its coaction
`N → B ⊗_A N` is the value of the descent isomorphism over `B ⊗_A B` on `1 ⊗ n`, transported
by the base-change isomorphism of the pushout square (`ModuleCat.baseChangeMap`). This file
constructs that functor `ExtendScalarsDescent.coalgebraFunctor f`, proves that it is fully
faithful, and identifies its composite with `toDescentData` with Mathlib's
`Comonad.comparison`. No flatness hypothesis is used here.

The pushouts `B ⊗_A B` and `B ⊗_A (B ⊗_A B)` are Mathlib's categorical pushouts in
`CommRingCat`. The counit and coassociativity of the coaction are the diagonal and cocycle
conditions of the descent datum (Vistoli, *Notes on Grothendieck topologies, fibered categories
and descent theory*, arXiv:math/0412512v4, §4.2.1, the category `Mod_{A→B}` before
Theorem 4.21; Stacks Project, Tag 023G for descent data and Tag 023H for the coaction
`n ↦ φ(n ⊗ 1)`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite Limits

namespace ModuleCat

variable {R₁ R₂ R₃ : Type u} [CommRing R₁] [CommRing R₂] [CommRing R₃]

/-- Extension of scalars along a composite, for an arbitrary proof of the composite equation.
This is `extendScalarsComp` precomposed with the identification of `extendScalars f₁₃`
with `extendScalars (f₂₃.comp f₁₂)`. -/
def extendScalarsComp' (f₁₂ : R₁ →+* R₂) (f₂₃ : R₂ →+* R₃) (f₁₃ : R₁ →+* R₃)
    (h : f₂₃.comp f₁₂ = f₁₃) :
    extendScalars.{u, u, u} f₁₃ ≅ extendScalars f₁₂ ⋙ extendScalars f₂₃ :=
  eqToIso (by subst h; rfl) ≪≫ extendScalarsComp f₁₂ f₂₃

/-- The element `1 ⊗ m` of `S ⊗_R M = (extendScalars g).obj M`. It is the value of the unit of
`extendRestrictScalarsAdj g`, typed in `(extendScalars g).obj M`; this avoids instance
mismatches between the tensor-product notations. -/
def ExtendScalars.oneTmul {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S)
    (M : ModuleCat.{u} R) (m : M) : (extendScalars g).obj M :=
  (extendRestrictScalarsAdj g).unit.app M m

open ExtendScalars

section

variable {R S : Type u} [CommRing R] [CommRing S] {g : R →+* S}

lemma extendScalars_hom_ext' {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    {α β : (extendScalars g).obj M ⟶ N} (h : ∀ m : M, α (oneTmul g M m) = β (oneTmul g M m)) :
    α = β :=
  ExtendScalars.hom_ext h

variable (g)

lemma extendScalars_map_oneTmul {M M' : ModuleCat.{u} R} (φ : M ⟶ M') (m : M) :
    (extendScalars g).map φ (oneTmul g M m) = oneTmul g M' (φ m) :=
  rfl

lemma extendRestrictScalarsAdj_homEquiv_apply' {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (φ : (extendScalars g).obj M ⟶ N) (m : M) :
    (extendRestrictScalarsAdj g).homEquiv _ _ φ m = φ (oneTmul g M m) :=
  rfl

lemma extendRestrictScalarsAdj_counit_app_oneTmul (N : ModuleCat.{u} S) (n : N) :
    (extendRestrictScalarsAdj g).counit.app N (oneTmul g ((restrictScalars g).obj N) n) = n :=
  ConcreteCategory.congr_hom ((extendRestrictScalarsAdj g).right_triangle_components N) n

end

lemma extendScalarsId_hom_app_oneTmul {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (m : M) :
    (extendScalarsId R).hom.app M (oneTmul (RingHom.id R) M m) = m :=
  extendScalarsId_hom_app_one_tmul M m

variable (f₁₂ : R₁ →+* R₂) (f₂₃ : R₂ →+* R₃) (f₁₃ : R₁ →+* R₃) (h : f₂₃.comp f₁₂ = f₁₃)

lemma extendScalarsComp'_hom_app_oneTmul (M : ModuleCat.{u} R₁) (m : M) :
    (extendScalarsComp' f₁₂ f₂₃ f₁₃ h).hom.app M (oneTmul f₁₃ M m) =
      oneTmul f₂₃ ((extendScalars f₁₂).obj M) (oneTmul f₁₂ M m) := by
  subst h
  exact extendScalarsComp_hom_app_one_tmul f₁₂ f₂₃ M m

lemma extendScalarsComp'_inv_app_oneTmul (M : ModuleCat.{u} R₁) (m : M) :
    (extendScalarsComp' f₁₂ f₂₃ f₁₃ h).inv.app M
      (oneTmul f₂₃ ((extendScalars f₁₂).obj M) (oneTmul f₁₂ M m)) = oneTmul f₁₃ M m := by
  rw [← extendScalarsComp'_hom_app_oneTmul]
  exact ConcreteCategory.congr_hom ((extendScalarsComp' f₁₂ f₂₃ f₁₃ h).hom_inv_id_app M) _

lemma baseChangeMap_oneTmul {R A S B : CommRingCat.{u}} (φ : R ⟶ A) (ψ : R ⟶ S) (ρ : A ⟶ B)
    (σ : S ⟶ B) (w : φ ≫ ρ = ψ ≫ σ) (M : ModuleCat.{u} A) (m : M) :
    baseChangeMap φ ψ ρ σ w M (oneTmul ψ.hom ((restrictScalars φ.hom).obj M) m) =
      oneTmul ρ.hom M m :=
  baseChangeMap_unit_apply φ ψ ρ σ w M m

lemma extendScalarsId_hom_app_oneTmul' (B : CommRingCat.{u}) (M : ModuleCat.{u} B) (m : M) :
    (extendScalarsId B).hom.app M (oneTmul (CommRingCat.Hom.hom (𝟙 B)) M m) = m :=
  extendScalarsId_hom_app_one_tmul M m

end ModuleCat

namespace CommRingCat

open ModuleCat ModuleCat.ExtendScalars

/-- Mathlib's extension-of-scalars pseudofunctor `moduleCatExtendScalarsPseudofunctor`,
precomposed with the canonical isomorphism `unopUnop : CommRingCatᵒᵖᵒᵖ ⥤ CommRingCat`.
It is a pseudofunctor `LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` for the site category
`C = CommRingCatᵒᵖ` of affine schemes, so that Mathlib's descent predicates
`Pseudofunctor.IsStackFor` and `Pseudofunctor.IsStack` apply. -/
def moduleCatExtendScalarsPseudofunctorOpOp :
    Pseudofunctor (LocallyDiscrete CommRingCat.{u}ᵒᵖᵒᵖ) Cat :=
  (unopUnop CommRingCat.{u}).toPseudofunctor.comp moduleCatExtendScalarsPseudofunctor.{u}

variable {R S T : CommRingCat.{u}}

lemma moduleCatExtendScalarsPseudofunctorOpOp_mapComp'_hom_app (g : R ⟶ S) (h : S ⟶ T)
    (gh : R ⟶ T) (e : g ≫ h = gh) (hh : g.op.op.toLoc ≫ h.op.op.toLoc = gh.op.op.toLoc)
    (M : ModuleCat.{u} R) :
    (moduleCatExtendScalarsPseudofunctorOpOp.mapComp' g.op.op.toLoc h.op.op.toLoc
      gh.op.op.toLoc hh).hom.toNatTrans.app M =
      (extendScalarsComp' g.hom h.hom gh.hom (by rw [← e]; rfl)).hom.app M := by
  subst e
  rfl

lemma moduleCatExtendScalarsPseudofunctorOpOp_mapComp'_inv_app (g : R ⟶ S) (h : S ⟶ T)
    (gh : R ⟶ T) (e : g ≫ h = gh) (hh : g.op.op.toLoc ≫ h.op.op.toLoc = gh.op.op.toLoc)
    (M : ModuleCat.{u} R) :
    (moduleCatExtendScalarsPseudofunctorOpOp.mapComp' g.op.op.toLoc h.op.op.toLoc
      gh.op.op.toLoc hh).inv.toNatTrans.app M =
      (extendScalarsComp' g.hom h.hom gh.hom (by rw [← e]; rfl)).inv.app M := by
  subst e
  rfl

/-- Variant of `moduleCatExtendScalarsPseudofunctorOpOp_mapComp'_hom_app` for an object of the
category `moduleCatExtendScalarsPseudofunctorOpOp.obj ⟨op (op R)⟩`. -/
lemma moduleCatExtendScalarsPseudofunctorOpOp_mapComp'_hom_app' (g : R ⟶ S) (h : S ⟶ T)
    (gh : R ⟶ T) (e : g ≫ h = gh) (hh : g.op.op.toLoc ≫ h.op.op.toLoc = gh.op.op.toLoc)
    (M : moduleCatExtendScalarsPseudofunctorOpOp.obj ⟨op (op R)⟩) :
    (moduleCatExtendScalarsPseudofunctorOpOp.mapComp' g.op.op.toLoc h.op.op.toLoc
      gh.op.op.toLoc hh).hom.toNatTrans.app M =
      (extendScalarsComp' g.hom h.hom gh.hom (by rw [← e]; rfl)).hom.app M := by
  subst e
  rfl

/-- Variant of `moduleCatExtendScalarsPseudofunctorOpOp_mapComp'_inv_app` for an object of the
category `moduleCatExtendScalarsPseudofunctorOpOp.obj ⟨op (op R)⟩`. -/
lemma moduleCatExtendScalarsPseudofunctorOpOp_mapComp'_inv_app' (g : R ⟶ S) (h : S ⟶ T)
    (gh : R ⟶ T) (e : g ≫ h = gh) (hh : g.op.op.toLoc ≫ h.op.op.toLoc = gh.op.op.toLoc)
    (M : moduleCatExtendScalarsPseudofunctorOpOp.obj ⟨op (op R)⟩) :
    (moduleCatExtendScalarsPseudofunctorOpOp.mapComp' g.op.op.toLoc h.op.op.toLoc
      gh.op.op.toLoc hh).inv.toNatTrans.app M =
      (extendScalarsComp' g.hom h.hom gh.hom (by rw [← e]; rfl)).inv.app M := by
  subst e
  rfl

namespace ExtendScalarsDescent

variable {A B : CommRingCat.{u}} {f : A ⟶ B}

/-- The category of descent data for modules along the single morphism `f.op : op B ⟶ op A`
of `CommRingCatᵒᵖ`, as an abbreviation of Mathlib's `Pseudofunctor.DescentData`. -/
abbrev Data (f : A ⟶ B) :=
  (moduleCatExtendScalarsPseudofunctorOpOp.{u}).DescentData (fun (_ : PUnit.{1}) ↦ f.op)

/-- The `B`-module underlying a descent datum. -/
abbrev module (D : Data f) : ModuleCat.{u} B := D.obj PUnit.unit

/-- The `B`-linear map underlying a morphism of descent data. -/
def homModule {D₁ D₂ : Data f} (φ : D₁ ⟶ D₂) : module D₁ ⟶ module D₂ := φ.hom PUnit.unit

/-- The descent morphism of `D` over a ring `R` with two maps `u₁ u₂ : B ⟶ R` that agree
on `A`, written with Mathlib's extension of scalars. -/
def hom' (D : Data f) {R : CommRingCat.{u}} (u₁ u₂ : B ⟶ R) (h : f ≫ u₁ = f ≫ u₂) :
    (extendScalars u₁.hom).obj (module D) ⟶ (extendScalars u₂.hom).obj (module D) :=
  D.hom (f ≫ u₁).op (i₁ := PUnit.unit) (i₂ := PUnit.unit) u₁.op u₂.op rfl
    (by rw [h]; rfl)

lemma hom_eq_hom' (D : Data f) {Y : CommRingCat.{u}ᵒᵖ} (q : Y ⟶ op A) (f₁ f₂ : Y ⟶ op B)
    (hf₁ : f₁ ≫ f.op = q) (hf₂ : f₂ ≫ f.op = q) :
    D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) f₁ f₂ hf₁ hf₂ =
      hom' D f₁.unop f₂.unop (Quiver.Hom.op_inj (hf₁.trans hf₂.symm)) := by
  subst hf₁
  rfl

lemma hom'_self (D : Data f) {R : CommRingCat.{u}} (u : B ⟶ R) :
    hom' D u u rfl = 𝟙 _ :=
  D.hom_self (f ≫ u).op (i := PUnit.unit) u.op rfl

@[reassoc]
lemma hom'_comp (D : Data f) {R : CommRingCat.{u}} (u₁ u₂ u₃ : B ⟶ R)
    (h₁₂ : f ≫ u₁ = f ≫ u₂) (h₂₃ : f ≫ u₂ = f ≫ u₃) :
    hom' D u₁ u₂ h₁₂ ≫ hom' D u₂ u₃ h₂₃ = hom' D u₁ u₃ (h₁₂.trans h₂₃) := by
  have := D.hom_comp (f ≫ u₁).op (i₁ := PUnit.unit) (i₂ := PUnit.unit) (i₃ := PUnit.unit)
    u₁.op u₂.op u₃.op rfl (by rw [h₁₂]; rfl) (by rw [h₁₂, h₂₃]; rfl)
  rwa [hom_eq_hom', hom_eq_hom', hom_eq_hom'] at this

/-- Pulling back the descent morphism along `g : R ⟶ R'` (the axiom `pullHom_hom`). -/
lemma hom'_eq_of_comp (D : Data f) {R R' : CommRingCat.{u}} (u₁ u₂ : B ⟶ R)
    (h : f ≫ u₁ = f ≫ u₂) (g : R ⟶ R') (v₁ v₂ : B ⟶ R') (e₁ : u₁ ≫ g = v₁)
    (e₂ : u₂ ≫ g = v₂) :
    hom' D v₁ v₂ (by rw [← e₁, ← e₂, ← Category.assoc, h, Category.assoc]) =
      (extendScalarsComp' u₁.hom g.hom v₁.hom (by rw [← e₁]; rfl)).hom.app (module D) ≫
        (extendScalars g.hom).map (hom' D u₁ u₂ h) ≫
          (extendScalarsComp' u₂.hom g.hom v₂.hom (by rw [← e₂]; rfl)).inv.app (module D) := by
  have := D.pullHom_hom g.op (f ≫ u₁).op (f ≫ v₁).op (by rw [← e₁]; rfl)
    (i₁ := PUnit.unit) (i₂ := PUnit.unit) u₁.op u₂.op rfl (by rw [h]; rfl) v₁.op v₂.op
    (by rw [← e₁]; rfl) (by rw [← e₂]; rfl)
  rw [hom_eq_hom'] at this
  dsimp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom] at this
  rw [moduleCatExtendScalarsPseudofunctorOpOp_mapComp'_hom_app' _ _ _ e₁,
    moduleCatExtendScalarsPseudofunctorOpOp_mapComp'_inv_app' _ _ _ e₂] at this
  exact this.symm

lemma hom'_eq_of_comp_apply (D : Data f) {R R' : CommRingCat.{u}} (u₁ u₂ : B ⟶ R)
    (h : f ≫ u₁ = f ≫ u₂) (g : R ⟶ R') (v₁ v₂ : B ⟶ R') (e₁ : u₁ ≫ g = v₁)
    (e₂ : u₂ ≫ g = v₂) (n : module D) :
    hom' D v₁ v₂ (by rw [← e₁, ← e₂, ← Category.assoc, h, Category.assoc])
        (oneTmul v₁.hom (module D) n) =
      (extendScalarsComp' u₂.hom g.hom v₂.hom (by rw [← e₂]; rfl)).inv.app (module D)
        (oneTmul g.hom ((extendScalars u₂.hom).obj (module D))
          (hom' D u₁ u₂ h (oneTmul u₁.hom (module D) n))) := by
  rw [hom'_eq_of_comp D u₁ u₂ h g v₁ v₂ e₁ e₂, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, extendScalarsComp'_hom_app_oneTmul, extendScalars_map_oneTmul]

lemma comm_hom' {D₁ D₂ : Data f} (φ : D₁ ⟶ D₂) {R : CommRingCat.{u}} (u₁ u₂ : B ⟶ R)
    (h : f ≫ u₁ = f ≫ u₂) :
    (extendScalars u₁.hom).map (homModule φ) ≫ hom' D₂ u₁ u₂ h =
      hom' D₁ u₁ u₂ h ≫ (extendScalars u₂.hom).map (homModule φ) :=
  φ.comm (f ≫ u₁).op (i₁ := PUnit.unit) (i₂ := PUnit.unit) u₁.op u₂.op rfl (by rw [h]; rfl)

lemma toDescentData_obj_hom' (M : moduleCatExtendScalarsPseudofunctorOpOp.obj ⟨op (op A)⟩)
    {R : CommRingCat.{u}} (u₁ u₂ : B ⟶ R)
    (h : f ≫ u₁ = f ≫ u₂) :
    hom' ((moduleCatExtendScalarsPseudofunctorOpOp.{u}).toDescentData
        (fun (_ : PUnit.{1}) ↦ f.op) |>.obj M) u₁ u₂ h =
      (extendScalarsComp' f.hom u₁.hom (f ≫ u₁).hom rfl).inv.app M ≫
        (extendScalarsComp' f.hom u₂.hom (f ≫ u₁).hom (by rw [h]; rfl)).hom.app M := by
  rw [← moduleCatExtendScalarsPseudofunctorOpOp_mapComp'_inv_app' f u₁ (f ≫ u₁) rfl rfl M,
    ← moduleCatExtendScalarsPseudofunctorOpOp_mapComp'_hom_app' f u₂ (f ≫ u₁) h.symm
      (by rw [h]; rfl) M]
  rfl

/-! ### The coaction -/

/-- The descent morphism as a `B`-linear map `N ⟶ u₁_* u₂^* N`, `n ↦ hom' (1 ⊗ n)`. -/
def theta (D : Data f) {R : CommRingCat.{u}} (u₁ u₂ : B ⟶ R) (h : f ≫ u₁ = f ≫ u₂) :
    module D ⟶ (restrictScalars u₁.hom).obj ((extendScalars u₂.hom).obj (module D)) :=
  (extendRestrictScalarsAdj u₁.hom).homEquiv _ _ (hom' D u₁ u₂ h)

lemma theta_apply (D : Data f) {R : CommRingCat.{u}} (u₁ u₂ : B ⟶ R) (h : f ≫ u₁ = f ≫ u₂)
    (n : module D) : theta D u₁ u₂ h n = hom' D u₁ u₂ h (oneTmul u₁.hom (module D) n) :=
  rfl

/-- Pullback along `g : R ⟶ R'` as a map `u₁_* u₂^* N ⟶ v₁_* v₂^* N`, `z ↦ 1 ⊗ z`. -/
def pull (N : ModuleCat.{u} B) {R R' : CommRingCat.{u}} (u₁ u₂ : B ⟶ R) (g : R ⟶ R')
    (v₁ v₂ : B ⟶ R') (e₁ : u₁ ≫ g = v₁) (e₂ : u₂ ≫ g = v₂) :
    (restrictScalars u₁.hom).obj ((extendScalars u₂.hom).obj N) ⟶
      (restrictScalars v₁.hom).obj ((extendScalars v₂.hom).obj N) :=
  (restrictScalars u₁.hom).map ((extendRestrictScalarsAdj g.hom).unit.app _) ≫
    (restrictScalarsComp'App u₁.hom g.hom v₁.hom (by rw [← e₁]; rfl) _).inv ≫
      (restrictScalars v₁.hom).map
        ((extendScalarsComp' u₂.hom g.hom v₂.hom (by rw [← e₂]; rfl)).inv.app N)

lemma pull_apply (N : ModuleCat.{u} B) {R R' : CommRingCat.{u}} (u₁ u₂ : B ⟶ R) (g : R ⟶ R')
    (v₁ v₂ : B ⟶ R') (e₁ : u₁ ≫ g = v₁) (e₂ : u₂ ≫ g = v₂)
    (z : (extendScalars u₂.hom).obj N) :
    pull N u₁ u₂ g v₁ v₂ e₁ e₂ z =
      (extendScalarsComp' u₂.hom g.hom v₂.hom (by rw [← e₂]; rfl)).inv.app N
        (oneTmul g.hom ((extendScalars u₂.hom).obj N) z) :=
  rfl

@[reassoc]
lemma theta_comp_pull (D : Data f) {R R' : CommRingCat.{u}} (u₁ u₂ : B ⟶ R)
    (h : f ≫ u₁ = f ≫ u₂) (g : R ⟶ R') (v₁ v₂ : B ⟶ R') (e₁ : u₁ ≫ g = v₁)
    (e₂ : u₂ ≫ g = v₂) :
    theta D u₁ u₂ h ≫ pull (module D) u₁ u₂ g v₁ v₂ e₁ e₂ =
      theta D v₁ v₂ (by rw [← e₁, ← e₂, ← Category.assoc, h, Category.assoc]) := by
  ext n
  rw [ConcreteCategory.comp_apply, theta_apply, theta_apply,
    hom'_eq_of_comp_apply D u₁ u₂ h g v₁ v₂ e₁ e₂]
  erw [pull_apply]

@[reassoc]
lemma theta_comp_hom' (D : Data f) {R : CommRingCat.{u}} (u₁ u₂ u₃ : B ⟶ R)
    (h₁₂ : f ≫ u₁ = f ≫ u₂) (h₂₃ : f ≫ u₂ = f ≫ u₃) :
    theta D u₁ u₂ h₁₂ ≫ (restrictScalars u₁.hom).map (hom' D u₂ u₃ h₂₃) =
      theta D u₁ u₃ (h₁₂.trans h₂₃) := by
  ext n
  rw [ConcreteCategory.comp_apply, theta_apply, theta_apply, ← hom'_comp D u₁ u₂ u₃ h₁₂ h₂₃]
  rfl

lemma theta_naturality {D₁ D₂ : Data f} (φ : D₁ ⟶ D₂) {R : CommRingCat.{u}} (u₁ u₂ : B ⟶ R)
    (h : f ≫ u₁ = f ≫ u₂) :
    homModule φ ≫ theta D₂ u₁ u₂ h =
      theta D₁ u₁ u₂ h ≫ (restrictScalars u₁.hom).map ((extendScalars u₂.hom).map
        (homModule φ)) := by
  rw [theta, theta, ← Adjunction.homEquiv_naturality_left,
    ← Adjunction.homEquiv_naturality_right, comm_hom']

variable (f) in
/-- The base-change isomorphism `B ⊗_A N ≅ ι₁_* ι₂^* N` of the pushout square of `f` with
itself (Aglib's `ModuleCat.baseChangeMap`). -/
def bc (N : ModuleCat.{u} B) :
    (extendScalars f.hom).obj ((restrictScalars f.hom).obj N) ⟶
      (restrictScalars (pushout.inl f f).hom).obj ((extendScalars (pushout.inr f f).hom).obj N) :=
  baseChangeMap f f (pushout.inr f f) (pushout.inl f f) pushout.condition.symm N

instance (N : ModuleCat.{u} B) : IsIso (bc f N) :=
  baseChangeMap_isIso _ _ _ _ (IsPushout.of_hasPushout f f).flip N

lemma bc_oneTmul (N : ModuleCat.{u} B) (n : N) :
    bc f N (oneTmul f.hom ((restrictScalars f.hom).obj N) n) =
      oneTmul (pushout.inr f f).hom N n :=
  baseChangeMap_oneTmul _ _ _ _ _ N n

@[reassoc]
lemma bc_naturality {N N' : ModuleCat.{u} B} (φ : N ⟶ N') :
    (extendScalars f.hom).map ((restrictScalars f.hom).map φ) ≫ bc f N' =
      bc f N ≫ (restrictScalars (pushout.inl f f).hom).map
        ((extendScalars (pushout.inr f f).hom).map φ) := by
  apply extendScalars_hom_ext'
  intro n
  exact (bc_oneTmul (f := f) N' (φ n)).trans (congrArg ((restrictScalars (pushout.inl f f).hom).map
    ((extendScalars (pushout.inr f f).hom).map φ)) (bc_oneTmul (f := f) N n)).symm

/-- The coaction `N ⟶ B ⊗_A N` of a descent datum. -/
def coaction (D : Data f) :
    module D ⟶ (extendScalars f.hom).obj ((restrictScalars f.hom).obj (module D)) :=
  theta D (pushout.inl f f) (pushout.inr f f) pushout.condition ≫ inv (bc f (module D))

@[reassoc (attr := simp)]
lemma coaction_comp_bc (D : Data f) :
    coaction D ≫ bc f (module D) =
      theta D (pushout.inl f f) (pushout.inr f f) pushout.condition := by
  simp [coaction]

variable (f) in
/-- The codiagonal `B ⊗_A B ⟶ B`. -/
abbrev codiag : pushout f f ⟶ B := pushout.desc (𝟙 B) (𝟙 B) rfl

lemma inl_codiag : pushout.inl f f ≫ codiag f = 𝟙 B := pushout.inl_desc _ _ _

lemma inr_codiag : pushout.inr f f ≫ codiag f = 𝟙 B := pushout.inr_desc _ _ _

variable (f) in
/-- The map `ι₁_* ι₂^* N ⟶ N`, `x ⊗ n ↦ codiag(x) n`. -/
def kappa (N : ModuleCat.{u} B) :
    (restrictScalars (pushout.inl f f).hom).obj ((extendScalars (pushout.inr f f).hom).obj N) ⟶
      N :=
  pull N (pushout.inl f f) (pushout.inr f f) (codiag f) (𝟙 B) (𝟙 B) inl_codiag inr_codiag ≫
    (restrictScalars (CommRingCat.Hom.hom (𝟙 B))).map ((extendScalarsId B).hom.app N) ≫
      (restrictScalarsId'App (CommRingCat.Hom.hom (𝟙 B)) rfl N).hom

lemma kappa_oneTmul (N : ModuleCat.{u} B) (n : N) :
    kappa f N (oneTmul (pushout.inr f f).hom N n) = n :=
  (congrArg ((extendScalarsId B).hom.app N) (extendScalarsComp'_inv_app_oneTmul
    (pushout.inr f f).hom (codiag f).hom (CommRingCat.Hom.hom (𝟙 B))
    (congrArg CommRingCat.Hom.hom inr_codiag) N n)).trans (extendScalarsId_hom_app_oneTmul' B N n)

lemma bc_comp_kappa (N : ModuleCat.{u} B) :
    bc f N ≫ kappa f N = (extendRestrictScalarsAdj f.hom).counit.app N := by
  apply extendScalars_hom_ext'
  intro n
  exact (congrArg (kappa f N) (bc_oneTmul (f := f) N n)).trans ((kappa_oneTmul N n).trans
    (extendRestrictScalarsAdj_counit_app_oneTmul f.hom N n).symm)

lemma theta_comp_kappa (D : Data f) :
    theta D (pushout.inl f f) (pushout.inr f f) pushout.condition ≫ kappa f (module D) = 𝟙 _ := by
  rw [kappa, theta_comp_pull_assoc]
  ext n
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, theta_apply, hom'_self]
  exact extendScalarsId_hom_app_oneTmul' B (module D) n

lemma coaction_counit (D : Data f) :
    coaction D ≫ (extendRestrictScalarsAdj f.hom).counit.app (module D) = 𝟙 _ := by
  rw [← bc_comp_kappa, coaction_comp_bc_assoc, theta_comp_kappa]

variable (f) in
/-- The triple pushout `B ⊗_A (B ⊗_A B)`. -/
abbrev P₃ := pushout f (f ≫ pushout.inl f f)

variable (f) in
/-- The coprojection `B ⟶ P₃` onto the first factor. -/
abbrev tj : B ⟶ P₃ f := pushout.inl _ _

variable (f) in
/-- The coprojection `B ⊗_A B ⟶ P₃` onto the last two factors. -/
abbrev tk : pushout f f ⟶ P₃ f := pushout.inr _ _

lemma tj_condition : f ≫ tj f = (f ≫ pushout.inl f f) ≫ tk f := pushout.condition

variable (f) in
/-- The map `B ⊗_A B ⟶ P₃` onto the first two factors. -/
def p₁₂ : pushout f f ⟶ P₃ f :=
  pushout.desc (tj f) (pushout.inl f f ≫ tk f) (by rw [tj_condition, Category.assoc])

variable (f) in
/-- The map `B ⊗_A B ⟶ P₃` onto the first and last factors. -/
def p₁₃ : pushout f f ⟶ P₃ f :=
  pushout.desc (tj f) (pushout.inr f f ≫ tk f)
    (by rw [tj_condition, ← Category.assoc, pushout.condition])

lemma inl_p₁₂ : pushout.inl f f ≫ p₁₂ f = tj f := pushout.inl_desc _ _ _

lemma inr_p₁₂ : pushout.inr f f ≫ p₁₂ f = pushout.inl f f ≫ tk f := pushout.inr_desc _ _ _

lemma inl_p₁₃ : pushout.inl f f ≫ p₁₃ f = tj f := pushout.inl_desc _ _ _

lemma inr_p₁₃ : pushout.inr f f ≫ p₁₃ f = pushout.inr f f ≫ tk f := pushout.inr_desc _ _ _

variable (f) in
/-- The isomorphism `B ⊗_A (B ⊗_A N) ≅ (tj)_* (inr ≫ tk)^* N` used to detect coassociativity. -/
def xi (N : ModuleCat.{u} B) :
    (extendScalars f.hom).obj ((restrictScalars f.hom).obj
      ((extendScalars f.hom).obj ((restrictScalars f.hom).obj N))) ⟶
      (restrictScalars (tj f).hom).obj ((extendScalars (pushout.inr f f ≫ tk f).hom).obj N) :=
  (extendScalars f.hom).map ((restrictScalars f.hom).map (bc f N)) ≫
    (extendScalars f.hom).map (restrictScalarsComp'App f.hom (pushout.inl f f).hom
      (f ≫ pushout.inl f f).hom rfl ((extendScalars (pushout.inr f f).hom).obj N)).inv ≫
    baseChangeMap (f ≫ pushout.inl f f) f (tk f) (tj f) tj_condition.symm
      ((extendScalars (pushout.inr f f).hom).obj N) ≫
    (restrictScalars (tj f).hom).map
      ((extendScalarsComp' (pushout.inr f f).hom (tk f).hom (pushout.inr f f ≫ tk f).hom
        rfl).inv.app N)

instance (N : ModuleCat.{u} B) : IsIso (xi f N) := by
  have : IsIso (baseChangeMap (f ≫ pushout.inl f f) f (tk f) (tj f) tj_condition.symm
      ((extendScalars (pushout.inr f f).hom).obj N)) :=
    baseChangeMap_isIso _ _ _ _ (IsPushout.of_hasPushout f (f ≫ pushout.inl f f)).flip _
  dsimp only [xi]
  infer_instance

lemma xi_oneTmul (N : ModuleCat.{u} B)
    (y : (extendScalars f.hom).obj ((restrictScalars f.hom).obj N)) :
    xi f N (oneTmul f.hom ((restrictScalars f.hom).obj
      ((extendScalars f.hom).obj ((restrictScalars f.hom).obj N))) y) =
      (extendScalarsComp' (pushout.inr f f).hom (tk f).hom (pushout.inr f f ≫ tk f).hom
        rfl).inv.app N (oneTmul (tk f).hom ((extendScalars (pushout.inr f f).hom).obj N)
          (bc f N y)) := by
  exact congrArg ((extendScalarsComp' (pushout.inr f f).hom (tk f).hom
    (pushout.inr f f ≫ tk f).hom rfl).inv.app N) (baseChangeMap_oneTmul (f ≫ pushout.inl f f) f
      (tk f) (tj f) tj_condition.symm ((extendScalars (pushout.inr f f).hom).obj N) (bc f N y))

lemma delta_comp_xi (N : ModuleCat.{u} B) :
    (extendScalars f.hom).map ((extendRestrictScalarsAdj f.hom).unit.app
      ((restrictScalars f.hom).obj N)) ≫ xi f N =
      bc f N ≫ pull N (pushout.inl f f) (pushout.inr f f) (p₁₃ f) (tj f)
        (pushout.inr f f ≫ tk f) inl_p₁₃ inr_p₁₃ := by
  apply extendScalars_hom_ext'
  intro n
  have e₁ := xi_oneTmul (f := f) N (oneTmul f.hom ((restrictScalars f.hom).obj N) n)
  rw [bc_oneTmul (f := f) N n, extendScalarsComp'_inv_app_oneTmul (pushout.inr f f).hom
    (tk f).hom (pushout.inr f f ≫ tk f).hom rfl N n] at e₁
  have e₂ : pull N (pushout.inl f f) (pushout.inr f f) (p₁₃ f) (tj f) (pushout.inr f f ≫ tk f)
      inl_p₁₃ inr_p₁₃ (oneTmul (pushout.inr f f).hom N n) =
      oneTmul (pushout.inr f f ≫ tk f).hom N n :=
    extendScalarsComp'_inv_app_oneTmul _ _ _ (congrArg CommRingCat.Hom.hom inr_p₁₃) N n
  exact e₁.trans (e₂.symm.trans (congrArg (pull N (pushout.inl f f) (pushout.inr f f) (p₁₃ f)
    (tj f) (pushout.inr f f ≫ tk f) inl_p₁₃ inr_p₁₃) (bc_oneTmul (f := f) N n).symm))

lemma map_coaction_comp_xi (D : Data f) :
    (extendScalars f.hom).map ((restrictScalars f.hom).map (coaction D)) ≫ xi f (module D) =
      bc f (module D) ≫ pull (module D) (pushout.inl f f) (pushout.inr f f) (p₁₂ f) (tj f)
        (pushout.inl f f ≫ tk f) inl_p₁₂ inr_p₁₂ ≫
        (restrictScalars (tj f).hom).map (hom' D (pushout.inl f f ≫ tk f)
          (pushout.inr f f ≫ tk f)
          (by rw [← Category.assoc, pushout.condition, Category.assoc])) := by
  apply extendScalars_hom_ext'
  intro n
  rw [ConcreteCategory.comp_apply, extendScalars_map_oneTmul]
  have h₁ : bc f (module D) ((restrictScalars f.hom).map (coaction D) n) =
      theta D (pushout.inl f f) (pushout.inr f f) pushout.condition n :=
    ConcreteCategory.congr_hom (coaction_comp_bc D) n
  have h₂ := ConcreteCategory.congr_hom (theta_comp_pull D (pushout.inl f f) (pushout.inr f f)
    pushout.condition (tk f) (pushout.inl f f ≫ tk f) (pushout.inr f f ≫ tk f) rfl rfl) n
  rw [CategoryTheory.comp_apply (theta D (pushout.inl f f) (pushout.inr f f) pushout.condition)
      (pull (module D) (pushout.inl f f) (pushout.inr f f) (tk f) (pushout.inl f f ≫ tk f)
        (pushout.inr f f ≫ tk f) rfl rfl) n,
    pull_apply (module D) (pushout.inl f f) (pushout.inr f f) (tk f) (pushout.inl f f ≫ tk f)
      (pushout.inr f f ≫ tk f) rfl rfl
      (theta D (pushout.inl f f) (pushout.inr f f) pushout.condition n),
    theta_apply D (pushout.inl f f ≫ tk f) (pushout.inr f f ≫ tk f)
      (by rw [← Category.assoc, pushout.condition, Category.assoc]) n] at h₂
  have e₃ : pull (module D) (pushout.inl f f) (pushout.inr f f) (p₁₂ f) (tj f)
      (pushout.inl f f ≫ tk f) inl_p₁₂ inr_p₁₂ (oneTmul (pushout.inr f f).hom (module D) n) =
      oneTmul (pushout.inl f f ≫ tk f).hom (module D) n :=
    extendScalarsComp'_inv_app_oneTmul _ _ _ (congrArg CommRingCat.Hom.hom inr_p₁₂) (module D) n
  rw [xi_oneTmul (f := f) (module D) ((restrictScalars f.hom).map (coaction D) n), h₁, h₂,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    bc_oneTmul (f := f) (module D) n]
  exact congrArg (hom' D (pushout.inl f f ≫ tk f) (pushout.inr f f ≫ tk f)
    (by rw [← Category.assoc, pushout.condition, Category.assoc])) e₃.symm

lemma coaction_coassoc (D : Data f) :
    coaction D ≫ (extendScalars f.hom).map ((extendRestrictScalarsAdj f.hom).unit.app
      ((restrictScalars f.hom).obj (module D))) =
      coaction D ≫ (extendScalars f.hom).map ((restrictScalars f.hom).map (coaction D)) := by
  rw [← cancel_mono (xi f (module D)), Category.assoc, Category.assoc, delta_comp_xi,
    map_coaction_comp_xi, coaction_comp_bc_assoc, coaction_comp_bc_assoc, theta_comp_pull,
    theta_comp_pull_assoc, theta_comp_hom']

@[reassoc]
lemma coaction_naturality {D₁ D₂ : Data f} (φ : D₁ ⟶ D₂) :
    coaction D₁ ≫ (extendScalars f.hom).map ((restrictScalars f.hom).map (homModule φ)) =
      homModule φ ≫ coaction D₂ := by
  rw [← cancel_mono (bc f (module D₂)), Category.assoc, Category.assoc, bc_naturality,
    coaction_comp_bc, coaction_comp_bc_assoc, theta_naturality]

variable (f) in
/-- The functor from descent data along `f.op` to coalgebras over the comonad of
`extendScalars f ⊣ restrictScalars f`. -/
def coalgebraFunctor : Data f ⥤ (extendRestrictScalarsAdj f.hom).toComonad.Coalgebra where
  obj D :=
    { A := module D
      a := coaction D
      counit := coaction_counit D
      coassoc := coaction_coassoc D }
  map φ :=
    { f := homModule φ
      h := coaction_naturality φ }

/-! ### Full faithfulness -/

lemma comm_universal {D₁ D₂ : Data f} (g : module D₁ ⟶ module D₂)
    (hg : coaction D₁ ≫ (extendScalars f.hom).map ((restrictScalars f.hom).map g) =
      g ≫ coaction D₂) :
    (extendScalars (pushout.inl f f).hom).map g ≫
        hom' D₂ (pushout.inl f f) (pushout.inr f f) pushout.condition =
      hom' D₁ (pushout.inl f f) (pushout.inr f f) pushout.condition ≫
        (extendScalars (pushout.inr f f).hom).map g := by
  apply ((extendRestrictScalarsAdj (pushout.inl f f).hom).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  change g ≫ theta D₂ _ _ _ = theta D₁ _ _ _ ≫ _
  rw [← coaction_comp_bc, ← coaction_comp_bc, ← Category.assoc, ← hg]
  simp only [Category.assoc]
  rw [bc_naturality]

lemma comm_of_coaction {D₁ D₂ : Data f} (g : module D₁ ⟶ module D₂)
    (hg : coaction D₁ ≫ (extendScalars f.hom).map ((restrictScalars f.hom).map g) =
      g ≫ coaction D₂) {R : CommRingCat.{u}} (u₁ u₂ : B ⟶ R) (h : f ≫ u₁ = f ≫ u₂) :
    (extendScalars u₁.hom).map g ≫ hom' D₂ u₁ u₂ h =
      hom' D₁ u₁ u₂ h ≫ (extendScalars u₂.hom).map g := by
  have e₁ : pushout.inl f f ≫ pushout.desc u₁ u₂ h = u₁ := pushout.inl_desc _ _ _
  have e₂ : pushout.inr f f ≫ pushout.desc u₁ u₂ h = u₂ := pushout.inr_desc _ _ _
  rw [hom'_eq_of_comp D₂ _ _ pushout.condition (pushout.desc u₁ u₂ h) u₁ u₂ e₁ e₂,
    hom'_eq_of_comp D₁ _ _ pushout.condition (pushout.desc u₁ u₂ h) u₁ u₂ e₁ e₂]
  have n₁ := (extendScalarsComp' (pushout.inl f f).hom (pushout.desc u₁ u₂ h).hom u₁.hom
    (congrArg CommRingCat.Hom.hom e₁)).hom.naturality g
  have n₂ := (extendScalarsComp' (pushout.inr f f).hom (pushout.desc u₁ u₂ h).hom u₂.hom
    (congrArg CommRingCat.Hom.hom e₂)).inv.naturality g
  dsimp only [Functor.comp_map] at n₁ n₂
  rw [reassoc_of% n₁, ← Functor.map_comp_assoc, comm_universal g hg, Functor.map_comp_assoc, n₂]
  simp only [Category.assoc]

variable (f) in
/-- `coalgebraFunctor f` is fully faithful: a morphism of coalgebras is compatible with all
descent morphisms, by the universal property of `B ⊗_A B`. -/
def fullyFaithfulCoalgebraFunctor : (coalgebraFunctor f).FullyFaithful where
  preimage {D₁ D₂} g :=
    { hom _ := g.f
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
        cases i₁
        cases i₂
        have := comm_of_coaction (D₁ := D₁) (D₂ := D₂) g.f g.h f₁.unop f₂.unop
          (Quiver.Hom.op_inj (hf₁.trans hf₂.symm))
        rw [← hom_eq_hom' D₂ q f₁ f₂ hf₁ hf₂, ← hom_eq_hom' D₁ q f₁ f₂ hf₁ hf₂] at this
        exact this }
  map_preimage _ := rfl
  preimage_map φ := by
    ext i
    cases i
    rfl

/-! ### Comparison with `Comonad.comparison` -/

lemma theta_toDescentData (M : ModuleCat.{u} A) (m : M) :
    theta ((moduleCatExtendScalarsPseudofunctorOpOp.{u}).toDescentData
        (fun (_ : PUnit.{1}) ↦ f.op) |>.obj M) (pushout.inl f f) (pushout.inr f f)
        pushout.condition (oneTmul f.hom M m) =
      oneTmul (pushout.inr f f).hom ((extendScalars f.hom).obj M) (oneTmul f.hom M m) := by
  have e := toDescentData_obj_hom' (f := f) M (pushout.inl f f) (pushout.inr f f)
    pushout.condition
  exact (ConcreteCategory.congr_hom e _).trans
    ((congrArg ((extendScalarsComp' f.hom (pushout.inr f f).hom (f ≫ pushout.inl f f).hom
      (by rw [pushout.condition]; rfl)).hom.app M) (extendScalarsComp'_inv_app_oneTmul f.hom
        (pushout.inl f f).hom (f ≫ pushout.inl f f).hom rfl M m)).trans
      (extendScalarsComp'_hom_app_oneTmul f.hom (pushout.inr f f).hom (f ≫ pushout.inl f f).hom
        (by rw [pushout.condition]; rfl) M m))

lemma coaction_toDescentData (M : ModuleCat.{u} A) :
    coaction ((moduleCatExtendScalarsPseudofunctorOpOp.{u}).toDescentData
        (fun (_ : PUnit.{1}) ↦ f.op) |>.obj M) =
      (extendScalars f.hom).map ((extendRestrictScalarsAdj f.hom).unit.app M) := by
  rw [coaction]
  apply (IsIso.comp_inv_eq (bc f _)).mpr
  refine extendScalars_hom_ext' (g := f.hom) (M := M) (fun m ↦ ?_)
  exact (theta_toDescentData M m).trans
    (bc_oneTmul (f := f) ((extendScalars f.hom).obj M) (oneTmul f.hom M m)).symm

variable (f) in
/-- The composite of `toDescentData` with `coalgebraFunctor f` is Mathlib's
`Comonad.comparison` for `extendScalars f ⊣ restrictScalars f`. -/
def toDescentDataCompCoalgebraFunctorIso :
    (moduleCatExtendScalarsPseudofunctorOpOp.{u}).toDescentData (fun (_ : PUnit.{1}) ↦ f.op) ⋙
      coalgebraFunctor f ≅ Comonad.comparison (extendRestrictScalarsAdj f.hom) :=
  NatIso.ofComponents (fun M ↦ Comonad.Coalgebra.isoMk (Iso.refl _) (by
      refine (congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans ?_
      exact (Category.comp_id _).trans ((coaction_toDescentData (f := f) M).trans
        (Category.id_comp _).symm)))
    (fun _ ↦ Comonad.Coalgebra.Hom.ext rfl)

end ExtendScalarsDescent

end CommRingCat
