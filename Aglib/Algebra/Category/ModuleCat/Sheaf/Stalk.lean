/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.OfCommRing
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Actual module stalks and membership skyscrapers over a commutative ring sheaf

For a topological space and a commutative ring sheaf in one common universe,
the actual additive stalk carries the native CommRingCat-stalk action. The
skyscraper uses the existing membership-function sections. Their maps, germ
formulas, Hom equivalence, and adjunction form one construction.

Source: `Aglib/AlgebraicGeometry/Modules/Stalk/Basic.lean` and the underlying
stalk/zero criterion in `Modules/Support.lean`, immutable audit basis
`54d6974ace11bf7d197aa925cb8cade86db8a24f`. This extracts their general
topological commutative-ring-sheaf arguments without changing the scalar or
additive stalk colimit and without an independent-universe extension.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.ExactCategory
open TopCat.Presheaf

attribute [local instance] Abelian.hasFiniteBiproducts

namespace SheafOfModulesOfCommRing

variable {T : TopCat.{u}}

-- Select the native small-limit preservation route once, rather than repeatedly
-- searching the higher-priority arbitrary-multicospan route.
local instance commRingHasSheafCompose :
    (Opens.grothendieckTopology T).HasSheafCompose
      (forget₂ CommRingCat.{u} RingCat.{u}) :=
  hasSheafCompose_of_preservesLimitsOfSize (Opens.grothendieckTopology T)
    (F := forget₂ CommRingCat.{u} RingCat.{u})

/-- The underlying abelian-group stalk functor on actual module sheaves. -/
abbrev stalkFunctor (R : T.Sheaf CommRingCat.{u}) (x : T) :
    _root_.SheafOfModulesOfCommRing
      (C := Opens T) (J := Opens.grothendieckTopology T) R ⥤ AddCommGrpCat.{u} :=
  (SheafOfModules.forget.{u} ((sheafCompose (Opens.grothendieckTopology T)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
    _root_.PresheafOfModules.toPresheaf.{u}
      ((sheafCompose (Opens.grothendieckTopology T)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj) ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (X := T) x

/-- A module sheaf is zero exactly when all its stalks are zero. -/
theorem isZero_iff_stalks {R : T.Sheaf CommRingCat.{u}} (M : _root_.SheafOfModulesOfCommRing
      (C := Opens T) (J := Opens.grothendieckTopology T) R) :
    IsZero M ↔ ∀ x : T, IsZero ((stalkFunctor R x).obj M) := by
  have h : IsZero M ↔ IsZero ((SheafOfModules.toSheaf
      ((sheafCompose (Opens.grothendieckTopology T)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)).obj M) := by
    let F := SheafOfModules.toSheaf ((sheafCompose (Opens.grothendieckTopology T)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    constructor
    · exact F.map_isZero
    · intro hM
      apply (IsZero.iff_id_eq_zero _).2
      apply F.map_injective
      rw [F.map_id, F.map_zero]
      exact (IsZero.iff_id_eq_zero _).1 hM
  exact h.trans (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero
    ((SheafOfModules.toSheaf ((sheafCompose (Opens.grothendieckTopology T)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)).obj M))

/-- A simultaneous representative of a stalk scalar and a module-stalk element. -/
theorem exists_germ_smul_representatives (R : T.Sheaf CommRingCat.{u}) (x : T)
    (M : _root_.SheafOfModulesOfCommRing
      (C := Opens T) (J := Opens.grothendieckTopology T) R) (r : TopCat.Presheaf.stalk (C :=
        CommRingCat.{u}) (X := T) R.obj x) (m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X
        := T) M.val.presheaf x) :
    ∃ (U : (Opens T)) (hx : x ∈ U) (a : (R.obj.obj (op U))) (s : (M.val.obj (op U))),
      TopCat.Presheaf.germ (C := CommRingCat.{u}) (X := T) R.obj U x hx a = r ∧
        TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := T) M.val.presheaf U x hx s = m := by
  obtain ⟨V, hxV, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := CommRingCat.{u}) (X := T) R.obj r
  obtain ⟨U, hUV, hxU, s, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq (C := AddCommGrpCat.{u}) (X :=
    T) M.val.presheaf m hxV
  exact ⟨U, hxU, R.obj.map (homOfLE hUV).op a, s,
    TopCat.Presheaf.germ_res_apply (C := CommRingCat.{u}) (X := T) R.obj _ _ _ _, rfl⟩

instance instModuleModuleStalk (R : T.Sheaf CommRingCat.{u}) (x : T) (M :
  _root_.SheafOfModulesOfCommRing
      (C := Opens T) (J := Opens.grothendieckTopology T) R) :
    Module (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := T) R.obj x) (TopCat.Presheaf.stalk
      (C := AddCommGrpCat.{u}) (X := T) M.val.presheaf x) := by
  exact inferInstanceAs (Module (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := T) R.obj x)
    ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := T) M.val.presheaf x))

/-- The actual induced map on stalks is linear over the commutative-ring-sheaf stalk. -/
def moduleStalkMap {R : T.Sheaf CommRingCat.{u}} (x : T)
    {M N : _root_.SheafOfModulesOfCommRing
      (C := Opens T) (J := Opens.grothendieckTopology T) R} (p : M ⟶ N) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := T) M.val.presheaf x
      →ₗ[TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := T) R.obj x] TopCat.Presheaf.stalk (C :=
      AddCommGrpCat.{u}) (X := T) N.val.presheaf x where
  toFun := (stalkFunctor R x).map p
  map_add' := map_add ((stalkFunctor R x).map p).hom
  map_smul' r m := by
    obtain ⟨U, hx, a, s, rfl, rfl⟩ := exists_germ_smul_representatives R x M r m
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (X := T) x).map
      ((_root_.PresheafOfModules.toPresheaf _).map p.val)
      (TopCat.Presheaf.germ (C := CommRingCat.{u}) (X := T) R.obj U x hx a • TopCat.Presheaf.germ
        (C := AddCommGrpCat.{u}) (X := T) M.val.presheaf U x hx s) = _
    erw [← _root_.PresheafOfModules.germ_smul M.val x U hx,
      TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := T) N.val.presheaf U x hx (p.val.app
      (op U) (a • s)) = _
    erw [(p.val.app (op U)).hom.map_smul, _root_.PresheafOfModules.germ_smul N.val x U hx]
    rfl

/-- The stalk functor with its actual module structure. -/
def moduleStalk (R : T.Sheaf CommRingCat.{u}) (x : T) :
    _root_.SheafOfModulesOfCommRing
      (C := Opens T) (J := Opens.grothendieckTopology T) R ⥤ ModuleCat.{u} (TopCat.Presheaf.stalk
        (C := CommRingCat.{u}) (X := T) R.obj x) where
  obj M := ModuleCat.of (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := T) R.obj x)
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := T) M.val.presheaf x)
  map p := ModuleCat.ofHom (moduleStalkMap x p)
  map_id M := by
    ext m
    exact ConcreteCategory.congr_hom ((stalkFunctor R x).map_id M) m
  map_comp p q := by
    ext m
    exact ConcreteCategory.congr_hom ((stalkFunctor R x).map_comp p q) m

instance stalkFunctor_additive (R : T.Sheaf CommRingCat.{u}) (x : T) :
    (stalkFunctor R x).Additive := by
  let := TopCat.instAdditivePresheafStalkFunctor (C := AddCommGrpCat.{u}) x
  change (SheafOfModules.forget.{u} ((sheafCompose (Opens.grothendieckTopology T)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
    _root_.PresheafOfModules.toPresheaf.{u}
    ((sheafCompose (Opens.grothendieckTopology T)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (X := T) x).Additive
  infer_instance

/-- Forgetting the module structure gives precisely the established abelian stalk. -/
def moduleStalkForgetIso (R : T.Sheaf CommRingCat.{u}) (x : T) :
    moduleStalk R x ⋙ forget₂ (ModuleCat (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := T)
      R.obj x)) AddCommGrpCat.{u} ≅
      stalkFunctor R x := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

instance moduleStalk_additive (R : T.Sheaf CommRingCat.{u}) (x : T) :
    (moduleStalk R x).Additive where
  map_add {M N} p q := by
    apply (forget₂ (ModuleCat (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := T) R.obj x))
      AddCommGrpCat.{u}).map_injective
    exact (stalkFunctor R x).map_add

instance stalkFunctor_preservesFiniteLimits (R : T.Sheaf CommRingCat.{u}) (x : T) :
    PreservesFiniteLimits (stalkFunctor R x) := by
  let := TopCat.Sheaf.instPreservesFiniteLimitsCompPresheafForgetStalkFunctor
    (C := AddCommGrpCat.{u}) x
  change PreservesFiniteLimits
    (SheafOfModules.toSheaf.{u} ((sheafCompose (Opens.grothendieckTopology T)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      (TopCat.Sheaf.forget AddCommGrpCat.{u} T ⋙ TopCat.Presheaf.stalkFunctor
        AddCommGrpCat.{u} (X := T) x))
  exact comp_preservesFiniteLimits
    (SheafOfModules.toSheaf.{u} ((sheafCompose (Opens.grothendieckTopology T)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (TopCat.Sheaf.forget AddCommGrpCat.{u} T ⋙ TopCat.Presheaf.stalkFunctor
      AddCommGrpCat.{u} (X := T) x)

instance moduleStalk_preservesFiniteLimits (R : T.Sheaf CommRingCat.{u}) (x : T) :
    PreservesFiniteLimits (moduleStalk R x) := by
  have := preservesFiniteLimits_of_natIso (moduleStalkForgetIso R x).symm
  exact preservesFiniteLimits_of_reflects_of_preserves (moduleStalk R x)
    (forget₂ (ModuleCat (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := T) R.obj x))
      AddCommGrpCat.{u})

/-- Actual module stalks detect monomorphisms of arbitrary module sheaves. -/
theorem mono_of_moduleStalk {R : T.Sheaf CommRingCat.{u}}
    {M N : _root_.SheafOfModulesOfCommRing
      (C := Opens T) (J := Opens.grothendieckTopology T) R} (p : M ⟶ N)
    (hp : ∀ x, Mono ((moduleStalk R x).map p)) : Mono p := by
  apply Preadditive.mono_of_isZero_kernel
  apply (isZero_iff_stalks _).mpr
  intro x
  have := hp x
  have hk : IsZero ((moduleStalk R x).obj (kernel p)) :=
    (isZero_kernel_of_mono ((moduleStalk R x).map p)).of_iso
      (PreservesKernel.iso (moduleStalk R x) p)
  exact ((forget₂ (ModuleCat (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := T) R.obj x))
    AddCommGrpCat.{u}).map_isZero hk).of_iso
    ((moduleStalkForgetIso R x).app (kernel p)).symm

/-- The skyscraper abelian presheaf, written as functions from open membership.
This presentation avoids choices of a zero object on opens missing the point. -/
abbrev pointPresheaf (R : T.Sheaf CommRingCat.{u}) (x : T) (N : ModuleCat.{u}
  (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := T) R.obj x)) :
    TopCat.Presheaf AddCommGrpCat.{u} T where
  obj U := AddCommGrpCat.of (PLift (x ∈ U.unop) → N)
  map {U V} i := AddCommGrpCat.ofHom
    { toFun := fun s hx => s ⟨i.unop.le hx.down⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

/-- Each skyscraper section is a module over the corresponding ring of sections. -/
instance instModulePointSection (R : T.Sheaf CommRingCat.{u}) (x : T)
    (N : ModuleCat.{u} (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := T) R.obj x)) (U : (Opens
      T)) :
    Module (R.obj.obj (op U)) (PLift (x ∈ U) → N) where
  smul r s hx := TopCat.Presheaf.germ (C := CommRingCat.{u}) (X := T) R.obj U x hx.down r • s hx
  one_smul s := by
    ext hx
    change TopCat.Presheaf.germ (C := CommRingCat.{u}) (X := T) R.obj U x hx.down 1 • s hx = s hx
    simp
  mul_smul r t s := by
    ext hx
    change TopCat.Presheaf.germ (C := CommRingCat.{u}) (X := T) R.obj U x hx.down (r * t) • s hx =
      TopCat.Presheaf.germ (C := CommRingCat.{u}) (X := T) R.obj U x hx.down r •
        (TopCat.Presheaf.germ (C := CommRingCat.{u}) (X := T) R.obj U x hx.down t • s hx)
    simp [mul_smul]
  smul_add r s t := by
    ext hx
    change TopCat.Presheaf.germ (C := CommRingCat.{u}) (X := T) R.obj U x hx.down r • (s hx + t hx)
      = _
    exact smul_add _ _ _
  smul_zero r := by
    ext hx
    change TopCat.Presheaf.germ (C := CommRingCat.{u}) (X := T) R.obj U x hx.down r • (0 : N) = 0
    exact smul_zero _
  add_smul r t s := by
    ext hx
    change TopCat.Presheaf.germ (C := CommRingCat.{u}) (X := T) R.obj U x hx.down (r + t) • s hx =
      TopCat.Presheaf.germ (C := CommRingCat.{u}) (X := T) R.obj U x hx.down r • s hx +
        TopCat.Presheaf.germ (C := CommRingCat.{u}) (X := T) R.obj U x hx.down t • s hx
    simp [add_smul]
  zero_smul s := by
    ext hx
    change TopCat.Presheaf.germ (C := CommRingCat.{u}) (X := T) R.obj U x hx.down 0 • s hx = 0
    simp

instance instModulePointPresheafObjRingSheaf (R : T.Sheaf CommRingCat.{u}) (x : T)
    (N : ModuleCat.{u} (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := T) R.obj x)) (U : (Opens
      T)ᵒᵖ) :
    Module (((sheafCompose (Opens.grothendieckTopology T)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj.obj U)
      ((pointPresheaf R x N).obj U) :=
  instModulePointSection R x N U.unop

instance instModulePointPresheafObjCommRingSheaf (R : T.Sheaf CommRingCat.{u}) (x : T)
    (N : ModuleCat.{u} (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := T) R.obj x)) (U : (Opens
      T)ᵒᵖ) :
    Module (R.obj.obj U) ((pointPresheaf R x N).obj U) :=
  instModulePointSection R x N U.unop

/-- Restriction of a skyscraper section is semilinear for the commutative ring sheaf. -/
theorem pointPresheaf_map_smul (R : T.Sheaf CommRingCat.{u}) (x : T)
    (N : ModuleCat.{u} (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := T) R.obj x)) {U V :
      (Opens T)ᵒᵖ} (i : U ⟶ V)
    (r : (R.obj.obj (op U.unop))) (s : (pointPresheaf R x N).obj U) :
    (pointPresheaf R x N).map i (r • s) =
      R.obj.map i r • (pointPresheaf R x N).map i s := by
  funext hx
  change TopCat.Presheaf.germ (C := CommRingCat.{u}) (X := T) R.obj U.unop x (i.unop.le hx.down) r
    • s ⟨i.unop.le hx.down⟩ =
    TopCat.Presheaf.germ (C := CommRingCat.{u}) (X := T) R.obj V.unop x hx.down (R.obj.map i r) • s
      ⟨i.unop.le hx.down⟩
  exact congrArg (fun a => a • s ⟨i.unop.le hx.down⟩)
    (TopCat.Presheaf.germ_res_apply (C := CommRingCat.{u}) (X := T) R.obj i.unop x hx.down r).symm

/-- The module skyscraper is an actual sheaf, with arbitrary stalk module. -/
theorem pointPresheaf_isSheaf (R : T.Sheaf CommRingCat.{u}) (x : T)
    (N : ModuleCat.{u} (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := T) R.obj x)) :
      (pointPresheaf R x N).IsSheaf := by
  classical
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro ι U sf hs
  let idx : x ∈ iSup U → ι := fun hx => Classical.choose (Opens.mem_iSup.mp hx)
  have hi : ∀ hx : x ∈ iSup U, x ∈ U (idx hx) :=
    fun hx => Classical.choose_spec (Opens.mem_iSup.mp hx)
  let s : PLift (x ∈ iSup U) → N := fun hx => sf (idx hx.down) ⟨hi hx.down⟩
  refine ⟨s, ?_, ?_⟩
  · intro i
    funext hx
    exact congrFun (hs (idx ((Opens.leSupr U i).le hx.down)) i)
      ⟨⟨hi ((Opens.leSupr U i).le hx.down), hx.down⟩⟩
  · intro t ht
    funext hx
    exact congrFun (ht (idx hx.down)) ⟨hi hx.down⟩

/-- The actual skyscraper sheaf of modules at a topological point. -/
abbrev moduleSkyscraperObj (R : T.Sheaf CommRingCat.{u}) (x : T)
    (N : ModuleCat.{u} (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := T) R.obj x)) :
      _root_.SheafOfModulesOfCommRing
      (C := Opens T) (J := Opens.grothendieckTopology T) R where
  val := _root_.PresheafOfModules.ofPresheaf
    (R := ((sheafCompose (Opens.grothendieckTopology T)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj) (pointPresheaf R x N)
    (fun {_ _} i r s => pointPresheaf_map_smul R x N i r s)
  isSheaf := pointPresheaf_isSheaf R x N

/-- Pointwise postcomposition makes the module skyscraper functorial. -/
def moduleSkyscraper (R : T.Sheaf CommRingCat.{u}) (x : T) :
    ModuleCat.{u} (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := T) R.obj x) ⥤
      _root_.SheafOfModulesOfCommRing
      (C := Opens T) (J := Opens.grothendieckTopology T) R where
  obj := moduleSkyscraperObj R x
  map p := ⟨_root_.PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun s hx => p (s hx)
          map_zero' := by funext hx; change p 0 = 0; exact p.hom.map_zero
          map_add' := by intros; funext hx; simp }
      naturality := by intros; ext s; funext hx; rfl }
    (by intro U r s; funext hx; exact p.hom.map_smul _ _)⟩
  map_id _ := by ext U s; funext hx; rfl
  map_comp _ _ := by ext U s; funext hx; rfl

/-- A linear map from the actual module stalk gives a morphism to the skyscraper. -/
def moduleStalkToSkyscraper {R : T.Sheaf CommRingCat.{u}} (x : T) (M :
  _root_.SheafOfModulesOfCommRing
      (C := Opens T) (J := Opens.grothendieckTopology T) R)
    (N : ModuleCat.{u} (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := T) R.obj x)) (p :
      (moduleStalk R x).obj M ⟶ N) :
    M ⟶ (moduleSkyscraper R x).obj N :=
  ⟨_root_.PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun s hx => p (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := T)
          M.val.presheaf U.unop x hx.down s)
          map_zero' := by
            funext hx
            change p (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := T) M.val.presheaf U.unop
              x hx.down 0) = 0
            simp
          map_add' := by intros; funext hx; simp; rfl }
      naturality := by
        intro U V i
        ext s
        funext hx
        change p (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := T) M.val.presheaf V.unop x
          hx.down (M.val.presheaf.map i s)) =
          p (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := T) M.val.presheaf U.unop x
            (i.unop.le hx.down) s)
        exact congrArg (fun m => p m) (TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) (X
          := T) M.val.presheaf i.unop x hx.down s) }
    (by
      intro U r s
      funext hx
      change p (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := T) M.val.presheaf U.unop x
        hx.down (r • s)) =
        TopCat.Presheaf.germ (C := CommRingCat.{u}) (X := T) R.obj U.unop x hx.down r • p
          (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := T) M.val.presheaf U.unop x hx.down s)
      erw [_root_.PresheafOfModules.germ_smul M.val x U.unop hx.down]
      exact p.hom.map_smul _ _)⟩

/-- The cocone of evaluations of a morphism to a module skyscraper. -/
def moduleSkyscraperCocone {R : T.Sheaf CommRingCat.{u}} (x : T) (M :
  _root_.SheafOfModulesOfCommRing
      (C := Opens T) (J := Opens.grothendieckTopology T) R)
    (N : ModuleCat.{u} (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := T) R.obj x)) (p : M ⟶
      (moduleSkyscraper R x).obj N) :
    Cocone ((OpenNhds.inclusion x).op ⋙ M.val.presheaf) where
  pt := (forget₂ (ModuleCat (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := T) R.obj x))
    AddCommGrpCat.{u}).obj N
  ι.app U := AddCommGrpCat.ofHom
    { toFun := fun s => p.val.app (op U.unop.1) s ⟨U.unop.2⟩
      map_zero' := by rw [map_zero]; rfl
      map_add' := by intros; rw [map_add]; rfl }
  ι.naturality U V i := by
    ext s
    exact congrFun (_root_.PresheafOfModules.naturality_apply p.val
      ((OpenNhds.inclusion x).op.map i) s) ⟨V.unop.2⟩

/-- Evaluation of the cocone map on an actual germ. -/
theorem germ_moduleSkyscraperCocone_desc {R : T.Sheaf CommRingCat.{u}} (x : T) (M :
  _root_.SheafOfModulesOfCommRing
      (C := Opens T) (J := Opens.grothendieckTopology T) R)
    (N : ModuleCat.{u} (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := T) R.obj x)) (p : M ⟶
      (moduleSkyscraper R x).obj N)
    (U : (Opens T)) (hx : x ∈ U) (s : (M.val.obj (op U))) :
    colimit.desc _ (moduleSkyscraperCocone x M N p) (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
      (X := T) M.val.presheaf U x hx s) =
      p.val.app (op U) s ⟨hx⟩ :=
  ConcreteCategory.congr_hom (colimit.ι_desc (moduleSkyscraperCocone x M N p)
    (op ⟨U, hx⟩)) s

/-- A morphism to a module skyscraper induces a linear map from the actual stalk. -/
def moduleSkyscraperFromStalk {R : T.Sheaf CommRingCat.{u}} (x : T) (M :
  _root_.SheafOfModulesOfCommRing
      (C := Opens T) (J := Opens.grothendieckTopology T) R)
    (N : ModuleCat.{u} (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := T) R.obj x)) (p : M ⟶
      (moduleSkyscraper R x).obj N) :
    (moduleStalk R x).obj M ⟶ N := ModuleCat.ofHom
  { toFun := colimit.desc _ (moduleSkyscraperCocone x M N p)
    map_add' := map_add (colimit.desc _ (moduleSkyscraperCocone x M N p)).hom
    map_smul' := by
      intro r m
      obtain ⟨U, hx, a, s, rfl, rfl⟩ := exists_germ_smul_representatives R x M r m
      change colimit.desc _ (moduleSkyscraperCocone x M N p)
        (TopCat.Presheaf.germ (C := CommRingCat.{u}) (X := T) R.obj U x hx a • TopCat.Presheaf.germ
          (C := AddCommGrpCat.{u}) (X := T) M.val.presheaf U x hx s) = _
      erw [← _root_.PresheafOfModules.germ_smul M.val x U hx]
      erw [germ_moduleSkyscraperCocone_desc, germ_moduleSkyscraperCocone_desc]
      exact congrFun ((p.val.app (op U)).hom.map_smul a s) ⟨hx⟩ }

/-- Universal property of the module-valued stalk among module skyscrapers. -/
def moduleStalkSkyscraperHomEquiv (R : T.Sheaf CommRingCat.{u}) (x : T) (M :
  _root_.SheafOfModulesOfCommRing
      (C := Opens T) (J := Opens.grothendieckTopology T) R)
    (N : ModuleCat.{u} (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := T) R.obj x)) :
    ((moduleStalk R x).obj M ⟶ N) ≃ (M ⟶ (moduleSkyscraper R x).obj N) where
  toFun := moduleStalkToSkyscraper x M N
  invFun := moduleSkyscraperFromStalk x M N
  left_inv p := by
    ext m
    obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) (X := T)
      M.val.presheaf m
    exact germ_moduleSkyscraperCocone_desc x M N (moduleStalkToSkyscraper x M N p) U hx s
  right_inv p := by
    apply SheafOfModules.hom_ext
    apply _root_.PresheafOfModules.hom_ext
    intro U
    ext s
    funext hx
    exact germ_moduleSkyscraperCocone_desc x M N p U.unop hx.down s

/-- Naturality of the stalk/skyscraper universal property in the sheaf. -/
theorem moduleStalkToSkyscraper_naturality_left {R : T.Sheaf CommRingCat.{u}} (x : T)
    {M M' : _root_.SheafOfModulesOfCommRing
      (C := Opens T) (J := Opens.grothendieckTopology T) R} (f : M ⟶ M') (N : ModuleCat.{u}
        (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := T) R.obj x))
    (p : (moduleStalk R x).obj M' ⟶ N) :
    moduleStalkToSkyscraper x M N ((moduleStalk R x).map f ≫ p) =
      f ≫ moduleStalkToSkyscraper x M' N p := by
  have h_germ (U : Opens T) (hx : x ∈ U) (s : M.val.obj (op U)) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply
      (C := AddCommGrpCat.{u}) (X := T)
      (F := M.val.presheaf) (G := M'.val.presheaf) U x hx
      ((_root_.PresheafOfModules.toPresheaf
        ((sheafCompose (Opens.grothendieckTopology T)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj).map f.val) s
  apply SheafOfModules.hom_ext
  apply _root_.PresheafOfModules.hom_ext
  intro U
  ext s
  funext hx
  exact congrArg (fun m : TopCat.Presheaf.stalk
      (C := AddCommGrpCat.{u}) (X := T) M'.val.presheaf x => p m)
    (h_germ U.unop hx.down s)

/-- The actual module stalk functor is left adjoint to the actual module skyscraper. -/
def moduleStalkSkyscraperAdjunction (R : T.Sheaf CommRingCat.{u}) (x : T) :
    moduleStalk R x ⊣ moduleSkyscraper R x := Adjunction.mkOfHomEquiv
  { homEquiv := moduleStalkSkyscraperHomEquiv R x
    homEquiv_naturality_left_symm := by
      intro M M' N f p
      apply (moduleStalkSkyscraperHomEquiv R x M N).injective
      rw [Equiv.apply_symm_apply]
      change _ = moduleStalkToSkyscraper x M N _
      rw [moduleStalkToSkyscraper_naturality_left]
      exact congrArg (fun q => f ≫ q) ((moduleStalkSkyscraperHomEquiv R x M' N).apply_symm_apply
        p).symm
    homEquiv_naturality_right := by
      intros
      ext U s
      funext hx
      rfl }

instance moduleStalk_isLeftAdjoint (R : T.Sheaf CommRingCat.{u}) (x : T) :
    (moduleStalk R x).IsLeftAdjoint := (moduleStalkSkyscraperAdjunction R x).isLeftAdjoint

/-- Module stalks are exact on arbitrary module sheaves. -/
def moduleStalkExactFunctor (R : T.Sheaf CommRingCat.{u}) (x : T) :
    ExactFunctor (abelianExactStructure (_root_.SheafOfModulesOfCommRing
      (C := Opens T) (J := Opens.grothendieckTopology T) R))
      (abelianExactStructure (ModuleCat.{u} (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := T)
        R.obj x))) where
  toFunctor := moduleStalk R x
  map_conflation _ h := h.map_of_exact _

end SheafOfModulesOfCommRing
