/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Support
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
/-!
# Module-valued stalks for arbitrary scheme module sheaves

These constructions retain the actual underlying abelian-group stalks and
endow them with the structure-sheaf stalk action. No quasicoherence hypothesis
is used. The module-valued functor is exact and jointly detects monomorphisms.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CategoryTheory.ExactCategory

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

/-- A simultaneous representative of a stalk scalar and a module-stalk element. -/
theorem exists_germ_smul_representatives (X : Scheme.{u}) (x : X)
    (M : X.Modules) (r : X.presheaf.stalk x) (m : M.presheaf.stalk x) :
    ∃ (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) (s : Γ(M, U)),
      X.presheaf.germ U x hx a = r ∧ M.presheaf.germ U x hx s = m := by
  obtain ⟨V, hxV, a, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨U, hUV, hxU, s, rfl⟩ := M.presheaf.exists_le_germ_eq m hxV
  exact ⟨U, hxU, X.presheaf.map (homOfLE hUV).op a, s,
    X.presheaf.germ_res_apply _ _ _ _, rfl⟩

instance instModuleSchemeModuleStalk (X : Scheme.{u}) (x : X) (M : X.Modules) :
    Module (X.presheaf.stalk x) (M.presheaf.stalk x) := by
  exact inferInstanceAs (Module (X.presheaf.stalk x)
    ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := (X : TopCat.{u})) M.val.presheaf x))

/-- The actual induced map on stalks is linear over the structure-sheaf stalk. -/
def moduleStalkMap {X : Scheme.{u}} (x : X) {M N : X.Modules} (p : M ⟶ N) :
    M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N.presheaf.stalk x where
  toFun := (stalkFunctor X x).map p
  map_add' := map_add ((stalkFunctor X x).map p).hom
  map_smul' r m := by
    obtain ⟨U, hx, a, s, rfl, rfl⟩ := exists_germ_smul_representatives X x M r m
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (X := (X : TopCat.{u})) x).map
      p.mapPresheaf
      (X.presheaf.germ U x hx a • M.presheaf.germ U x hx s) = _
    erw [← _root_.PresheafOfModules.germ_smul M.val x U hx,
      TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change N.presheaf.germ U x hx (p.app U (a • s)) = _
    erw [p.app_smul, _root_.PresheafOfModules.germ_smul N.val x U hx]
    rfl

/-- The stalk functor with its actual module structure. -/
def moduleStalk (X : Scheme.{u}) (x : X) : X.Modules ⥤ ModuleCat.{u} (X.presheaf.stalk x) where
  obj M := ModuleCat.of (X.presheaf.stalk x) (M.presheaf.stalk x)
  map p := ModuleCat.ofHom (moduleStalkMap x p)
  map_id M := by
    ext m
    exact ConcreteCategory.congr_hom ((stalkFunctor X x).map_id M) m
  map_comp p q := by
    ext m
    exact ConcreteCategory.congr_hom ((stalkFunctor X x).map_comp p q) m

instance stalkFunctor_additive (X : Scheme.{u}) (x : X) : (stalkFunctor X x).Additive := by
  let := TopCat.instAdditivePresheafStalkFunctor (C := AddCommGrpCat.{u}) x
  change (SheafOfModules.forget.{u} X.ringCatSheaf ⋙ _root_.PresheafOfModules.toPresheaf.{u}
    X.ringCatSheaf.obj ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (X := (X : TopCat.{u})) x).Additive
  infer_instance

/-- Forgetting the module structure gives precisely the established abelian stalk. -/
def moduleStalkForgetIso (X : Scheme.{u}) (x : X) :
    moduleStalk X x ⋙ forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat.{u} ≅
      stalkFunctor X x := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

instance moduleStalk_additive (X : Scheme.{u}) (x : X) : (moduleStalk X x).Additive where
  map_add {M N} p q := by
    apply (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat.{u}).map_injective
    exact (stalkFunctor X x).map_add

instance stalkFunctor_preservesFiniteLimits (X : Scheme.{u}) (x : X) :
    PreservesFiniteLimits (stalkFunctor X x) := by
  let := TopCat.Sheaf.instPreservesFiniteLimitsCompPresheafForgetStalkFunctor
    (C := AddCommGrpCat.{u}) x
  change PreservesFiniteLimits
    (SheafOfModules.toSheaf.{u} X.ringCatSheaf ⋙
      (TopCat.Sheaf.forget AddCommGrpCat.{u} (X : TopCat.{u}) ⋙ TopCat.Presheaf.stalkFunctor
        AddCommGrpCat.{u} (X := (X : TopCat.{u})) x))
  exact comp_preservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf)
    (TopCat.Sheaf.forget AddCommGrpCat.{u} (X : TopCat.{u}) ⋙ TopCat.Presheaf.stalkFunctor
      AddCommGrpCat.{u} (X := (X : TopCat.{u})) x)

instance moduleStalk_preservesFiniteLimits (X : Scheme.{u}) (x : X) :
    PreservesFiniteLimits (moduleStalk X x) := by
  have := preservesFiniteLimits_of_natIso (moduleStalkForgetIso X x).symm
  exact preservesFiniteLimits_of_reflects_of_preserves (moduleStalk X x)
    (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat.{u})

/-- Actual module stalks detect monomorphisms of arbitrary module sheaves. -/
theorem mono_of_moduleStalk {X : Scheme.{u}} {M N : X.Modules} (p : M ⟶ N)
    (hp : ∀ x, Mono ((moduleStalk X x).map p)) : Mono p := by
  apply Preadditive.mono_of_isZero_kernel
  apply (isZero_iff_stalks _).mpr
  intro x
  have := hp x
  have hk : IsZero ((moduleStalk X x).obj (kernel p)) :=
    (isZero_kernel_of_mono ((moduleStalk X x).map p)).of_iso
      (PreservesKernel.iso (moduleStalk X x) p)
  exact ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat.{u}).map_isZero hk).of_iso
    ((moduleStalkForgetIso X x).app (kernel p)).symm

/-- The skyscraper abelian presheaf, written as functions from open membership.
This presentation avoids choices of a zero object on opens missing the point. -/
abbrev pointPresheaf (X : Scheme.{u}) (x : X) (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    TopCat.Presheaf AddCommGrpCat.{u} (X : TopCat.{u}) where
  obj U := AddCommGrpCat.of (PLift (x ∈ U.unop) → N)
  map {U V} i := AddCommGrpCat.ofHom
    { toFun := fun s hx => s ⟨i.unop.le hx.down⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

/-- Each skyscraper section is a module over the corresponding ring of sections. -/
instance instModulePointSection (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opens) :
    Module Γ(X, U) (PLift (x ∈ U) → N) where
  smul r s hx := X.presheaf.germ U x hx.down r • s hx
  one_smul s := by
    ext hx
    change X.presheaf.germ U x hx.down 1 • s hx = s hx
    simp
  mul_smul r t s := by
    ext hx
    change X.presheaf.germ U x hx.down (r * t) • s hx =
      X.presheaf.germ U x hx.down r • (X.presheaf.germ U x hx.down t • s hx)
    simp [mul_smul]
  smul_add r s t := by
    ext hx
    change X.presheaf.germ U x hx.down r • (s hx + t hx) = _
    exact smul_add _ _ _
  smul_zero r := by
    ext hx
    change X.presheaf.germ U x hx.down r • (0 : N) = 0
    exact smul_zero _
  add_smul r t s := by
    ext hx
    change X.presheaf.germ U x hx.down (r + t) • s hx =
      X.presheaf.germ U x hx.down r • s hx + X.presheaf.germ U x hx.down t • s hx
    simp [add_smul]
  zero_smul s := by
    ext hx
    change X.presheaf.germ U x hx.down 0 • s hx = 0
    simp

instance instModulePointPresheafObjRingSheaf (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) ((pointPresheaf X x N).obj U) :=
  instModulePointSection X x N U.unop

instance instModulePointPresheafObjStructureSheaf (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opensᵒᵖ) :
    Module (X.presheaf.obj U) ((pointPresheaf X x N).obj U) :=
  instModulePointSection X x N U.unop

/-- Restriction of a skyscraper section is semilinear for the structure sheaf. -/
theorem pointPresheaf_map_smul (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) {U V : X.Opensᵒᵖ} (i : U ⟶ V)
    (r : Γ(X, U.unop)) (s : (pointPresheaf X x N).obj U) :
    (pointPresheaf X x N).map i (r • s) =
      X.presheaf.map i r • (pointPresheaf X x N).map i s := by
  funext hx
  change X.presheaf.germ U.unop x (i.unop.le hx.down) r • s ⟨i.unop.le hx.down⟩ =
    X.presheaf.germ V.unop x hx.down (X.presheaf.map i r) • s ⟨i.unop.le hx.down⟩
  exact congrArg (fun a => a • s ⟨i.unop.le hx.down⟩)
    (X.presheaf.germ_res_apply i.unop x hx.down r).symm

/-- The module skyscraper is an actual sheaf, with arbitrary stalk module. -/
theorem pointPresheaf_isSheaf (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) : (pointPresheaf X x N).IsSheaf := by
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

/-- The actual skyscraper sheaf of modules at a scheme point. -/
abbrev moduleSkyscraperObj (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) : X.Modules where
  val := _root_.PresheafOfModules.ofPresheaf (R := X.ringCatSheaf.obj) (pointPresheaf X x N)
    (fun {_ _} i r s => pointPresheaf_map_smul X x N i r s)
  isSheaf := pointPresheaf_isSheaf X x N

/-- Pointwise postcomposition makes the module skyscraper functorial. -/
def moduleSkyscraper (X : Scheme.{u}) (x : X) :
    ModuleCat.{u} (X.presheaf.stalk x) ⥤ X.Modules where
  obj := moduleSkyscraperObj X x
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
def moduleStalkToSkyscraper {X : Scheme.{u}} (x : X) (M : X.Modules)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (p : (moduleStalk X x).obj M ⟶ N) :
    M ⟶ (moduleSkyscraper X x).obj N :=
  ⟨_root_.PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun s hx => p (M.presheaf.germ U.unop x hx.down s)
          map_zero' := by
            funext hx
            change p (M.presheaf.germ U.unop x hx.down 0) = 0
            simp
          map_add' := by intros; funext hx; simp; rfl }
      naturality := by
        intro U V i
        ext s
        funext hx
        change p (M.presheaf.germ V.unop x hx.down (M.presheaf.map i s)) =
          p (M.presheaf.germ U.unop x (i.unop.le hx.down) s)
        exact congrArg (fun m => p m) (M.presheaf.germ_res_apply i.unop x hx.down s) }
    (by
      intro U r s
      funext hx
      change p (M.presheaf.germ U.unop x hx.down (r • s)) =
        X.presheaf.germ U.unop x hx.down r • p (M.presheaf.germ U.unop x hx.down s)
      erw [_root_.PresheafOfModules.germ_smul M.val x U.unop hx.down]
      exact p.hom.map_smul _ _)⟩

/-- The cocone of evaluations of a morphism to a module skyscraper. -/
def moduleSkyscraperCocone {X : Scheme.{u}} (x : X) (M : X.Modules)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (p : M ⟶ (moduleSkyscraper X x).obj N) :
    Cocone ((OpenNhds.inclusion x).op ⋙ M.presheaf) where
  pt := (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat.{u}).obj N
  ι.app U := AddCommGrpCat.ofHom
    { toFun := fun s => p.app U.unop.1 s ⟨U.unop.2⟩
      map_zero' := by rw [map_zero]; rfl
      map_add' := by intros; rw [map_add]; rfl }
  ι.naturality U V i := by
    ext s
    exact congrFun (_root_.PresheafOfModules.naturality_apply p.val
      ((OpenNhds.inclusion x).op.map i) s) ⟨V.unop.2⟩

/-- Evaluation of the cocone map on an actual germ. -/
theorem germ_moduleSkyscraperCocone_desc {X : Scheme.{u}} (x : X) (M : X.Modules)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (p : M ⟶ (moduleSkyscraper X x).obj N)
    (U : X.Opens) (hx : x ∈ U) (s : Γ(M, U)) :
    colimit.desc _ (moduleSkyscraperCocone x M N p) (M.presheaf.germ U x hx s) =
      p.app U s ⟨hx⟩ :=
  ConcreteCategory.congr_hom (colimit.ι_desc (moduleSkyscraperCocone x M N p)
    (op ⟨U, hx⟩)) s

/-- A morphism to a module skyscraper induces a linear map from the actual stalk. -/
def moduleSkyscraperFromStalk {X : Scheme.{u}} (x : X) (M : X.Modules)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (p : M ⟶ (moduleSkyscraper X x).obj N) :
    (moduleStalk X x).obj M ⟶ N := ModuleCat.ofHom
  { toFun := colimit.desc _ (moduleSkyscraperCocone x M N p)
    map_add' := map_add (colimit.desc _ (moduleSkyscraperCocone x M N p)).hom
    map_smul' := by
      intro r m
      obtain ⟨U, hx, a, s, rfl, rfl⟩ := exists_germ_smul_representatives X x M r m
      change colimit.desc _ (moduleSkyscraperCocone x M N p)
        (X.presheaf.germ U x hx a • M.presheaf.germ U x hx s) = _
      erw [← _root_.PresheafOfModules.germ_smul M.val x U hx]
      erw [germ_moduleSkyscraperCocone_desc, germ_moduleSkyscraperCocone_desc]
      exact congrFun (p.app_smul a s) ⟨hx⟩ }

/-- Universal property of the module-valued stalk among module skyscrapers. -/
def moduleStalkSkyscraperHomEquiv (X : Scheme.{u}) (x : X) (M : X.Modules)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    ((moduleStalk X x).obj M ⟶ N) ≃ (M ⟶ (moduleSkyscraper X x).obj N) where
  toFun := moduleStalkToSkyscraper x M N
  invFun := moduleSkyscraperFromStalk x M N
  left_inv p := by
    ext m
    obtain ⟨U, hx, s, rfl⟩ := M.presheaf.exists_germ_eq m
    exact germ_moduleSkyscraperCocone_desc x M N (moduleStalkToSkyscraper x M N p) U hx s
  right_inv p := by
    ext U s
    funext hx
    exact germ_moduleSkyscraperCocone_desc x M N p U hx.down s

/-- Naturality of the stalk/skyscraper universal property in the sheaf. -/
theorem moduleStalkToSkyscraper_naturality_left {X : Scheme.{u}} (x : X)
    {M M' : X.Modules} (f : M ⟶ M') (N : ModuleCat.{u} (X.presheaf.stalk x))
    (p : (moduleStalk X x).obj M' ⟶ N) :
    moduleStalkToSkyscraper x M N ((moduleStalk X x).map f ≫ p) =
      f ≫ moduleStalkToSkyscraper x M' N p := by
  ext U s
  funext hx
  change p ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
      (X := (X : TopCat.{u})) x).map f.mapPresheaf (M.presheaf.germ U x hx.down s)) =
    p (M'.presheaf.germ U x hx.down (f.app U s))
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  rfl

/-- The actual module stalk functor is left adjoint to the actual module skyscraper. -/
def moduleStalkSkyscraperAdjunction (X : Scheme.{u}) (x : X) :
    moduleStalk X x ⊣ moduleSkyscraper X x := Adjunction.mkOfHomEquiv
  { homEquiv := moduleStalkSkyscraperHomEquiv X x
    homEquiv_naturality_left_symm := by
      intro M M' N f p
      apply (moduleStalkSkyscraperHomEquiv X x M N).injective
      rw [Equiv.apply_symm_apply]
      change _ = moduleStalkToSkyscraper x M N _
      rw [moduleStalkToSkyscraper_naturality_left]
      exact congrArg (fun q => f ≫ q) ((moduleStalkSkyscraperHomEquiv X x M' N).apply_symm_apply
        p).symm
    homEquiv_naturality_right := by
      intros
      ext U s
      funext hx
      rfl }

instance moduleStalk_isLeftAdjoint (X : Scheme.{u}) (x : X) :
    (moduleStalk X x).IsLeftAdjoint := (moduleStalkSkyscraperAdjunction X x).isLeftAdjoint

/-- Module stalks are exact on arbitrary module sheaves. -/
def moduleStalkExactFunctor (X : Scheme.{u}) (x : X) :
    ExactFunctor (sheafExactStructure X)
      (abelianExactStructure (ModuleCat.{u} (X.presheaf.stalk x))) where
  toFunctor := moduleStalk X x
  map_conflation _ h := h.map_of_exact _

end AlgebraicGeometry.Scheme.Modules
