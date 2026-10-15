/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.FlatMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/PushforwardModuleStalk.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 134]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Actual module stalks of geometric pushforward

The canonical pushforward stalk map is linear over the original target stalk
ring, with scalar restriction along the original geometric stalk map.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology Opposite

open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- The original pushforward stalk map, with its actual scalar restriction. -/
def pushforwardModuleStalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (M : X.Modules) :
    (moduleStalk Y (f x)).obj ((Scheme.Modules.pushforward f).obj M) ⟶
      (ModuleCat.restrictScalars (f.stalkMap x).hom).obj ((moduleStalk X x).obj M) :=
  ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (f.stalkMap x).hom).obj ((moduleStalk X x).obj M))
    { toFun := M.presheaf.stalkPushforward AddCommGrpCat f.base x
      map_add' := map_add (M.presheaf.stalkPushforward AddCommGrpCat f.base x).hom
      map_smul' := by
        intro r m
        obtain ⟨U, hx, a, s, rfl, rfl⟩ := exists_germ_smul_representatives Y (f x)
          ((Scheme.Modules.pushforward f).obj M) r m
        change M.presheaf.stalkPushforward AddCommGrpCat f.base x
          (Y.presheaf.germ U (f x) hx a •
            ((Scheme.Modules.pushforward f).obj M).presheaf.germ U (f x) hx s) =
          f.stalkMap x (Y.presheaf.germ U (f x) hx a) •
            M.presheaf.stalkPushforward AddCommGrpCat f.base x
              (((Scheme.Modules.pushforward f).obj M).presheaf.germ U (f x) hx s)
        erw [← PresheafOfModules.germ_smul ((Scheme.Modules.pushforward f).obj M).val
          (f x) U hx]
        erw [TopCat.Presheaf.stalkPushforward_germ_apply,
          TopCat.Presheaf.stalkPushforward_germ_apply]
        change M.presheaf.germ (f ⁻¹ᵁ U) x hx (f.app U a • (show Γ(M, f ⁻¹ᵁ U) from s)) = _
        erw [PresheafOfModules.germ_smul M.val x (f ⁻¹ᵁ U) hx]
        rw [f.germ_stalkMap_apply]
        rfl }

/-- The comparison sends an original pushforward germ to the same section germ. -/
theorem pushforwardModuleStalkMap_germ {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (M : X.Modules) (U : Y.Opens) (hx : f x ∈ U) (s : Γ(M, f ⁻¹ᵁ U)) :
    pushforwardModuleStalkMap f x M
      (((Scheme.Modules.pushforward f).obj M).presheaf.germ U (f x) hx s) =
      M.presheaf.germ (f ⁻¹ᵁ U) x hx s := by
  exact TopCat.Presheaf.stalkPushforward_germ_apply AddCommGrpCat f.base M.presheaf U x hx s

/-- The canonical map commutes with every original coefficient morphism. -/
theorem pushforwardModuleStalkMap_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    {M N : X.Modules} (p : M ⟶ N) :
    (moduleStalk Y (f x)).map ((Scheme.Modules.pushforward f).map p) ≫
        pushforwardModuleStalkMap f x N =
      pushforwardModuleStalkMap f x M ≫
        (ModuleCat.restrictScalars (f.stalkMap x).hom).map ((moduleStalk X x).map p) := by
  ext m
  obtain ⟨U, hx, s, rfl⟩ := ((Scheme.Modules.pushforward f).obj M).presheaf.exists_germ_eq m
  change pushforwardModuleStalkMap f x N
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (f x)).map
      ((Scheme.Modules.pushforward f).map p).mapPresheaf
      (((Scheme.Modules.pushforward f).obj M).presheaf.germ U (f x) hx s)) =
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map p.mapPresheaf
      (pushforwardModuleStalkMap f x M
        (((Scheme.Modules.pushforward f).obj M).presheaf.germ U (f x) hx s))
  rw [pushforwardModuleStalkMap_germ]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    TopCat.Presheaf.stalkFunctor_map_germ_apply]
  exact pushforwardModuleStalkMap_germ f x N U hx (p.app (f ⁻¹ᵁ U) s)

/-- The comparison is invertible for every inducing scheme map. -/
theorem pushforwardModuleStalkMap_isIso_of_isInducing {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hf : IsInducing f) (x : X) (M : X.Modules) :
    IsIso (pushforwardModuleStalkMap f x M) := by
  let := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
    AddCommGrpCat (f := f.base) hf M.presheaf x
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact (ConcreteCategory.isIso_iff_bijective
    (M.presheaf.stalkPushforward AddCommGrpCat f.base x)).mp inferInstance

/-- Native module stalks of pushforward along an inducing map, naturally in the sheaf. -/
def pushforwardModuleStalkIso {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsInducing f) (x : X) :
    Scheme.Modules.pushforward f ⋙ moduleStalk Y (f x) ≅
      moduleStalk X x ⋙ ModuleCat.restrictScalars (f.stalkMap x).hom := by
  letI (M : X.Modules) := pushforwardModuleStalkMap_isIso_of_isInducing f hf x M
  exact NatIso.ofComponents (fun M => asIso (pushforwardModuleStalkMap f x M))
    (fun p => pushforwardModuleStalkMap_naturality f x p)

/-- A closed immersion has the same scalar-compatible comparison without extra hypotheses. -/
def closedImmersionModuleStalkIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] (x : X) :
    Scheme.Modules.pushforward f ⋙ moduleStalk Y (f x) ≅
      moduleStalk X x ⋙ ModuleCat.restrictScalars (f.stalkMap x).hom :=
  pushforwardModuleStalkIso f f.isClosedEmbedding.isInducing x

/-- Every pushforward stalk off a closed image vanishes, for arbitrary module sheaves. -/
theorem isZero_pushforward_moduleStalk_of_not_mem {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsClosed (Set.range f)) (y : Y) (hy : y ∉ Set.range f) (M : X.Modules) :
    IsZero ((moduleStalk Y y).obj ((Scheme.Modules.pushforward f).obj M)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  ext m
  let U : Y.Opens := ⟨(Set.range f)ᶜ, hf.isOpen_compl⟩
  obtain ⟨V, hVU, hyV, s, rfl⟩ :=
    ((Scheme.Modules.pushforward f).obj M).presheaf.exists_le_germ_eq m (show y ∈ U from hy)
  have hV : f ⁻¹ᵁ V = ⊥ := by
    apply bot_unique
    intro z hz
    exact (hVU hz) ⟨z, rfl⟩
  have ht : IsTerminal (M.presheaf.obj (op (f ⁻¹ᵁ V))) :=
    TopCat.Sheaf.isTerminalOfEqEmpty ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) hV
  have hs : s = 0 := ConcreteCategory.congr_hom (ht.hom_ext (𝟙 _) 0) s
  change ((Scheme.Modules.pushforward f).obj M).presheaf.germ V y hyV s = 0
  rw [hs, map_zero]

/-- The off-image vanishing needed for the original diagonal pushforward. -/
theorem isZero_closedImmersion_moduleStalk_of_not_mem {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] (y : Y) (hy : y ∉ Set.range f) (M : X.Modules) :
    IsZero ((moduleStalk Y y).obj ((Scheme.Modules.pushforward f).obj M)) :=
  isZero_pushforward_moduleStalk_of_not_mem f f.isClosedEmbedding.isClosed_range y hy M

end AlgebraicGeometry.Scheme.Modules
