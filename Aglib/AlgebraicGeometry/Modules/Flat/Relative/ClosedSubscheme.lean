/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.QuotientModule
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.OfSections
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.Unit
public import Aglib.AlgebraicGeometry.Modules.Pushforward.Stalk
public import Aglib.RingTheory.Flat.Exact
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Relative flatness of the structure module and the ideal of a closed subscheme

For a closed subscheme `W ⊆ X` with closed immersion `i = W.subschemeι` and `p : X ⟶ S`:

* `Scheme.Modules.pushforwardUnitStalkIso`: the stalk of `i_* 𝒪_W` at `i z`, over the base local
  ring, is `𝒪_{W,z}` with `𝒪_{S, p(i z)}` acting through `(i ≫ p).stalkMap z`; off `i(W)` the
  stalks vanish. Hence `i_* 𝒪_W` is relatively flat over `S` if and only if `i ≫ p` is flat
  (`relativeFlat_pushforward_unit_of_flat`, `flat_comp_of_relativeFlat_pushforward_unit`).
* `Scheme.IdealSheafData.relativeFlat_quotientModule_iff_flat`: through `𝒪_X / I_W ≅ i_* 𝒪_W`,
  the structure module `𝒪_X / I_W` is relatively flat over `S` if and only if `W ⟶ X ⟶ S` is
  flat. This is the "flat over `T`" of the Hilbert functor, Mathlib's `Flat` of `W ⟶ T`.
* `Scheme.IdealSheafData.relativeFlat_pullback_quotientModule_iff`: for any `f : Y ⟶ X` and
  `p : Y ⟶ S`, `f^* 𝒪_W` is relatively flat over `S` if and only if `W.comap f ⟶ Y ⟶ S` is flat
  (`quotientModulePullbackIso`, no flatness of `W`).
* `Scheme.Modules.relativeFlat_idealModule_of_flat`: over an affine base, for flat `p` and `W`
  flat over the base with quasi-coherent ideal module, the ideal module `I_W` is relatively flat:
  on an affine open `U`, `Γ(U, I_W)` is the kernel of the surjection `Γ(X, U) ⟶ Γ(W, W ∩ U)` of
  flat modules.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry

namespace Scheme.Modules

/-- The stalk of `i_* 𝒪_W` at `i z`, over the base local ring of `p : X ⟶ S`, is the local ring
`𝒪_{W,z}` with `𝒪_{S, p(i z)}` acting through `p.stalkMap (i z) ≫ i.stalkMap z`
(`closedImmersionModuleStalkIso`, `unitStalkIso`). -/
def pushforwardUnitStalkIso {X W S : Scheme.{u}} (p : X ⟶ S) (i : W ⟶ X) [IsClosedImmersion i]
    (z : W) :
    (ModuleCat.restrictScalars (p.stalkMap (i z)).hom).obj
      ((moduleStalk X (i z)).obj ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit W.ringCatSheaf))) ≅
      (ModuleCat.restrictScalars (p.stalkMap (i z) ≫ i.stalkMap z).hom).obj
        (ModuleCat.of (W.presheaf.stalk z) (W.presheaf.stalk z)) :=
  have : Subsingleton (ULift.{u} (PLift (z ∈ (⊤ : W.Opens)))) :=
    ⟨fun a b => by
      obtain ⟨⟨_⟩⟩ := a
      obtain ⟨⟨_⟩⟩ := b
      rfl⟩
  (ModuleCat.restrictScalars (p.stalkMap (i z)).hom).mapIso
      ((closedImmersionModuleStalkIso i z).app (SheafOfModules.unit W.ringCatSheaf) ≪≫
        (ModuleCat.restrictScalars (i.stalkMap z).hom).mapIso
          (unitStalkIso W z ≪≫ (Finsupp.uniqueLinearEquiv _ _
            (⟨⟨trivial⟩⟩ : ULift.{u} (PLift (z ∈ (⊤ : W.Opens))))).toModuleIso)) ≪≫
    (ModuleCat.restrictScalarsComp'App (p.stalkMap (i z)).hom (i.stalkMap z).hom
      (p.stalkMap (i z) ≫ i.stalkMap z).hom rfl _).symm

/-- **The pushforward of the structure sheaf of a flat closed subscheme is relatively flat**: for
a closed immersion `i : W ⟶ X` and `p : X ⟶ S` with `i ≫ p` flat, `i_* 𝒪_W` is relatively flat
over `S`. Its stalks vanish off `i(W)` and are the local rings `𝒪_{W,z}` at the points `i z`. -/
theorem relativeFlat_pushforward_unit_of_flat {X W S : Scheme.{u}} (p : X ⟶ S) (i : W ⟶ X)
    [IsClosedImmersion i] [Flat (i ≫ p)] :
    relativeFlat p ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit W.ringCatSheaf)) := by
  intro y
  by_cases hy : y ∈ Set.range i
  · obtain ⟨z, rfl⟩ := hy
    have hφ : (p.stalkMap (i z) ≫ i.stalkMap z).hom.Flat := by
      have h := Flat.stalkMap (i ≫ p) z
      rwa [Scheme.Hom.stalkMap_comp] at h
    have hφ' : Module.Flat (S.presheaf.stalk (p (i z)))
        ((ModuleCat.restrictScalars (p.stalkMap (i z) ≫ i.stalkMap z).hom).obj
          (ModuleCat.of (W.presheaf.stalk z) (W.presheaf.stalk z))) := hφ
    exact Module.Flat.of_linearEquiv (pushforwardUnitStalkIso p i z).toLinearEquiv
  · have hz := isZero_closedImmersion_moduleStalk_of_not_mem i y hy
      (SheafOfModules.unit W.ringCatSheaf)
    have : Subsingleton ((ModuleCat.restrictScalars (p.stalkMap y).hom).obj
        ((moduleStalk X y).obj ((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit W.ringCatSheaf)))) :=
      ModuleCat.subsingleton_of_isZero
        ((ModuleCat.restrictScalars (p.stalkMap y).hom).map_isZero hz)
    infer_instance

/-- **Flatness of a closed subscheme from relative flatness of its structure sheaf**: for a closed
immersion `i : W ⟶ X` and `p : X ⟶ S`, if `i_* 𝒪_W` is relatively flat over `S`, then `i ≫ p` is
flat. -/
theorem flat_comp_of_relativeFlat_pushforward_unit {X W S : Scheme.{u}} (p : X ⟶ S) (i : W ⟶ X)
    [IsClosedImmersion i]
    (h : relativeFlat p ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit W.ringCatSheaf))) :
    Flat (i ≫ p) := by
  rw [Flat.iff_flat_stalkMap]
  intro z
  have hz := h (i z)
  have hflat := Module.Flat.of_linearEquiv (pushforwardUnitStalkIso p i z).symm.toLinearEquiv
  rw [Scheme.Hom.stalkMap_comp]
  exact hflat

/-- **The ideal module of a closed subscheme flat over an affine base is relatively flat**: for a
flat `p : X ⟶ Spec R` and a closed subscheme `Z ⊆ X` flat over `Spec R` whose ideal module is
quasicoherent, the ideal module is relatively flat over `Spec R`. On an affine open `U`,
`Γ(U, I_Z)` is the kernel of the surjection `Γ(X, U) ⟶ Γ(Z, Z ∩ U)` of flat `R`-modules. -/
theorem relativeFlat_idealModule_of_flat {X : Scheme.{u}} {R : CommRingCat.{u}} (p : X ⟶ Spec R)
    [Flat p] (Z : X.IdealSheafData) [Flat (Z.subschemeι ≫ p)]
    [(Scheme.Hom.idealModule Z.subschemeι).IsQuasicoherent] :
    relativeFlat p (Scheme.Hom.idealModule Z.subschemeι) := by
  rw [relativeFlat_iff_flat_affineOpen_sections]
  intro U hU
  let i := Z.subschemeι
  let φ : R ⟶ Γ(X, U) := (Scheme.ΓSpecIso R).inv ≫ p.appLE ⊤ U (by simp)
  have hφ : φ.hom.Flat := by
    have h := HasRingHomProperty.appLE @Flat p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩
      (by simp)
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv)) h
  have hU' : IsAffineOpen (i ⁻¹ᵁ U) := hU.preimage i
  have hψ : (φ ≫ i.app U).hom.Flat := by
    have h := HasRingHomProperty.appLE @Flat (i ≫ p) inferInstance ⟨⊤, isAffineOpen_top _⟩
      ⟨i ⁻¹ᵁ U, hU'⟩ (by simp)
    have heq : φ ≫ i.app U = (Scheme.ΓSpecIso R).inv ≫ (i ≫ p).appLE ⊤ (i ⁻¹ᵁ U) (by simp) :=
      congrArg ((Scheme.ΓSpecIso R).inv ≫ ·)
        ((congrArg (p.appLE ⊤ U (by simp) ≫ ·) (Scheme.Hom.app_eq_appLE i)).trans
          (Scheme.Hom.appLE_comp_appLE i p ⊤ U (i ⁻¹ᵁ U) _ _))
    rw [heq]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv)) h
  algebraize [φ.hom, (φ ≫ i.app U).hom]
  have hsurj : Function.Surjective (i.app U) := Scheme.Hom.app_surjective i U hU
  let χ : Γ(X, U) →ₐ[R] Γ(Z.subscheme, i ⁻¹ᵁ U) :=
    { (i.app U).hom with commutes' := fun _ => rfl }
  have hker : Module.Flat R (LinearMap.ker χ.toLinearMap) :=
    Module.Flat.ker_of_surjective χ.toLinearMap hsurj
  let e₃ : LinearMap.ker χ.toLinearMap ≃ₗ[R] (ModuleCat.restrictScalars φ.hom).obj
      (ModuleCat.of Γ(X, U) (RingHom.ker (i.app U).hom)) :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hker' : Module.Flat R ((ModuleCat.restrictScalars φ.hom).obj
      (ModuleCat.of Γ(X, U) (RingHom.ker (i.app U).hom))) :=
    Module.Flat.of_linearEquiv e₃.symm
  exact Module.Flat.of_linearEquiv ((ModuleCat.restrictScalars φ.hom).mapIso
    (Scheme.Hom.idealSectionsEquiv i U).toModuleIso).toLinearEquiv

end Scheme.Modules

namespace Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- **The structure module of a flat closed subscheme is relatively flat**: for `p : X ⟶ S` and a
closed subscheme `W` flat over `S`, `𝒪_X / I_W` is relatively flat over `S`. -/
theorem relativeFlat_quotientModule_of_flat {S : Scheme.{u}} (p : X ⟶ S) (W : X.IdealSheafData)
    [Flat (W.subschemeι ≫ p)] : relativeFlat p W.quotientModule :=
  relativeFlat_of_iso p W.quotientModuleIsoPushforward
    (relativeFlat_pushforward_unit_of_flat p W.subschemeι)

/-- **A closed subscheme is flat when its structure module is relatively flat**: for
`p : X ⟶ S`, relative flatness of `𝒪_X / I_W` over `S` makes `W ⟶ X ⟶ S` flat. -/
theorem flat_of_relativeFlat_quotientModule {S : Scheme.{u}} (p : X ⟶ S) (W : X.IdealSheafData)
    (h : relativeFlat p W.quotientModule) : Flat (W.subschemeι ≫ p) :=
  Scheme.Modules.flat_comp_of_relativeFlat_pushforward_unit p W.subschemeι
    (relativeFlat_of_iso p W.quotientModuleIsoPushforward.symm h)

/-- **Flatness of a closed subscheme is relative flatness of its structure module.** -/
theorem relativeFlat_quotientModule_iff_flat {S : Scheme.{u}} (p : X ⟶ S)
    (W : X.IdealSheafData) : relativeFlat p W.quotientModule ↔ Flat (W.subschemeι ≫ p) :=
  ⟨W.flat_of_relativeFlat_quotientModule p, fun _ => W.relativeFlat_quotientModule_of_flat p⟩

variable {Y : Scheme.{u}}

/-- **Flatness of the pulled-back structure module is flatness of the pulled-back subscheme**:
for `f : Y ⟶ X`, a closed subscheme `W ⊆ X` and `p : Y ⟶ S`, `f^* 𝒪_W` is relatively flat over
`S` if and only if `W.comap f ⟶ Y ⟶ S` is flat. -/
theorem relativeFlat_pullback_quotientModule_iff {S : Scheme.{u}} (p : Y ⟶ S)
    (W : X.IdealSheafData) (f : Y ⟶ X) :
    relativeFlat p ((Scheme.Modules.pullback f).obj W.quotientModule) ↔
      Flat ((W.comap f).subschemeι ≫ p) := by
  rw [← relativeFlat_quotientModule_iff_flat]
  exact ⟨relativeFlat_of_iso p (W.quotientModulePullbackIso f).symm,
    relativeFlat_of_iso p (W.quotientModulePullbackIso f)⟩

end Scheme.IdealSheafData

end AlgebraicGeometry
