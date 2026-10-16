/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.AllAffine
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Composition
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Pullback

/-! # Canonical affine module base change

For an affine morphism and arbitrary quasicoherent coefficients, the original
`moduleBaseChangeMap` is invertible after every change of base. The proof uses
the actual affine section/scalar comparison and the original open base-change
and composition maps. No flatness or finiteness assumption is imposed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {X S T : Scheme.{u}}

/-- Canonical affine module base change, for arbitrary quasicoherent coefficients
and arbitrary changes of base. -/
theorem moduleBaseChangeMap_isIso (f : X ⟶ S) (g : T ⟶ S) (M : X.Modules)
    [IsAffineHom f] [M.IsQuasicoherent] : IsIso (moduleBaseChangeMap f g M) := by
  rw [moduleBaseChangeMap_eq_cartesianBaseChangeMap]
  let p := Limits.pullback.fst f g
  let q := Limits.pullback.snd f g
  let h := IsPullback.of_hasPullback f g
  change IsIso ((cartesianBaseChangeMap p q f g h).app M)
  apply Pullback.OpenRestriction.isIso_of_local_restrict
    ((cartesianBaseChangeMap p q f g h).app M)
  intro t
  obtain ⟨U, hUaff, hgt, -⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top (g t))
  obtain ⟨V, hVaff, ht, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (show t ∈ g ⁻¹ᵁ U from hgt)
  refine ⟨V, ht, ?_⟩
  let : IsAffine U.toScheme := hUaff
  let : IsAffine V.toScheme := hVaff
  let r := g.resLE U V hVU
  have hr : r ≫ U.ι = V.ι ≫ g := Scheme.Hom.resLE_comp_ι g hVU
  let a := Limits.pullback.fst f U.ι
  let b := Limits.pullback.snd f U.ι
  let hU := IsPullback.of_hasPullback f U.ι
  let c := Limits.pullback.fst q V.ι
  let d := Limits.pullback.snd q V.ι
  let hV := IsPullback.of_hasPullback q V.ι
  let H := hV.paste_horiz h
  have HU : IsPullback (c ≫ p) d f (r ≫ U.ι) := by
    simpa only [hr] using H
  let e := hU.lift (c ≫ p) (d ≫ r) (by simpa only [Category.assoc] using HU.w)
  have he : e ≫ a = c ≫ p := hU.lift_fst _ _ _
  have hlocal : IsPullback e d b r := HU.of_right' hU
  let Hlocal := hlocal.paste_horiz hU
  let : IsAffineHom q := MorphismProperty.pullback_snd _ _ ‹IsAffineHom f›
  let : IsAffineHom b := inferInstanceAs (IsAffineHom (Limits.pullback.snd f U.ι))
  let : IsAffineHom d := inferInstanceAs (IsAffineHom (Limits.pullback.snd q V.ι))
  let : IsAffine (Limits.pullback f U.ι) := isAffine_of_isAffineHom b
  let : IsAffine (Limits.pullback q V.ι) := isAffine_of_isAffineHom d
  let : IsIso ((cartesianBaseChangeMap a b f U.ι hU).app M) :=
    isIso_cartesianBaseChangeMap_of_isOpenImmersion a b f U.ι hU M
  let : IsIso ((cartesianBaseChangeMap e d b r hlocal).app ((pullback a).obj M)) :=
    cartesianBaseChangeMap_isIso_of_isAffine e d b r hlocal ((pullback a).obj M)
  have hcomp := cartesianBaseChangeMap_comp a b f U.ι hU e d r hlocal Hlocal M
  have houter : IsIso ((cartesianBaseChangeMap (e ≫ a) d f (r ≫ U.ι) Hlocal).app M) := by
    have : IsIso ((pullbackComp r U.ι).hom.app ((pushforward f).obj M) ≫
        (cartesianBaseChangeMap (e ≫ a) d f (r ≫ U.ι) Hlocal).app M) := by
      rw [hcomp]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((pullbackComp r U.ι).hom.app ((pushforward f).obj M)) _
  have htransport (a₁ a₂ : Limits.pullback q V.ι ⟶ X) (g₁ g₂ : V.toScheme ⟶ S)
      (ha : a₁ = a₂) (hg : g₁ = g₂)
      (H₁ : IsPullback a₁ d f g₁) (H₂ : IsPullback a₂ d f g₂) :
      IsIso ((cartesianBaseChangeMap a₁ d f g₁ H₁).app M) ↔
        IsIso ((cartesianBaseChangeMap a₂ d f g₂ H₂).app M) := by
    subst a₂
    subst g₂
    rfl
  have houter' : IsIso ((cartesianBaseChangeMap (c ≫ p) d f (V.ι ≫ g) H).app M) := by
    exact (htransport (e ≫ a) (c ≫ p) (r ≫ U.ι) (V.ι ≫ g) he hr Hlocal H).mp houter
  let : IsIso ((cartesianBaseChangeMap c d q V.ι hV).app ((pullback p).obj M)) :=
    isIso_cartesianBaseChangeMap_of_isOpenImmersion c d q V.ι hV ((pullback p).obj M)
  have hcomp' := cartesianBaseChangeMap_comp p q f g h c d V.ι hV H M
  have : IsIso ((pullback V.ι).map ((cartesianBaseChangeMap p q f g h).app M) ≫
      (cartesianBaseChangeMap c d q V.ι hV).app ((pullback p).obj M) ≫
      (pushforward d).map ((pullbackComp c p).hom.app M)) := by
    rw [← hcomp']
    infer_instance
  have : IsIso ((pullback V.ι).map ((cartesianBaseChangeMap p q f g h).app M) ≫
      (cartesianBaseChangeMap c d q V.ι hV).app ((pullback p).obj M)) :=
    IsIso.of_isIso_comp_right _ ((pushforward d).map ((pullbackComp c p).hom.app M))
  have hp : IsIso ((pullback V.ι).map ((cartesianBaseChangeMap p q f g h).app M)) :=
    IsIso.of_isIso_comp_right _
      ((cartesianBaseChangeMap c d q V.ι hV).app ((pullback p).obj M))
  exact (NatIso.isIso_map_iff (restrictFunctorIsoPullback V.ι)
    ((cartesianBaseChangeMap p q f g h).app M)).mpr hp

/-- The full canonical affine module base-change theorem family, with no additional input. -/
theorem affineModuleBaseChange : AffineModuleBaseChange.{u} := by
  intro X S T f g M hf hM
  let := hf
  let := hM
  exact moduleBaseChangeMap_isIso f g M

end AlgebraicGeometry.Scheme.Modules
