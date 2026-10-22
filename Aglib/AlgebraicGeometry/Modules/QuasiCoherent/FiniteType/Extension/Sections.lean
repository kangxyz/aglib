/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Extension.Global
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Morphisms

/-!
# Finite-type subsheaves capturing prescribed affine sections

Every section of a quasicoherent sheaf on an affine open of a quasi-compact quasi-separated
scheme belongs to a global finite-type subsheaf. The section lies in the range of the actual
inclusion, so the result can be used to prove equality of ideal sheaves rather than equality
of their supports.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

/-- A finite submodule realizes a finite-type subsheaf, with its actual global-section map. -/
theorem exists_finiteType_subsheaf_section_spec (R : CommRingCat.{u})
    (M : (Spec R).Modules) [M.IsQuasicoherent] (x : moduleSpecΓFunctor.obj M) :
    ∃ (N : FiniteTypeSheaves (Spec R)) (i : N.obj ⟶ M), Mono i ∧
      ∃ y : moduleSpecΓFunctor.obj N.obj, (moduleSpecΓFunctor.map i) y = x := by
  let P := moduleSpecΓFunctor.obj M
  let : Module R P := P.isModule
  let L : Submodule R P := Submodule.span R {x}
  have hL : L.FG := Submodule.fg_span_singleton x
  have : Module.Finite R L := Module.Finite.of_fg hL
  let N : FiniteTypeSheaves (Spec R) :=
    ⟨tilde (ModuleCat.of R L), (affineLocallyFiniteType_spec_iff R _).mpr
      ⟨inferInstance, Module.Finite.equiv (tilde.isoTop (ModuleCat.of R L)).toLinearEquiv⟩⟩
  let a : ModuleCat.of R L ⟶ P := ModuleCat.ofHom (Y := P) L.subtype
  have : Mono a := (ModuleCat.mono_iff_injective a).mpr (by
    intro x y h
    exact Subtype.ext h)
  have : Mono (tilde.map a) := (tilde.functor R).map_mono a
  have : IsIso M.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent M
  let i : N.obj ⟶ M := tilde.map a ≫ M.fromTildeΓ
  have hi : Mono i := by dsimp [i]; infer_instance
  let z : L := ⟨x, Submodule.subset_span (by simp)⟩
  have he : (tilde.adjunction (R := R)).unit.app (ModuleCat.of R L) ≫
      moduleSpecΓFunctor.map i = a := by
    apply ((tilde.adjunction (R := R)).unit_comp_map_eq_iff i a).mpr
    rfl
  refine ⟨N, i, hi, (tilde.adjunction (R := R)).unit.app (ModuleCat.of R L) z, ?_⟩
  exact ConcreteCategory.congr_hom he z

/-- On a quasi-compact quasi-separated scheme, every section on an affine chart is contained
in a global finite-type subsheaf through the actual inclusion map. -/
theorem exists_finiteType_subsheaf_section
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (M : X.Modules) [M.IsQuasicoherent] (U : X.affineOpens) (x : Γ(M, U)) :
    ∃ (N : FiniteTypeSheaves X) (i : N.obj ⟶ M), Mono i ∧
      ∃ y : Γ(N.obj, U), i.app U.val y = x := by
  let j := U.property.fromSpec
  let x' := (affineChartΓIso U M).inv x
  obtain ⟨A, a, ha, y, hy⟩ :=
    exists_finiteType_subsheaf_section_spec Γ(X, U) (M.restrict j) x'
  have : Mono a := ha
  obtain ⟨N, i, hi, e, he⟩ :=
    affineLocallyFiniteType_subobject_extension_of_qcqs j M A a
  let z := moduleSpecΓFunctor.map e.inv y
  have hz : moduleSpecΓFunctor.map ((restrictFunctor j).map i) z = x' := by
    rw [he, Functor.map_comp]
    change moduleSpecΓFunctor.map a
      (moduleSpecΓFunctor.map e.hom (moduleSpecΓFunctor.map e.inv y)) = x'
    have hcancel : moduleSpecΓFunctor.map e.hom
        (moduleSpecΓFunctor.map e.inv y) = y :=
      (moduleSpecΓFunctor.mapIso e).inv_hom_id_apply y
    exact (congrArg (moduleSpecΓFunctor.map a) hcancel).trans hy
  refine ⟨N, i, hi, (affineChartΓIso U N.obj).hom z, ?_⟩
  have hn := ConcreteCategory.congr_hom (affineChartΓIso_naturality U i) z
  change (affineChartΓIso U M).hom
      (moduleSpecΓFunctor.map ((restrictFunctor j).map i) z) =
    i.app U.val ((affineChartΓIso U N.obj).hom z) at hn
  rw [hz] at hn
  exact hn.symm.trans ((affineChartΓIso U M).inv_hom_id_apply x)

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
