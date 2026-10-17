/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Spec
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit

/-!
# Degree-zero structure-sheaf base change on global functions

For a commutative square `p ≫ f = q ≫ Spec.map σ` with `f : X ⟶ Spec R` and
`q : Y ⟶ Spec B`, the original degree-zero cohomology tensor map of the actual
structure module, followed by `Sheaf.H.equiv₀` and the original pullback-unit
comparison `pullbackUnitIso p`, sends `b ⊗ x` to `β b * p.appTop x`. Here `β` is the
structural map of `q` and `x` is read through `Sheaf.H.equiv₀` as a global function
on `X`. No flatness, quasicoherence or properness is assumed.

The statements concern only degree zero; their intended owner is the module
base-change family `Cohomology/BaseChange/Modules`.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y : Scheme.{u}}

/-- Degree-zero cohomology of the actual structure module, read as global functions. -/
def unitSections (X : Scheme.{u}) :
    Sheaf.H.{u + 1} (moduleAddSheaf X (SheafOfModules.unit X.ringCatSheaf)) 0 ≃+ Γ(X, ⊤) :=
  Sheaf.H.equiv₀ (moduleAddSheaf X (SheafOfModules.unit X.ringCatSheaf)) isTerminalTop

/-- Degree-zero cohomology of the pulled-back structure module, read as global functions
through `Sheaf.H.equiv₀` and the original pullback-unit comparison. -/
def pullbackUnitSections (p : Y ⟶ X) :
    Sheaf.H.{u + 1} (moduleAddSheaf Y
      ((Scheme.Modules.pullback p).obj (SheafOfModules.unit X.ringCatSheaf))) 0 →+
        Γ(Y, ⊤) :=
  ((Scheme.Modules.pullbackUnitIso p).hom.app ⊤).hom.comp
    (Sheaf.H.equiv₀ (moduleAddSheaf Y ((Scheme.Modules.pullback p).obj
      (SheafOfModules.unit X.ringCatSheaf))) isTerminalTop).toAddMonoidHom

theorem pullbackUnitSections_bijective (p : Y ⟶ X) :
    Function.Bijective (pullbackUnitSections p) := by
  have h1 := (Sheaf.H.equiv₀ (moduleAddSheaf Y ((Scheme.Modules.pullback p).obj
    (SheafOfModules.unit X.ringCatSheaf))) isTerminalTop).bijective
  have h2 : Function.Bijective ((Scheme.Modules.pullbackUnitIso p).hom.app ⊤) :=
    ConcreteCategory.bijective_of_isIso _
  exact h2.comp h1

/-- The direct-image section comparison is the identity on elements. -/
theorem pushforwardSectionsIso_hom_app_apply (p : Y ⟶ X)
    (F : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (y : F.obj.obj (op ((Opens.map p.base).obj ⊤))) :
    (pushforwardSectionsIso p).hom.app F y = y := by
  simp [pushforwardSectionsIso]

/-- Multiplication by a global function commutes with `pullbackUnitSections`. -/
theorem pullbackUnitSections_scalar (p : Y ⟶ X) (a : Γ(Y, ⊤))
    (z : Sheaf.H.{u + 1} (moduleAddSheaf Y
      ((Scheme.Modules.pullback p).obj (SheafOfModules.unit X.ringCatSheaf))) 0) :
    pullbackUnitSections p (Sheaf.H.map (moduleScalarOfGlobal Y
        ((Scheme.Modules.pullback p).obj (SheafOfModules.unit X.ringCatSheaf)) a) 0 z) =
      a * pullbackUnitSections p z := by
  let N : Y.Modules := (Scheme.Modules.pullback p).obj (SheafOfModules.unit X.ringCatSheaf)
  change ((Scheme.Modules.pullbackUnitIso p).hom.app ⊤)
      (Sheaf.H.equiv₀ (moduleAddSheaf Y N) isTerminalTop
        (Sheaf.H.map (moduleScalarOfGlobal Y N a) 0 z)) = _
  rw [← Sheaf.H.equiv₀_naturality]
  change ((Scheme.Modules.pullbackUnitIso p).hom.app ⊤)
      (show Γ(N, ⊤) from globalRestriction Y ⊤ a •
        (show Γ(N, ⊤) from Sheaf.H.equiv₀ (moduleAddSheaf Y N) isTerminalTop z)) = _
  rw [globalRestriction_top_apply, Scheme.Modules.Hom.app_smul]
  rfl

/-- The pulled-back degree-zero class of a global function is its actual pullback. -/
theorem pullbackUnitSections_moduleCohomologyPullback (p : Y ⟶ X)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X (SheafOfModules.unit X.ringCatSheaf)) 0) :
    pullbackUnitSections p
        (moduleCohomologyPullback p (SheafOfModules.unit X.ringCatSheaf) 0 x) =
      p.appTop (unitSections X x) := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have hu := Scheme.Modules.pullbackUnitIso_homEquiv p
  rw [Adjunction.homEquiv_unit] at hu
  have hv := congrArg
    (fun z : O ⟶ (Scheme.Modules.pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf) =>
      Scheme.Modules.Hom.app z ⊤ (show Γ(O, ⊤) from unitSections X x)) hu
  simp only [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply] at hv
  change ((Scheme.Modules.pullbackUnitIso p).hom.app ⊤)
      (Sheaf.H.equiv₀ _ isTerminalTop
        (moduleCohomologyMapAlong p ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
          O) 0 x)) = _
  rw [moduleCohomologyMapAlong_equiv₀, pushforwardSectionsIso_hom_app_apply]
  exact hv

variable {R B : Type u} [CommRing R] [CommRing B]
  (p : Y ⟶ X) (q : Y ⟶ Spec (CommRingCat.of B)) (f : X ⟶ Spec (CommRingCat.of R))
  (σ : R →+* B) (w : p ≫ f = q ≫ Spec.map (CommRingCat.ofHom σ))

/-- The degree-zero structure-sheaf tensor map on global functions:
`b ⊗ x ↦ β b * p.appTop x`. -/
theorem pullbackUnitSections_moduleCohomologyTensorMap_tmul (b : B)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X (SheafOfModules.unit X.ringCatSheaf)) 0) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    let β := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
    let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let N : Y.Modules := (Scheme.Modules.pullback p).obj O
    let φp : O ⟶ (Scheme.Modules.pushforward p).obj N :=
      (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app O
    let := moduleCohomologyModuleOfHom X α O 0
    pullbackUnitSections p (moduleCohomologyTensorMap (M := O) (N := N) p σ α β
        (moduleSectionsBaseChangeScalars p q f σ w) φp 0 (b ⊗ₜ[R,σ] x)) =
      β b * p.appTop (unitSections X x) := by
  intro α β O N φp _
  let := moduleCohomologyModuleOfHom Y β N 0
  let T := moduleCohomologyTensorMap (M := O) (N := N) p σ α β
    (moduleSectionsBaseChangeScalars p q f σ w) φp 0
  have h1 : b ⊗ₜ[R,σ] x = b • ((1 : B) ⊗ₜ[R,σ] x) := by
    change b ⊗ₜ[R,σ] x = (b * 1) ⊗ₜ[R,σ] x
    rw [mul_one]
  have h2 : T (b ⊗ₜ[R,σ] x) = b • moduleCohomologyPullback p O 0 x := by
    rw [h1, map_smul]
    congr 1
    exact moduleCohomologyTensorMap_one_tmul p σ α β _ φp 0 x
  change pullbackUnitSections p (T (b ⊗ₜ[R,σ] x)) = _
  rw [h2]
  change pullbackUnitSections p (Sheaf.H.map (moduleScalarOfGlobal Y N (β b)) 0
    (moduleCohomologyPullback p O 0 x)) = _
  rw [pullbackUnitSections_scalar, pullbackUnitSections_moduleCohomologyPullback]

end AlgebraicGeometry.Scheme.Cohomology
