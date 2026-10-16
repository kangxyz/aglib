/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.AlgebraicGeometry.Modules.Linear
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineOpenSections

/-!
# Actual annihilation on subopens of an affine open

A global-section annihilator of a quasicoherent module on an affine scheme
annihilates the original sections on every subopen. The proof identifies
the original scalar-center endomorphism with zero through the native
tilde/global-section counit. Transport along the actual affine chart keeps
the original restriction and section-ring action. No finiteness or
Noetherian hypothesis is used, and the subopen need not be affine.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- An annihilator of the original affine global sections makes the
original scalar-center endomorphism zero on the entire module sheaf. -/
theorem globalScalarEndomorphism_eq_zero_of_mem_annihilator_specΓ
    {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent] (a : R)
    (ha : a ∈ Module.annihilator R (moduleSpecΓFunctor.obj M)) :
    globalScalarEndomorphism (Spec R) M ((Scheme.ΓSpecIso R).inv a) = 0 := by
  let q := globalScalarEndomorphism (Spec R) M ((Scheme.ΓSpecIso R).inv a)
  have hq : moduleSpecΓFunctor.map q = 0 := by
    ext m
    change (globalScalarEndomorphism (Spec R) M ((Scheme.ΓSpecIso R).inv a)).val.app
      (op ⊤) m = 0
    rw [globalScalarEndomorphism_app]
    exact (Module.mem_annihilator.mp ha) m
  apply (cancel_epi M.fromTildeΓ).mp
  have hn := (fromTildeΓNatTrans (R := R)).naturality q
  change (tilde.functor R).map (moduleSpecΓFunctor.map q) ≫ M.fromTildeΓ =
    M.fromTildeΓ ≫ q at hn
  rw [hq, Functor.map_zero, zero_comp] at hn
  simpa only [comp_zero] using hn.symm

/-- An affine global-section annihilator kills sections on an arbitrary
actual subopen, with the native structural action of the affine ring. -/
theorem smul_eq_zero_of_mem_annihilator_specΓ {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] (a : R)
    (ha : a ∈ Module.annihilator R (moduleSpecΓFunctor.obj M))
    (W : (Spec R).Opens) (m : Γ(M, W)) : a • m = 0 := by
  have h := congrArg (fun q : M ⟶ M => q.val.app (op W) m)
    (globalScalarEndomorphism_eq_zero_of_mem_annihilator_specΓ M a ha)
  rw [globalScalarEndomorphism_app] at h
  exact h

open QuasiCoherent.AffineOpenSections

/-- An annihilator on an actual affine open still annihilates every actual
subopen after restriction of the original scalar. The subopen is arbitrary. -/
theorem smul_restriction_eq_zero_of_mem_annihilator_affineSections
    {X : Scheme.{u}} (M : X.Modules) {V W : X.Opens} (hV : IsAffineOpen V)
    [(M.restrict hV.fromSpec).IsQuasicoherent] (hWV : W ≤ V) (a : Γ(X, V))
    (ha : a ∈ Module.annihilator Γ(X, V) Γ(M, V)) (m : Γ(M, W)) :
    X.presheaf.map (homOfLE hWV).op a • m = 0 := by
  let N := M.restrict hV.fromSpec
  let e := toSpecTopSectionsLinearEquiv M hV
  have ha' : a ∈ Module.annihilator Γ(X, V) (moduleSpecΓFunctor.obj N) :=
    e.toLinearMap.annihilator_le_of_surjective e.surjective ha
  apply (restrictionUnitIso M hV hWV).addCommGroupIsoToAddEquiv.injective
  change (restrictionUnitIso M hV hWV).hom
      (X.presheaf.map (homOfLE hWV).op a • m) = (restrictionUnitIso M hV hWV).hom 0
  rw [restrictionUnit_smul, map_zero]
  exact smul_eq_zero_of_mem_annihilator_specΓ N a ha' (hV.fromSpec ⁻¹ᵁ W)
    ((restrictionUnitIso M hV hWV).hom m)

/-- Original scalar restriction maps the affine section annihilator into
the annihilator of sections on every subopen. -/
theorem map_annihilator_affineSections_le {X : Scheme.{u}} (M : X.Modules)
    {V W : X.Opens} (hV : IsAffineOpen V)
    [(M.restrict hV.fromSpec).IsQuasicoherent] (hWV : W ≤ V) :
    (Module.annihilator Γ(X, V) Γ(M, V)).map
        (X.presheaf.map (homOfLE hWV).op).hom ≤
      Module.annihilator Γ(X, W) Γ(M, W) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  change X.presheaf.map (homOfLE hWV).op a ∈ Module.annihilator Γ(X, W) Γ(M, W)
  rw [Module.mem_annihilator]
  intro m
  exact smul_restriction_eq_zero_of_mem_annihilator_affineSections M hV hWV a ha m

end AlgebraicGeometry.Scheme.Modules
