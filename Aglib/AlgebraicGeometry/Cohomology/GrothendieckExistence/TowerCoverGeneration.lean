/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.NilpotentGeneration
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Exactness
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineOpenSections
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness

/-! # Nilpotent generation tested on an affine cover -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent.AffineOpenSections

namespace AlgebraicGeometry.Scheme.Modules

universe u v
variable {X : Scheme.{u}} {J : Type v}
  (U : J → X.affineOpens) (hU : ∀ x : X, ∃ j, x ∈ (U j).val)

include hU in
/-- Original section surjectivity on a jointly covering family of affine
opens detects an epimorphism between quasicoherent coefficients. -/
theorem epi_of_affineCoverSections_surjective
    {P M : X.Modules} [P.IsQuasicoherent] [M.IsQuasicoherent]
    (p : P ⟶ M) (hp : ∀ j, Function.Surjective (p.app (U j).val)) : Epi p := by
  let Y (j : J) := Spec Γ(X, (U j).val)
  let a (j : J) : Y j ⟶ X := (U j).property.fromSpec
  have hc : ∀ x : X, ∃ (j : J) (y : Y j), a j y = x := by
    intro x
    obtain ⟨j, hj⟩ := hU x
    have hx : x ∈ Set.range (a j) := by
      change x ∈ Set.range (U j).property.fromSpec
      rwa [(U j).property.range_fromSpec]
    obtain ⟨y, hy⟩ := hx
    exact ⟨j, y, hy⟩
  have he (j : J) : Epi ((restrictFunctor (a j)).map p) := by
    let p' := (restrictFunctor (a j)).map p
    let : Epi (moduleSpecΓFunctor.map p') := by
      apply (ModuleCat.epi_iff_surjective _).mpr
      intro y
      obtain ⟨x, hx⟩ := hp j ((toSpecTopSectionsIso M (U j).property).inv y)
      refine ⟨(toSpecTopSectionsIso P (U j).property).hom x, ?_⟩
      have h := ConcreteCategory.congr_hom
        (toSpecTopSectionsIso_naturality P p (U j).property) x
      change (toSpecTopSectionsIso M (U j).property).hom (p.app (U j).val x) =
        p'.app ⊤ ((toSpecTopSectionsIso P (U j).property).hom x) at h
      rw [hx, Iso.inv_hom_id_apply] at h
      exact h.symm
    exact epi_of_epi_globalSections _ p'
  apply Preadditive.epi_of_isZero_cokernel
  apply isZero_of_restrict_openCover Y a hc
  intro j
  let := he j
  exact (isZero_cokernel_of_epi ((restrictFunctor (a j)).map p)).of_iso
    (PreservesCokernel.iso (restrictFunctor (a j)) p)

include hU in
/-- For an annihilated tower it suffices to bound reduction kernels on a
fixed affine cover. This avoids replacing a finite chartwise bound by an
unnecessary all-affine localization statement. -/
theorem compatible_epi_of_affineCover_kernel_bound
    (K : X.IdealSheafData) {P : X.Modules} [hP : P.IsQuasicoherent]
    (F : ℕᵒᵖ ⥤ X.Modules) (hF : ∀ n : ℕ, (F.obj (op n)).IsQuasicoherent)
    (p : (Functor.const ℕᵒᵖ).obj P ⟶ F) (k : ℕ) [Epi (p.app (op k))]
    (hepi : ∀ n m (h : n ≤ m), Epi (F.map (homOfLE h).op))
    (hkilled : ∀ n : ℕ, killedByIdealSheaf (K ^ n) (F.obj (op n)))
    (hker : ∀ n (h : k ≤ n) (j : J),
      LinearMap.ker ((F.map (homOfLE h).op).val.app (op (U j).val)).hom ≤
        K.ideal (U j) • (⊤ : Submodule Γ(X, (U j).val) Γ(F.obj (op n), (U j).val)))
    (n : ℕ) : Epi (p.app (op n)) := by
  rcases le_total k n with h | h
  · let : (((Functor.const ℕᵒᵖ).obj P).obj (op n)).IsQuasicoherent := hP
    let := hF k
    let := hF n
    have hc : p.app (op n) ≫ F.map (homOfLE h).op = p.app (op k) := by
      have hn := p.naturality (homOfLE h).op
      change 𝟙 P ≫ p.app (op k) = p.app (op n) ≫ F.map (homOfLE h).op at hn
      exact ((Category.id_comp _).symm.trans hn).symm
    let : Epi (p.app (op n) ≫ F.map (homOfLE h).op) := by rw [hc]; infer_instance
    let : (kernel (p.app (op n) ≫ F.map (homOfLE h).op)).IsQuasicoherent :=
      quasicoherent_kernel _
    apply epi_of_affineCoverSections_surjective U hU
    intro j
    have hnil : (K.ideal (U j)) ^ n •
        (⊤ : Submodule Γ(X, (U j).val) Γ(F.obj (op n), (U j).val)) = ⊥ := by
      apply le_bot_iff.mp
      apply Submodule.smul_le.mpr
      intro a ha x _
      exact hkilled n (U j) a ha x
    exact LinearMap.surjective_of_surjective_comp_of_ker_le_smul (K.ideal (U j))
      ((p.app (op n)).val.app (op (U j).val)).hom
      ((F.map (homOfLE h).op).val.app (op (U j).val)).hom
      (affineOpenSections_epi_surjective (U j) (p.app (op n) ≫ F.map (homOfLE h).op))
      (hker n h j) n hnil
  · let := hepi n k h
    have hc : p.app (op n) = p.app (op k) ≫ F.map (homOfLE h).op := by
      have hn := p.naturality (homOfLE h).op
      change 𝟙 P ≫ p.app (op n) = p.app (op k) ≫ F.map (homOfLE h).op at hn
      exact (Category.id_comp _).symm.trans hn
    rw [hc]
    infer_instance

end AlgebraicGeometry.Scheme.Modules
