/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Flat.Generic.Spec
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.AffineSections

/-!
# Relative flatness from flat affine sections

For `f : X ⟶ Spec A` and a quasicoherent `𝒪_X`-module `M`, relative flatness of `M` over `A`
(`Scheme.Modules.relativeFlat f M`) holds as soon as every point has an affine open neighbourhood
`U` with `Γ(U, M)` flat over `A`; conversely relative flatness makes every `Γ(U, M)` flat
(`flat_affineOpen_sections_of_relativeFlat`). This is the last step of the proof of Nitsure,
*Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, Lemma 3.2, p. 15 ("As the `U_i`
form an open cover of `P^n_S`, it follows that `F` is flat over `𝒪_S`").

* `relativeFlat_specMap_of_flat`: on `Spec B ⟶ Spec A`, flat global sections give relative
  flatness;
* `relativeFlat_of_flat_affineOpen_sections`: the local criterion on an affine open cover;
* `relativeFlat_iff_flat_affineOpen_sections`: relative flatness over an affine base is flatness of
  all affine sections.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- On `Spec B ⟶ Spec A`, flatness of the global sections of a quasicoherent module over `A` gives
relative flatness. -/
theorem relativeFlat_specMap_of_flat {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (N : (Spec B).Modules) [N.IsQuasicoherent]
    (hN : Module.Flat A ((ModuleCat.restrictScalars φ.hom).obj (moduleSpecΓFunctor.obj N))) :
    relativeFlat (Spec.map φ) N := by
  intro y
  have hy : φ.hom 1 ∉ y.asIdeal := by
    rw [map_one]
    exact (Ideal.ne_top_iff_one _).mp y.isPrime.ne_top
  exact flat_stalk_specMap_of_flat_localizedModule_away φ N 1 y hy

/-- **Relative flatness from flat affine sections** (Stacks Project, Tag 01U4 (Lemma 29.26.2),
(4) ⇒ (1)): if every point of `X` has an affine open neighbourhood `U` such that `Γ(U, M)` is
flat over `A` (through the structure morphism), then `M` is relatively flat over `Spec A`. -/
theorem relativeFlat_of_flat_affineOpen_sections {X : Scheme.{u}} {A : CommRingCat.{u}}
    (f : X ⟶ Spec A) (M : X.Modules) [M.IsQuasicoherent]
    (H : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      Module.Flat A ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso A).inv ≫
        f.appLE ⊤ U (by simp)).hom).obj (ModuleCat.of Γ(X, U) Γ(M, U)))) :
    relativeFlat f M := by
  intro x
  obtain ⟨U, hU, hxU, hflat⟩ := H x
  let φ : A ⟶ Γ(X, U) := (Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U (by simp)
  let N := M.restrict hU.fromSpec
  let : N.IsQuasicoherent := isQuasicoherent_restrictFunctor hU.fromSpec M
  let e := (ModuleCat.restrictScalars φ.hom).mapIso
    (QuasiCoherent.AffineOpenSections.toSpecTopSectionsLinearEquiv M hU).toModuleIso
  have hN : relativeFlat (Spec.map φ) N :=
    relativeFlat_specMap_of_flat φ N ((Module.Flat.equiv_iff e.toLinearEquiv).mp hflat)
  rw [show Spec.map φ = hU.fromSpec ≫ f from SpecMap_affineOpen_baseRingHom f hU] at hN
  obtain ⟨y, rfl⟩ : x ∈ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact hxU
  exact flat_stalk_of_flat_stalk_restrict hU.fromSpec f M y (hN y)

/-- **Relative flatness over an affine base is flatness of all affine sections** (Stacks Project,
Tag 01U4 (Lemma 29.26.2), (1) ⇔ (2) with `V = Spec A`). -/
theorem relativeFlat_iff_flat_affineOpen_sections {X : Scheme.{u}} {A : CommRingCat.{u}}
    (f : X ⟶ Spec A) (M : X.Modules) [M.IsQuasicoherent] :
    relativeFlat f M ↔ ∀ U : X.Opens, IsAffineOpen U →
      Module.Flat A ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso A).inv ≫
        f.appLE ⊤ U (by simp)).hom).obj (ModuleCat.of Γ(X, U) Γ(M, U))) := by
  refine ⟨fun hM U hU => flat_affineOpen_sections_of_relativeFlat f M hM hU, fun H => ?_⟩
  refine relativeFlat_of_flat_affineOpen_sections f M fun x => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨U, hU, hxU, H U hU⟩

end AlgebraicGeometry.Scheme.Modules
