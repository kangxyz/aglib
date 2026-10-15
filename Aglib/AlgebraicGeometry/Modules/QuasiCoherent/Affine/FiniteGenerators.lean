/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeProperty
public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Basic
/-!
# Finite global generators on an affine scheme

For a quasicoherent sheaf on `Spec R`, a finite family of global generating
sections gives a finite module of global sections. The proof uses the actual
tilde equivalence: a sheaf epimorphism from a finite free sheaf pulls back to
an epimorphism of modules. Conversely, finite global sections give a finite
global generating family. These statements do not require noetherianity.

This concerns global generating families and global presentations. It does
not identify an arbitrary local finite-presentation witness with a global
finite presentation.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

variable (R : CommRingCat.{u})

/-- A quasicoherent sheaf on an affine scheme with finite global generators
has a finitely generated module of global sections. -/
theorem finite_globalSections_of_generatingSections (M : (Spec R).Modules)
    [M.IsQuasicoherent] (G : M.GeneratingSections) [G.IsFiniteType] :
    Module.Finite R (moduleSpecΓFunctor.obj M) := by
  have : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  have : Epi G.π := G.epi
  let e : tilde (moduleSpecΓFunctor.obj M) ≅ M := asIso M.fromTildeΓ
  let f : ModuleCat.of R (G.I →₀ R) ⟶ moduleSpecΓFunctor.obj M :=
    (tilde.functor R).preimage ((tildeFinsupp G.I).hom ≫ G.π ≫ e.inv)
  have hf : Epi ((tilde.functor R).map f) := by
    dsimp only [f]
    rw [Functor.map_preimage]
    infer_instance
  have : Epi f := (tilde.functor R).epi_of_epi_map hf
  exact Module.Finite.of_surjective f.hom ((ModuleCat.epi_iff_surjective f).mp inferInstance)

/-- An actual global presentation with finitely many generators suffices;
finiteness of the relation family is not needed for this conclusion. -/
theorem finite_globalSections_of_presentation {M : (Spec R).Modules}
    (P : M.Presentation) [P.generators.IsFiniteType] :
    Module.Finite R (moduleSpecΓFunctor.obj M) := by
  have : M.IsQuasicoherent := P.isQuasicoherent
  exact finite_globalSections_of_generatingSections R M P.generators

/-- A finite global presentation gives actual affine coherence without a
noetherianity hypothesis. -/
theorem affineFiniteSheaf_of_presentation {M : (Spec R).Modules}
    (P : M.Presentation) [P.generators.IsFiniteType] : affineFiniteSheaf R M :=
  ⟨P.isQuasicoherent, finite_globalSections_of_presentation R P⟩

/-- Finite global sections of a quasicoherent affine sheaf provide an actual
finite global generating family. No finite-relations hypothesis is needed. -/
theorem affineFiniteSheaf_exists_generatingSections {M : (Spec R).Modules}
    (hM : affineFiniteSheaf R M) :
    ∃ G : M.GeneratingSections, G.IsFiniteType := by
  classical
  have : M.IsQuasicoherent := hM.1
  have : Module.Finite R (moduleSpecΓFunctor.obj M) := hM.2
  have : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let N := moduleSpecΓFunctor.obj M
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top (R := R) (M := N))
  let f : ((s : Set N) →₀ R) →ₗ[R] N :=
    Finsupp.linearCombination R (fun x : (s : Set N) => x.1)
  let P := presentationTilde N (s : Set N) hs (LinearMap.ker f) (Submodule.span_eq _)
  have : P.generators.IsFiniteType :=
    ⟨inferInstanceAs (Finite (s : Set N))⟩
  exact ⟨P.generators.ofEpi M.fromTildeΓ, inferInstance⟩

/-- Affine finite quasicoherent sheaves are exactly quasicoherent sheaves
admitting a finite global generating family. -/
theorem affineFiniteSheaf_iff_exists_generatingSections (M : (Spec R).Modules) :
    affineFiniteSheaf R M ↔
      M.IsQuasicoherent ∧ ∃ G : M.GeneratingSections, G.IsFiniteType := by
  constructor
  · intro hM
    exact ⟨hM.1, affineFiniteSheaf_exists_generatingSections R hM⟩
  · rintro ⟨hM, G, hG⟩
    exact ⟨hM, finite_globalSections_of_generatingSections R M G⟩

/-- Restriction to an arbitrary affine open preserves finite quasicoherent
sheaves. This uses finite generating sections, not a claim that the affine
open is principal or a localization at a multiplicative subset. -/
theorem affineFiniteSheaf_restrict {S : CommRingCat.{u}}
    (j : Spec S ⟶ Spec R) [IsOpenImmersion j] {M : (Spec R).Modules}
    (hM : affineFiniteSheaf R M) :
    affineFiniteSheaf S ((Scheme.Modules.restrictFunctor j).obj M) := by
  have : M.IsQuasicoherent := hM.1
  obtain ⟨G, hG⟩ := affineFiniteSheaf_exists_generatingSections R hM
  have : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor j) := inferInstance
  let H := G.map (Scheme.Modules.restrictFunctor j) (Scheme.Modules.restrictUnitIso j).symm
  exact ⟨inferInstance, finite_globalSections_of_generatingSections S _ H⟩

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
