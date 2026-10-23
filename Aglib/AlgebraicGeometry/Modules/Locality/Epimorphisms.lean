/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness

/-!
# Epimorphisms of module sheaves detected on open covers

A morphism of module sheaves is an epimorphism if its restrictions along a jointly surjective
family of open immersions are epimorphisms: its cokernel then vanishes on every member of the
family (`isZero_of_restrict_openCover`). The restriction-to-pullback comparison along an open
immersion carries epimorphic pullbacks to epimorphic restrictions, so the criterion also holds
with pullbacks (`epi_of_pullback_openCover`). This is the epimorphism counterpart of
`mono_of_restrict_openCover` (`Modules/Locality/Monomorphisms`).
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- **Epimorphisms are detected on open covers**: a morphism of module sheaves whose restrictions
along a jointly surjective family of open immersions are epimorphisms is an epimorphism. -/
theorem epi_of_restrict_openCover {X : Scheme.{u}} {ι : Type v}
    (Y : ι → Scheme.{u}) (a : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (a i)]
    (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), a i y = x)
    {M N : X.Modules} (f : M ⟶ N)
    (hf : ∀ i, Epi ((Scheme.Modules.restrictFunctor (a i)).map f)) : Epi f := by
  apply Preadditive.epi_of_isZero_cokernel
  apply isZero_of_restrict_openCover Y a hcover
  intro i
  have := hf i
  exact (isZero_cokernel_of_epi ((Scheme.Modules.restrictFunctor (a i)).map f)).of_iso
    (PreservesCokernel.iso (Scheme.Modules.restrictFunctor (a i)) f)

/-- Epimorphicity of the pullback along an open immersion gives epimorphicity of the
restriction, through `restrictFunctorIsoPullback`. -/
theorem epi_restrict_of_epi_pullback {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] {M N : X.Modules} (f : M ⟶ N)
    [Epi ((Scheme.Modules.pullback j).map f)] :
    Epi ((Scheme.Modules.restrictFunctor j).map f) := by
  let e := Scheme.Modules.restrictFunctorIsoPullback j
  have h : (Scheme.Modules.restrictFunctor j).map f =
      e.hom.app M ≫ (Scheme.Modules.pullback j).map f ≫ e.inv.app N := by
    rw [← e.hom.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [h]
  infer_instance

/-- **Epimorphisms are detected by pullbacks along open covers**: a morphism of module sheaves
whose pullbacks along a jointly surjective family of open immersions are epimorphisms is an
epimorphism. -/
theorem epi_of_pullback_openCover {X : Scheme.{u}} {ι : Type v}
    (Y : ι → Scheme.{u}) (a : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (a i)]
    (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), a i y = x)
    {M N : X.Modules} (f : M ⟶ N)
    (hf : ∀ i, Epi ((Scheme.Modules.pullback (a i)).map f)) : Epi f :=
  epi_of_restrict_openCover Y a hcover f fun i =>
    haveI := hf i
    epi_restrict_of_epi_pullback (a i) f

end AlgebraicGeometry.Scheme.Modules
