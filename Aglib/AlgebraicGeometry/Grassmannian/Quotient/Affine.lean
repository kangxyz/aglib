/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.Quotient.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Free.Sections
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.Projective
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.LocalBases
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.FiniteType
public import Mathlib.RingTheory.Grassmannian

/-!
# Locally free quotients on an affine scheme

Let `A` be a commutative ring and `M` an `A`-module with a basis `b` indexed by `ULift (Fin n)`,
so that `M~ ≅ O^n` on `Spec A` (`tildeBasisIso`). A point `N` of Mathlib's Grassmannian
`G(k, M; A)` (a submodule with finite projective quotient of constant rank `k`) gives the
quotient `tildeQuot b N : O^n ≅ M~ ⟶ (M ⧸ N)~`, a rank-`k` locally free quotient of `O^n`.
Every rank-`k` locally free quotient of `O^n` on `Spec A` is isomorphic to exactly one of these
(`exists_tildeQuot_equiv`, `eq_of_tildeQuot_equiv`): its quotient sheaf is quasi-coherent, hence
the sheaf of its finite projective module of global sections.

The ranks are compared through Fitting ideals: on `Spec A`, the fibre rank at `y` of a finitely
presented sheaf whose module of global sections is finite and flat is the stalk rank at `y` of its
global sections (`Scheme.Modules.sheafRank_eq_rankAtStalk`, with `sheafHasRank_tilde` and
`rankAtStalk_globalSections`, in `Aglib.AlgebraicGeometry.Modules.FittingIdeal.ConstantRank`).

## Main results

- `Grassmannian.tildeQuot b N`, `Grassmannian.eq_of_tildeQuot_equiv`,
  `Grassmannian.exists_tildeQuot_equiv`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.Grassmannian

open Scheme.Modules

variable {A : CommRingCat.{u}} {k n : ℕ}

variable {M : Type u} [AddCommGroup M] [Module A M]

/-- The quotient `O^n ≅ M~ ⟶ (M ⧸ N)~` on `Spec A` of a point `N` of `G(k, M; A)`, for a basis
`b` of `M` indexed by `ULift (Fin n)`. -/
def tildeQuot (b : Module.Basis (ULift.{u} (Fin n)) A M) (N : Module.Grassmannian A M k) :
    LocallyFreeQuotient (Spec A) k n where
  obj := tilde (ModuleCat.of A (M ⧸ N.toSubmodule))
  π := (tildeBasisIso (ModuleCat.of A M) b).inv ≫
    tilde.map (ModuleCat.ofHom N.toSubmodule.mkQ)
  epi_π := by
    have : Epi (ModuleCat.ofHom N.toSubmodule.mkQ) :=
      (ModuleCat.epi_iff_surjective _).mpr N.toSubmodule.mkQ_surjective
    have : Epi (tilde.map (ModuleCat.ofHom N.toSubmodule.mkQ)) :=
      (tilde.functor A).map_epi _
    exact epi_comp _ _
  hasRank := sheafHasRank_tilde _ N.rankAtStalk_eq

theorem tildeQuot_π (b : Module.Basis (ULift.{u} (Fin n)) A M) (N : Module.Grassmannian A M k) :
    (tildeQuot b N).π = (tildeBasisIso (ModuleCat.of A M) b).inv ≫
      tilde.map (ModuleCat.ofHom N.toSubmodule.mkQ) := rfl

/-- An isomorphism of the quotients of two points is induced by a module map under `M`. -/
theorem le_of_tildeQuot_iso (b : Module.Basis (ULift.{u} (Fin n)) A M)
    {N N' : Module.Grassmannian A M k} (e : (tildeQuot b N).IsoUnder (tildeQuot b N')) :
    N.toSubmodule ≤ N'.toSubmodule := by
  let f₀ := (tilde.functor A).preimage e.iso.hom
  have hf₀ : tilde.map f₀ = e.iso.hom := (tilde.functor A).map_preimage _
  have hc := e.comm
  rw [tildeQuot_π, tildeQuot_π, Category.assoc, cancel_epi, ← hf₀, ← tilde.map_comp] at hc
  have h := (tilde.functor A).map_injective hc
  intro v hv
  have hv' := congrArg (fun g ↦ g.hom v) h
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    Submodule.mkQ_apply] at hv'
  rw [(Submodule.Quotient.mk_eq_zero _).mpr hv, map_zero] at hv'
  exact (Submodule.Quotient.mk_eq_zero _).mp hv'.symm

/-- **Injectivity on `Spec A`**: points with isomorphic quotients are equal. -/
theorem eq_of_tildeQuot_equiv (b : Module.Basis (ULift.{u} (Fin n)) A M)
    {N N' : Module.Grassmannian A M k} (h : tildeQuot b N ≈ tildeQuot b N') : N = N' := by
  obtain ⟨e⟩ := h
  exact Module.Grassmannian.ext
    (le_antisymm (le_of_tildeQuot_iso b e) (le_of_tildeQuot_iso b e.symm))

/-- **Surjectivity on `Spec A`**: every rank-`k` locally free quotient of `O^n` on `Spec A` is
isomorphic to the quotient of a point of `G(k, M; A)`. -/
theorem exists_tildeQuot_equiv (b : Module.Basis (ULift.{u} (Fin n)) A M)
    (P : LocallyFreeQuotient (Spec A) k n) :
    ∃ N : Module.Grassmannian A M k, P ≈ tildeQuot b N := by
  have : IsFiniteLocallyFree _ P.obj := P.hasRank.isFiniteLocallyFree
  have : IsIso P.obj.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent P.obj
  let c : tilde (moduleSpecΓFunctor.obj P.obj) ≅ P.obj := asIso P.obj.fromTildeΓ
  let g : ModuleCat.of A M ⟶ moduleSpecΓFunctor.obj P.obj :=
    (tilde.functor A).preimage
      ((tildeBasisIso (ModuleCat.of A M) b).hom ≫ P.π ≫ c.inv)
  have hg : tilde.map g =
      (tildeBasisIso (ModuleCat.of A M) b).hom ≫ P.π ≫ c.inv :=
    (tilde.functor A).map_preimage _
  have hge : Epi ((tilde.functor A).map g) := by
    change Epi (tilde.map g)
    rw [hg]
    infer_instance
  have : Epi g := (tilde.functor A).epi_of_epi_map hge
  have hsurj : Function.Surjective g.hom := (ModuleCat.epi_iff_surjective g).mp this
  let e := g.hom.quotKerEquivOfSurjective hsurj
  have : Module.Finite A (moduleSpecΓFunctor.obj P.obj) :=
    finite_globalSections_of_finiteLocallyFree A P.obj
  have : Module.Projective A (moduleSpecΓFunctor.obj P.obj) :=
    projective_globalSections_of_finiteLocallyFree A P.obj
  let N : Module.Grassmannian A M k :=
    { toSubmodule := LinearMap.ker g.hom
      finite_quotient := Module.Finite.equiv e.symm
      projective_quotient := Module.Projective.of_equiv e.symm
      rankAtStalk_eq := fun p ↦ by
        rw [congrFun (Module.rankAtStalk_eq_of_equiv e) p]
        exact rankAtStalk_globalSections P.obj P.hasRank p }
  refine ⟨N, ⟨⟨c.symm ≪≫ (tilde.functor A).mapIso e.symm.toModuleIso, ?_⟩⟩⟩
  have hgc : P.π ≫ c.inv =
      (tildeBasisIso (ModuleCat.of A M) b).inv ≫ tilde.map g := by
    rw [hg, Iso.inv_hom_id_assoc]
  have hmk : g ≫ e.symm.toModuleIso.hom = ModuleCat.ofHom N.toSubmodule.mkQ := by
    ext v
    change e.symm (g.hom v) = Submodule.Quotient.mk v
    rw [LinearEquiv.symm_apply_eq]
    exact (LinearMap.quotKerEquivOfSurjective_apply_mk _ hsurj v).symm
  rw [tildeQuot_π, Iso.trans_hom, Iso.symm_hom, ← Category.assoc, hgc, Category.assoc,
    Functor.mapIso_hom, tilde.functor_map, ← tilde.map_comp, hmk]

end AlgebraicGeometry.Grassmannian
