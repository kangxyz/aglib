/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Invertible.Affine
public import Aglib.AlgebraicGeometry.IdealSheaf.LocallyClosed
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.OpenImmersion
public import Aglib.AlgebraicGeometry.Modules.Invertible.Affine
public import Aglib.AlgebraicGeometry.Modules.Invertible.Locus

/-!
# Flat inverse images of actual Cartier ideals

Local rank one of the actual ideal module is preserved by a flat inverse image.
The proof uses affine regular generators, the native image-ideal formula and flat
preservation of regularity. No flatness of the quotient or finiteness hypothesis
is used. The lower result has no blowup dependency.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom
open Module

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

private lemma spectralIdeal_rankOne_of_regularGenerator {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (r : R) (hr : IsSMulRegular R r)
    (hker : RingHom.ker φ.hom = Ideal.span {r}) :
    IsLocallyRankOne (Spec R) (idealModule (Spec.map φ)) := by
  let b := Ideal.regularPrincipalIdealBasis (RingHom.ker φ.hom) r hr hker
  let e : R ≃ₗ[R] RingHom.ker φ.hom := (Basis.singleton PUnit R).equiv b (Equiv.refl _)
  let eM : ModuleCat.of R R ≅ ModuleCat.of R (RingHom.ker φ.hom) := e.toModuleIso
  have hfree : IsLocallyRankOne (Spec R) (tilde (ModuleCat.of R R)) :=
    tilde_isLocallyRankOne (R := R) (ModuleCat.of R R)
  exact isLocallyRankOne_of_iso _
    ((tilde.functor R).mapIso eM ≪≫ affineIdealIso φ) hfree

/-- Flat inverse image preserves local rank one of the actual ideal module. The ideal is
the native `I.comap f`, with all its scheme structure, over arbitrary schemes. -/
theorem isLocallyRankOne_comap_of_flat {X Y : Scheme.{u}} (I : X.IdealSheafData)
    (f : Y ⟶ X) [Flat f] (hI : IsLocallyRankOne X (idealModule I.subschemeι)) :
    IsLocallyRankOne Y (idealModule (I.comap f).subschemeι) := by
  apply isLocallyRankOne_of_forall_isLocallyRankOneAt
  intro y
  obtain ⟨U, hU, hyU, r, hr, hgen⟩ :=
    exists_affine_regular_idealGenerator_of_isLocallyRankOne I.subschemeι hI (f y)
  obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ f ⁻¹ᵁ U from hyU)
  let J := I.comap f
  let i := J.subschemeι
  let φ := i.app V
  let ψ := (f.appLE U V hVU).hom
  let : Algebra Γ(X, U) Γ(Y, V) := ψ.toAlgebra
  let : Module.Flat Γ(X, U) Γ(Y, V) := f.flat_appLE hU hV hVU
  have hr' : IsSMulRegular Γ(Y, V) (ψ r) := hr.of_flat
  have hker : RingHom.ker φ.hom = Ideal.span {ψ r} := by
    rw [I.ker_subschemeι_app ⟨U, hU⟩] at hgen
    rw [J.ker_subschemeι_app ⟨V, hV⟩,
      ideal_comap_eq_map_appLE I f ⟨U, hU⟩ ⟨V, hV⟩ hVU, hgen,
      Ideal.map_span, Set.image_singleton]
  have hspec := spectralIdeal_rankOne_of_regularGenerator φ (ψ r) hr' hker
  have : IsIso V.toSpecΓ := inferInstanceAs (IsIso hV.isoSpec.hom)
  have hD : IsAffineOpen (i ⁻¹ᵁ V) := hV.preimage i
  have : IsIso (i ⁻¹ᵁ V).toSpecΓ := inferInstanceAs (IsIso hD.isoSpec.hom)
  have hsquare := Scheme.Opens.toSpecΓ_naturality i V
  have : IsIso (idealPullbackMap (Spec.map φ) (i ∣_ V) V.toSpecΓ
      (i ⁻¹ᵁ V).toSpecΓ hsquare) :=
    idealPullbackMap_isIso_of_iso_square _ _ _ _ _
  have hlocal : IsLocallyRankOne V.toScheme (idealModule (i ∣_ V)) :=
    isLocallyRankOne_of_iso _
      (asIso (idealPullbackMap (Spec.map φ) (i ∣_ V) V.toSpecΓ
        (i ⁻¹ᵁ V).toSpecΓ hsquare)) (pullback_locallyRankOne V.toSpecΓ _ hspec)
  exact ⟨V.toScheme, V.ι, inferInstance, ⟨⟨y, hyV⟩, rfl⟩,
    isLocallyRankOne_of_iso _
      (asIso (idealPullbackMap i (i ∣_ V) V.ι (i ⁻¹ᵁ V).ι
        (morphismRestrict_ι i V).symm)).symm hlocal⟩

end AlgebraicGeometry.Scheme.IdealSheafData
