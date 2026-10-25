/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Normalization
public import Aglib.AlgebraicGeometry.Properties.Normal.Affine

/-! # Normal stalks of the actual normalization in a field point

The affine charts are the original integral closures in the original source
section rings. Any chart meeting a point meets the dominant field source,
so that source open is the whole field spectrum. Its integral closure is a
normal domain even when the original affine base ring is not a domain.

No finiteness, Noetherianity, normality of the base or Japanese hypothesis is
used. The actual normalization remains merely integral over the base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global

universe u

/-- A nonempty open of the actual field spectrum is the whole spectrum. -/
theorem fieldOpen_eq_top (K : Type u) [Field K]
    (U : (Spec (.of K)).Opens) [Nonempty U] : U = ⊤ := by
  apply le_antisymm le_top
  intro x _
  obtain ⟨y⟩ := ‹Nonempty U›
  rw [Subsingleton.elim x y.1]
  exact y.2

/-- The actual sections on a nonempty field open retain the original field
through the original restriction equality and affine section isomorphism. -/
def fieldOpenSectionsIso (K : Type u) [Field K]
    (U : (Spec (.of K)).Opens) [Nonempty U] :
    Γ(Spec (.of K), U) ≅ CommRingCat.of K :=
  eqToIso (by rw [fieldOpen_eq_top K U]) ≪≫ Scheme.ΓSpecIso (.of K)

/-- Integral closure in an arbitrary field is a normal domain, including
noninjective original base algebras. No finite-extension premise is needed. -/
theorem integralClosure_isIntegrallyClosed (R K : Type u) [CommRing R] [Field K]
    [Algebra R K] : IsIntegrallyClosed (integralClosure R K) :=
  IsIntegrallyClosed.of_isIntegrallyClosedIn (integralClosure R K) K

/-- Transport integral closedness through the field section isomorphism
without replacing the original section ring or integral-closure structures. -/
theorem integralClosure_normal_domain_of_ringIso (R B K : Type u) [CommRing R]
    [CommRing B] [Field K] [Algebra R B] (e : CommRingCat.of B ≅ CommRingCat.of K) :
    IsIntegrallyClosed (integralClosure R B) ∧ IsDomain (integralClosure R B) := by
  let C := integralClosure R B
  let ε : B ≃+* K := e.commRingCatIsoToRingEquiv
  let : Algebra C K := (ε.toRingHom.comp C.val.toRingHom).toAlgebra
  have hι : Function.Injective (algebraMap C K) := ε.injective.comp Subtype.val_injective
  have : FaithfulSMul C K := (faithfulSMul_iff_algebraMap_injective C K).mpr hι
  let φ : K →ₐ[C] B := {
    toRingHom := ε.symm.toRingHom
    commutes' c := by
      change ε.symm (ε c.1) = c.1
      exact ε.symm_apply_apply c.1 }
  have : IsIntegrallyClosedIn C K :=
    AlgHom.isIntegrallyClosedIn φ ε.symm.injective inferInstance
  exact ⟨IsIntegrallyClosed.of_isIntegrallyClosedIn C K, hι.isDomain _⟩

/-- Every stalk of the actual relative normalization in a field point is an
integrally closed domain. This does not assert that its structural map is finite. -/
theorem fieldNormalization_stalk_normal_domain {X : Scheme.{u}}
    (K : Type u) [Field K] (f : Spec (.of K) ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    (x : f.normalization) :
    IsIntegrallyClosed (f.normalization.presheaf.stalk x) ∧
      IsDomain (f.normalization.presheaf.stalk x) := by
  let cov := f.normalizationOpenCover
  let U : X.affineOpens := cov.idx x
  obtain ⟨y, hy⟩ := cov.covers x
  have hxU : x ∈ f.fromNormalization ⁻¹ᵁ U.1 := by
    rw [Scheme.Hom.fromNormalization_preimage]
    exact ⟨y, hy⟩
  obtain ⟨z, hz⟩ := f.toNormalization.denseRange.exists_mem_open
    (f.fromNormalization ⁻¹ᵁ U.1).isOpen ⟨x, hxU⟩
  have hsource : f z ∈ U.1 := by
    change f.fromNormalization (f.toNormalization z) ∈ U.1 at hz
    simpa only [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization] using hz
  let V := f ⁻¹ᵁ U.1
  have : Nonempty V := ⟨⟨z, hsource⟩⟩
  let B := Γ(Spec (.of K), V)
  let e : B ≅ CommRingCat.of K := fieldOpenSectionsIso K V
  let : Algebra Γ(X, U.1) B := (f.app U.1).hom.toAlgebra
  let C := integralClosure Γ(X, U.1) B
  have hC := integralClosure_normal_domain_of_ringIso Γ(X, U.1) B K e
  have : IsDomain C := hC.2
  have : IsIntegrallyClosed C := hC.1
  have hs : IsIntegrallyClosed ((cov.X U).presheaf.stalk y) ∧
      IsDomain ((cov.X U).presheaf.stalk y) := by
    change IsIntegrallyClosed ((Spec (.of C)).presheaf.stalk y) ∧
      IsDomain ((Spec (.of C)).presheaf.stalk y)
    exact @Scheme.isIntegrallyClosed_and_isDomain_stalk_Spec C
      (inferInstanceAs (CommRing C)) hC.2 hC.1 y
  let g := cov.f U
  have : IsOpenImmersion g := by dsimp [g]; infer_instance
  have : IsIntegrallyClosed ((cov.X U).presheaf.stalk y) := hs.1
  have : IsDomain ((cov.X U).presheaf.stalk y) := hs.2
  rw [← hy]
  let ρ := (asIso (g.stalkMap y)).symm.commRingCatIsoToRingEquiv
  exact ⟨IsIntegrallyClosed.of_equiv ρ, ρ.symm.toMulEquiv.isDomain _⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global
