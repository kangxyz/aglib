/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.AffineRestriction
public import Aglib.LinearAlgebra.FrobeniusBaseChange

/-!
# Semilinear operators on the original affine pullback sections

The operator is conjugated through the native affine pullback-section
comparison. Its original pure-tensor equation proves compatibility with every
affine over-map. There is no replacement coefficient sheaf and no flatness,
finiteness, domain or Noetherian premise.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

private theorem extendScalars_addHom_ext {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (M : ModuleCat.{u} R) {N : Type u} [AddCommGroup N]
    (g h : (ModuleCat.extendScalars f).obj M →+ N)
    (he : ∀ (r : S) (m : M), g (r ⊗ₜ[R,f] m) = h (r ⊗ₜ[R,f] m)) : g = h := by
  apply AddMonoidHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul r m => exact he r m
  | add x y hx hy =>
    erw [AddMonoidHom.map_add, AddMonoidHom.map_add]
    exact congrArg₂ (· + ·) hx hy

variable (X : Scheme.{u}) [IsAffine X] (F : X.Modules) [F.IsQuasicoherent]
  (p : ℕ) (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
  (Φ : (affineΓFunctor X).obj F →ₛₗ[RingHom.frobeniusOfPrimeCastEqZero p hp hX]
    (affineΓFunctor X).obj F)

/-- The original semilinear operator on the actual pullback sections of an affine test. -/
def affineSectionFrobenius (T : Over X) [IsAffine T.left] :
    Γ((pullback T.hom).obj F, ⊤) →+ Γ((pullback T.hom).obj F, ⊤) := by
  let : Algebra Γ(X, ⊤) Γ(T.left, ⊤) := T.hom.appTop.hom.toAlgebra
  let e := (affinePullbackSectionsIso T.hom F).toLinearEquiv.toAddEquiv
  exact e.toAddMonoidHom.comp
    ((LinearMap.frobeniusBaseChange p hp hX Φ Γ(T.left, ⊤)).toAddMonoidHom.comp
      e.symm.toAddMonoidHom)

/-- The operator retains the original affine-section tensor coordinates. -/
theorem affineSectionFrobenius_tmul (T : Over X) [IsAffine T.left]
    (r : Γ(T.left, ⊤)) (s : (affineΓFunctor X).obj F) :
    affineSectionFrobenius X F p hp hX Φ T
      ((affinePullbackSectionsIso T.hom F).hom
        (r ⊗ₜ[Γ(X, ⊤),T.hom.appTop.hom] s)) =
      (affinePullbackSectionsIso T.hom F).hom
        ((r ^ p) ⊗ₜ[Γ(X, ⊤),T.hom.appTop.hom] Φ s) := by
  let : Algebra Γ(X, ⊤) Γ(T.left, ⊤) := T.hom.appTop.hom.toAlgebra
  change (affinePullbackSectionsIso T.hom F).toLinearEquiv
    (LinearMap.frobeniusBaseChange p hp hX Φ Γ(T.left, ⊤)
      ((affinePullbackSectionsIso T.hom F).toLinearEquiv.symm
        ((affinePullbackSectionsIso T.hom F).toLinearEquiv _))) = _
  erw [LinearEquiv.symm_apply_apply]
  rfl

/-- The original additive restriction commutes with the operator on every affine tensor. -/
theorem affineSectionFrobenius_naturality_tmul {T U : Over X}
    [IsAffine T.left] [IsAffine U.left] (f : U ⟶ T)
    (r : Γ(T.left, ⊤)) (m : (affineΓFunctor X).obj F) :
    sectionsAddHom X F f (affineSectionFrobenius X F p hp hX Φ T
      ((affinePullbackSectionsIso T.hom F).hom
        (r ⊗ₜ[Γ(X, ⊤),T.hom.appTop.hom] m))) =
      affineSectionFrobenius X F p hp hX Φ U
        (sectionsAddHom X F f ((affinePullbackSectionsIso T.hom F).hom
          (r ⊗ₜ[Γ(X, ⊤),T.hom.appTop.hom] m))) := by
  have ht (r : Γ(T.left, ⊤)) (m : (affineΓFunctor X).obj F) :
      sectionsAddHom X F f ((affinePullbackSectionsIso T.hom F).hom
        (r ⊗ₜ[Γ(X, ⊤),T.hom.appTop.hom] m)) =
      (affinePullbackSectionsIso U.hom F).hom
        (f.left.appTop.hom r ⊗ₜ[Γ(X, ⊤),U.hom.appTop.hom] m) := by
    exact congrArg (β := Γ((pullback U.hom).obj F, ⊤))
      (fun z : (sectionsPresheaf X F).obj (op U) =>
      (z : Γ((pullback U.hom).obj F, ⊤)))
      (sectionsPresheaf_map_affine_tmul X F f r m)
  have hT := affineSectionFrobenius_tmul X F p hp hX Φ T r m
  have hr := ht r m
  have hrp := ht (r ^ p) (Φ m)
  have hU := affineSectionFrobenius_tmul X F p hp hX Φ U
    (f.left.appTop.hom r) m
  have hpow := congrArg (β := Γ((pullback U.hom).obj F, ⊤))
    (fun a : Γ(U.left, ⊤) => (affinePullbackSectionsIso U.hom F).hom
      (a ⊗ₜ[Γ(X, ⊤),U.hom.appTop.hom] Φ m))
    (map_pow f.left.appTop.hom r p)
  have hh := (congrArg
    (fun z : Γ((pullback T.hom).obj F, ⊤) => sectionsAddHom X F f z) hT).trans
    (hrp.trans (hpow.trans (hU.symm.trans
      (congrArg (affineSectionFrobenius X F p hp hX Φ U) hr.symm))))
  exact hh

/-- Compatibility is with the actual geometric section restriction. -/
theorem affineSectionFrobenius_naturality_hom {T U : Over X}
    [IsAffine T.left] [IsAffine U.left] (f : U ⟶ T) :
    (sectionsAddHom X F f).comp (affineSectionFrobenius X F p hp hX Φ T) =
      (affineSectionFrobenius X F p hp hX Φ U).comp (sectionsAddHom X F f) := by
  let e : (ModuleCat.extendScalars T.hom.appTop.hom).obj ((affineΓFunctor X).obj F) →+
      Γ((pullback T.hom).obj F, ⊤) :=
    (affinePullbackSectionsIso T.hom F).hom.hom.toAddMonoidHom
  let g := (sectionsAddHom X F f).comp ((affineSectionFrobenius X F p hp hX Φ T).comp e)
  let h := (affineSectionFrobenius X F p hp hX Φ U).comp ((sectionsAddHom X F f).comp e)
  have heval (z) : e z = (affinePullbackSectionsIso T.hom F).hom z := rfl
  have hg (z) : g z = sectionsAddHom X F f
      (affineSectionFrobenius X F p hp hX Φ T
        ((affinePullbackSectionsIso T.hom F).hom z)) := by
    simp only [g, AddMonoidHom.comp_apply, heval]
  have hq (z) : h z = affineSectionFrobenius X F p hp hX Φ U
      (sectionsAddHom X F f ((affinePullbackSectionsIso T.hom F).hom z)) := by
    simp only [h, AddMonoidHom.comp_apply, heval]
  have he : g = h := by
    apply extendScalars_addHom_ext T.hom.appTop.hom ((affineΓFunctor X).obj F)
    intro r m
    have hh := affineSectionFrobenius_naturality_tmul X F p hp hX Φ f r m
    exact (hg _).trans (hh.trans (hq _).symm)
  have hes : Function.Surjective e := by
    intro t
    obtain ⟨z, hz⟩ :=
      (ConcreteCategory.bijective_of_isIso (affinePullbackSectionsIso T.hom F).hom).2 t
    exact ⟨z, (heval z).trans hz⟩
  have hc : (sectionsAddHom X F f).comp (affineSectionFrobenius X F p hp hX Φ T) =
      (affineSectionFrobenius X F p hp hX Φ U).comp (sectionsAddHom X F f) :=
    (AddMonoidHom.cancel_right hes).mp he
  exact hc

/-- The whole additive square evaluates on the unchanged original section. -/
theorem affineSectionFrobenius_naturality {T U : Over X}
    [IsAffine T.left] [IsAffine U.left] (f : U ⟶ T)
    (s : Γ((pullback T.hom).obj F, ⊤)) :
    @Eq Γ((pullback U.hom).obj F, ⊤)
      ((sectionsPresheaf X F).map f.op (affineSectionFrobenius X F p hp hX Φ T s))
      (affineSectionFrobenius X F p hp hX Φ U ((sectionsPresheaf X F).map f.op s)) := by
  have hrmap : (sectionsAddHom X F f : Γ((pullback T.hom).obj F, ⊤) →
      Γ((pullback U.hom).obj F, ⊤)) = (sectionsPresheaf X F).map f.op := rfl
  have hv := DFunLike.congr_fun (affineSectionFrobenius_naturality_hom X F p hp hX Φ f) s
  simpa only [AddMonoidHom.comp_apply, hrmap] using hv

/-- On original geometric unit sections the extension is the original map. -/
theorem affineSectionFrobenius_unit (T : Over X) [IsAffine T.left]
    (s : (affineΓFunctor X).obj F) :
    affineSectionFrobenius X F p hp hX Φ T
      ((((pullbackPushforwardAdjunction T.hom).unit.app F).app ⊤) s) =
      (((pullbackPushforwardAdjunction T.hom).unit.app F).app ⊤) (Φ s) := by
  rw [← affinePullbackSectionsIso_one_tmul, affineSectionFrobenius_tmul, one_pow,
    affinePullbackSectionsIso_one_tmul]

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
