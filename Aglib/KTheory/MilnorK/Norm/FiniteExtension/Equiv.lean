/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.Basic

/-!
# Isomorphism transport of the actual finite-extension norm

The original coefficient square, together with polynomial coefficient base
change and proved presentation independence, gives naturality under field
isomorphisms. No tower compatibility is an input.
-/

@[expose] public noncomputable section

namespace MilnorK

open Polynomial PolynomialResidue PolynomialNorm Polynomial.LocalResidue

variable {k L : Type*} [Field k] [Field L]

/-- The literal polynomial transported through a coefficient field equivalence. -/
def normEquivPolynomial (φ : k ≃+* L) (p : MonicIrreducible k) : MonicIrreducible L :=
  ⟨p.val.map φ.toRingHom, p.property.1.map _, by
    change Irreducible ((Polynomial.mapEquiv φ) p.val)
    rw [MulEquiv.irreducible_iff]
    exact p.property.2⟩

/-- The actual root quotient equivalence for the transported coefficients. -/
def normEquivRoot (φ : k ≃+* L) (p : MonicIrreducible k) :
    AdjoinRoot p.val ≃+* AdjoinRoot (normEquivPolynomial φ p).val :=
  AdjoinRoot.mapRingEquiv φ p.val (normEquivPolynomial φ p).val (Associated.refl _)

/-- The root equivalence retains the original coefficient map. -/
theorem normEquivRoot_algebraMap (φ : k ≃+* L) (p : MonicIrreducible k) (a : k) :
    normEquivRoot φ p (algebraMap k (AdjoinRoot p.val) a) =
      algebraMap L (AdjoinRoot (normEquivPolynomial φ p).val) (φ a) := by
  change AdjoinRoot.map φ.toRingHom p.val (normEquivPolynomial φ p).val dvd_rfl
    (AdjoinRoot.of p.val a) = _
  exact AdjoinRoot.map_of _ _ _ _ _

/-- The equivalence is exactly the original coefficient quotient map. -/
theorem normEquivRoot_toRingHom (φ : k ≃+* L) (p : MonicIrreducible k) :
    (normEquivRoot φ p).toRingHom = adjoinRootMap φ.toRingHom p.val
      (normEquivPolynomial φ p).val dvd_rfl := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro a
    exact (normEquivRoot_algebraMap φ p a).trans
      (adjoinRootMap_algebraMap φ.toRingHom p.val
        (normEquivPolynomial φ p).val dvd_rfl a).symm
  · change AdjoinRoot.map φ.toRingHom p.val (normEquivPolynomial φ p).val dvd_rfl
      (AdjoinRoot.root p.val) = _
    exact (AdjoinRoot.map_root φ.toRingHom p.val
      (normEquivPolynomial φ p).val dvd_rfl).trans
      (adjoinRootMap_root φ.toRingHom p.val (normEquivPolynomial φ p).val dvd_rfl).symm

variable {E F : Type*} [Field E] [Field F] [Algebra k E] [Algebra L F]

/-- Transporting the actual primitive presentation along the original square. -/
def normEquivPresentation (φ : k ≃+* L) (ψ : E ≃+* F)
    (hsquare : ∀ a : k, ψ (algebraMap k E a) = algebraMap L F (φ a))
    (p : MonicIrreducible k) (ε : AdjoinRoot p.val ≃ₐ[k] E) :
    AdjoinRoot (normEquivPolynomial φ p).val ≃ₐ[L] F :=
  { (normEquivRoot φ p).symm.trans (ε.toRingEquiv.trans ψ) with
    commutes' := by
      intro b
      obtain ⟨a, rfl⟩ := φ.surjective b
      change ψ (ε ((normEquivRoot φ p).symm (algebraMap L _ (φ a)))) = _
      rw [← normEquivRoot_algebraMap, RingEquiv.symm_apply_apply, AlgEquiv.commutes,
        hsquare] }

/-- The original finite-extension norm is natural under an actual field square. -/
theorem finiteExtensionNorm_equiv [CharZero k] [CharZero L]
    [FiniteDimensional k E] [FiniteDimensional L F]
    (φ : k ≃+* L) (ψ : E ≃+* F)
    (hsquare : ∀ a : k, ψ (algebraMap k E a) = algebraMap L F (φ a))
    (n : ℕ) (x : K E n) :
    map n φ.toRingHom (finiteExtensionNorm k E n x) =
      finiteExtensionNorm L F n (map n ψ.toRingHom x) := by
  let p := finiteNormPolynomial k E
  let ε := finiteNormPresentation k E
  let q := normEquivPolynomial φ p
  let η := normEquivPresentation φ ψ hsquare p ε
  rw [finiteExtensionNorm_eq_presentation k E n p ε,
    finiteExtensionNorm_eq_presentation L F n q η]
  simp only [LinearMap.comp_apply]
  rw [polynomialNorm_restrict_irreducible φ.toRingHom n p q rfl]
  apply congrArg (polynomialNorm n q)
  have he : (adjoinRootMap φ.toRingHom p.val q.val dvd_rfl).comp ε.symm.toRingHom =
      η.symm.toRingHom.comp ψ.toRingHom := by
    rw [← normEquivRoot_toRingHom]
    apply RingHom.ext
    intro a
    change normEquivRoot φ p (ε.symm a) =
      normEquivRoot φ p (ε.symm (ψ.symm (ψ a)))
    rw [RingEquiv.symm_apply_apply]
  simpa only [map_comp, LinearMap.comp_apply] using congrArg (fun f => map n f x) he

/-- The norm is unchanged by an actual algebra equivalence of the upper field. -/
theorem finiteExtensionNorm_map_algEquiv {A B C : Type*}
    [Field A] [CharZero A] [Field B] [Field C] [Algebra A B] [Algebra A C]
    [FiniteDimensional A B] [FiniteDimensional A C]
    (ε : B ≃ₐ[A] C) (n : ℕ) (x : K B n) :
    finiteExtensionNorm A C n (map n ε.toRingHom x) = finiteExtensionNorm A B n x := by
  have h := finiteExtensionNorm_equiv (RingEquiv.refl A) ε.toRingEquiv ε.commutes n x
  change map n (RingHom.id A) (finiteExtensionNorm A B n x) = _ at h
  rw [map_id, LinearMap.id_apply] at h
  exact h.symm

end MilnorK
