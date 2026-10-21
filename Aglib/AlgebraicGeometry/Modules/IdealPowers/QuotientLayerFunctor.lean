/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IdealPowers.QuotientLayers

/-! # Naturality and composition of finite-stage quotient-layer maps -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

universe u
variable (X : Scheme.{u}) {A : Type u} [CommRing A] (α : A →+* Γ(X, ⊤))

/-- The actual map of quotient layers under an original coefficient morphism. -/
def idealQuotientLayerHom {F G : X.Modules} {J J' : Ideal A}
    (h : J ≤ J') (f : F ⟶ G) :
    idealQuotientLayer X α F h ⟶ idealQuotientLayer X α G h :=
  kernel.map (idealQuotientMap X α F h) (idealQuotientMap X α G h)
    (idealQuotientHom X α J f) (idealQuotientHom X α J' f)
    (idealQuotientHom_map X α h f).symm

@[reassoc (attr := simp)]
theorem idealQuotientLayerHom_ι {F G : X.Modules} {J J' : Ideal A}
    (h : J ≤ J') (f : F ⟶ G) :
    idealQuotientLayerHom X α h f ≫ kernel.ι (idealQuotientMap X α G h) =
      kernel.ι (idealQuotientMap X α F h) ≫ idealQuotientHom X α J f := by
  simp [idealQuotientLayerHom]

/-- Homogeneous layer multiplication commutes with every original coefficient map. -/
@[reassoc]
theorem idealQuotientLayerMul_naturality {F G : X.Modules} (f : F ⟶ G)
    {J J' K K' : Ideal A} (hJ : J ≤ J') (hK : K ≤ K') (a : A)
    (ha : ∀ b ∈ J, a * b ∈ K) (ha' : ∀ b ∈ J', a * b ∈ K') :
    idealQuotientLayerHom X α hJ f ≫ idealQuotientLayerMul X α G hJ hK a ha ha' =
      idealQuotientLayerMul X α F hJ hK a ha ha' ≫ idealQuotientLayerHom X α hK f := by
  apply (cancel_mono (kernel.ι (idealQuotientMap X α G hK))).mp
  simp only [Category.assoc, idealQuotientLayerMul_ι, idealQuotientLayerHom_ι,
    idealQuotientLayerMul_ι_assoc, idealQuotientLayerHom_ι_assoc]
  rw [idealQuotientMul_naturality]

/-- Multiplication of scalars is composition of the actual finite-stage layer maps. -/
theorem idealQuotientLayerMul_comp (F : X.Modules) {J J' K K' L L' : Ideal A}
    (hJ : J ≤ J') (hK : K ≤ K') (hL : L ≤ L') (a b : A)
    (ha : ∀ x ∈ J, a * x ∈ K) (ha' : ∀ x ∈ J', a * x ∈ K')
    (hb : ∀ x ∈ K, b * x ∈ L) (hb' : ∀ x ∈ K', b * x ∈ L') :
    idealQuotientLayerMul X α F hJ hK a ha ha' ≫
      idealQuotientLayerMul X α F hK hL b hb hb' =
    idealQuotientLayerMul X α F hJ hL (b * a)
      (fun x hx => by rw [mul_assoc]; exact hb _ (ha x hx))
      (fun x hx => by rw [mul_assoc]; exact hb' _ (ha' x hx)) := by
  apply (cancel_mono (kernel.ι (idealQuotientMap X α F hL))).mp
  simp only [Category.assoc, idealQuotientLayerMul_ι, idealQuotientLayerMul_ι_assoc]
  rw [idealQuotientMul_comp]

end AlgebraicGeometry.Scheme.Modules
