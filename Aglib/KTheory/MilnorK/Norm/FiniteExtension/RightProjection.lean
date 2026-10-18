/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.Basic
public import Aglib.KTheory.MilnorK.TupleSymbols

/-!
# Right base-unit projection for the actual finite-extension norm

Moving the final unit past an arbitrary symbol gives exactly its degree sign.
The identity descends to every Milnor class, and transports the proved left
projection formula to the rightmost slot used by the residue recursion.
No tower compatibility is an assumption of this argument.
-/

@[expose] public noncomputable section

namespace MilnorK

open MilnorK.K2 (unitsLinear)
open PolynomialNorm

variable {F : Type*} [Field F]

/-- Moving the last coordinate to the front gives the signed cyclic identity. -/
theorem symbol_snoc_eq_signed_cons (n : ℕ) (a : SymbolTuple F n) (b : Fˣ) :
    symbol (Fin.snoc a b) = (-1 : ℤ) ^ n • symbol (Fin.cons b a) := by
  induction n with
  | zero =>
    simp only [pow_zero, one_smul]
    congr 1
    funext i
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    rfl
  | succ n ih =>
    have ha : a = Fin.snoc (Fin.init a) (a (Fin.last n)) := (Fin.snoc_init_self a).symm
    rw [ha]
    let c : Fˣ := a (Fin.last n)
    let t : SymbolTuple F (n + 1 + 1) := Fin.snoc (Fin.snoc (Fin.init a) c) b
    have hs := symbol_skew t (Fin.last n).castSucc (Fin.last (n + 1)) (by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_last] at this
      omega)
    have hu : Function.update (Function.update t (Fin.last n).castSucc
        (t (Fin.last (n + 1)))) (Fin.last (n + 1)) (t (Fin.last n).castSucc) =
        Fin.snoc (Fin.snoc (Fin.init a) b) c := by
      simp only [t, Fin.snoc_last, Fin.snoc_castSucc, ← Fin.snoc_update,
        Fin.update_snoc_last]
    rw [hu] at hs
    change symbol (Fin.snoc (Fin.snoc (Fin.init a) c) b) = _
    rw [hs]
    have hc := congrArg (fun x : K F (n + 1) =>
      productUnit (n + 1) x (Additive.ofMul c)) (ih (Fin.init a))
    simp only [productUnit_symbol, toMul_ofMul, map_smul,
      LinearMap.smul_apply] at hc
    rw [hc, ← Fin.cons_snoc_eq_snoc_cons]
    simp only [pow_succ, mul_smul, neg_one_smul, smul_neg, c]

/-- Right-unit multiplication is left multiplication with the actual degree sign. -/
theorem productUnit_eq_signed_left (n : ℕ) (x : K F n) (b : Additive Fˣ) :
    productUnit n x b = (-1 : ℤ) ^ n •
      degreeCongr (Nat.one_add n) (product 1 n (unitsToOne F b) x) := by
  have h : ((productUnit n).flip b) = (-1 : ℤ) ^ n •
      (degreeCongr (Nat.one_add n)).toLinearMap.comp (product 1 n (unitsToOne F b)) := by
    apply linearMap_ext
    intro a
    simp only [LinearMap.flip_apply, productUnit_symbol, LinearMap.smul_apply,
      LinearMap.comp_apply, LinearEquiv.coe_coe]
    change symbol (Fin.snoc a b.toMul) = (-1 : ℤ) ^ n •
      degreeCongr (Nat.one_add n) (product 1 n (symbol (fun _ => b.toMul)) (symbol a))
    rw [product_symbol, degreeCongr_symbol, Fin.append_left_eq_cons]
    simpa only [Function.comp_def, Fin.cast_cast, Fin.cast_refl, id_eq] using
      symbol_snoc_eq_signed_cons n a b.toMul
  exact LinearMap.congr_fun h x

variable (k E : Type*) [Field k] [CharZero k] [Field E]
  [Algebra k E] [FiniteDimensional k E]

/-- The actual finite-extension norm satisfies left projection on arbitrary classes. -/
theorem finiteExtensionNorm_product_constants_left (m n : ℕ)
    (x : K k m) (y : K E n) :
    finiteExtensionNorm k E (m + n)
      (product m n (map m (algebraMap k E) x) y) =
        product m n x (finiteExtensionNorm k E n y) := by
  unfold finiteExtensionNorm
  simp only [LinearMap.comp_apply]
  rw [map_product]
  have hc : (finiteNormPresentation k E).symm.toRingHom.comp (algebraMap k E) =
      algebraMap k (AdjoinRoot (finiteNormPolynomial k E).val) := by
    apply RingHom.ext
    exact (finiteNormPresentation k E).symm.commutes
  rw [← LinearMap.comp_apply (map m (finiteNormPresentation k E).symm.toRingHom),
    ← map_comp, hc, polynomialNorm_product_constants_left]

private theorem finiteExtensionNorm_degreeCongr {m n : ℕ} (h : m = n) (x : K E m) :
    finiteExtensionNorm k E n (degreeCongr h x) =
      degreeCongr h (finiteExtensionNorm k E m x) := by
  subst n
  rfl

/-- The actual norm commutes with a base-field unit in the literal final slot. -/
theorem finiteExtensionNorm_productUnit_constants_right (n : ℕ)
    (x : K E n) (b : Additive kˣ) :
    finiteExtensionNorm k E (n + 1)
      (productUnit n x (unitsLinear (algebraMap k E) b)) =
        productUnit n (finiteExtensionNorm k E n x) b := by
  have hu : unitsToOne E (unitsLinear (algebraMap k E) b) =
      map 1 (algebraMap k E) (unitsToOne k b) := by
    change symbol (fun _ => Units.map (algebraMap k E).toMonoidHom b.toMul) = _
    rw [show unitsToOne k b = symbol (fun _ => b.toMul) from rfl, map_symbol]
    rfl
  rw [productUnit_eq_signed_left, map_smul, finiteExtensionNorm_degreeCongr, hu,
    finiteExtensionNorm_product_constants_left, ← productUnit_eq_signed_left]

end MilnorK
