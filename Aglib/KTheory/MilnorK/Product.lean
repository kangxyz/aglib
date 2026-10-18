/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.LowDegree
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Products on the all-degree Milnor presentation

Concatenation of ordered tuples descends through both actual Milnor relation
submodules. It gives a bilinear product in arbitrary nonnegative degrees and
arbitrary characteristic. Its symbol formula, field naturality, degree-zero
unit, and associativity are proved here. The latter two statements explicitly
transport between equal natural-number degrees; no strict identification of
unequal `Fin` types is used.
-/

@[expose] public section

noncomputable section

namespace Fin

variable {α : Type*} {m n : ℕ}

/-- Updating the left block of a concatenated tuple updates its corresponding index. -/
theorem append_update_left (a : Fin m → α) (b : Fin n → α) (i : Fin m) (x : α) :
    append (Function.update a i x) b = Function.update (append a b) (castAdd n i) x := by
  classical
  funext k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · by_cases h : j = i
    · subst j
      simp
    · have h' : castAdd n j ≠ castAdd n i :=
        fun e => h (Fin.ext (congrArg (fun k : Fin (m + n) => k.val) e))
      simp [h, h']
  · have h' : natAdd m j ≠ castAdd n i := by
      intro e
      have := congrArg Fin.val e
      simp only [val_natAdd, val_castAdd] at this
      omega
    simp [h']

/-- Updating the right block of a concatenated tuple updates its corresponding index. -/
theorem append_update_right (a : Fin m → α) (b : Fin n → α) (i : Fin n) (x : α) :
    append a (Function.update b i x) = Function.update (append a b) (natAdd m i) x := by
  classical
  funext k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · have h' : castAdd n j ≠ natAdd m i := by
      intro e
      have := congrArg Fin.val e
      simp only [val_natAdd, val_castAdd] at this
      omega
    simp [h']
  · by_cases h : j = i
    · subst j
      simp
    · have h' : natAdd m j ≠ natAdd m i := by
        intro e
        apply h
        apply Fin.ext
        have := congrArg Fin.val e
        simpa only [val_natAdd, Nat.add_right_inj] using this
      simp [h, h']

end Fin

namespace MilnorK

universe u v

variable {F : Type u} [Field F] {m n p : ℕ}

/-- Transport in the degree, retaining the actual quotient presentation. -/
def degreeCongr (h : m = n) : K F m ≃ₗ[ℤ] K F n := by
  subst n
  exact LinearEquiv.refl ℤ (K F m)

@[simp] theorem degreeCongr_refl (x : K F m) : degreeCongr rfl x = x := rfl

/-- Degree transport on symbols is precisely transport of the finite index type. -/
@[simp] theorem degreeCongr_symbol (h : m = n) (a : SymbolTuple F m) :
    degreeCongr h (symbol a) = symbol (a ∘ Fin.cast h.symm) := by
  subst n
  rfl

/-- Transports compose as the corresponding equalities of degrees. -/
theorem degreeCongr_trans (h : m = n) (h' : n = p) (x : K F m) :
    degreeCongr h' (degreeCongr h x) = degreeCongr (h.trans h') x := by
  subst n
  subst p
  rfl

/-- With the left tuple fixed, concatenation descends through all right-hand relations. -/
def productSymbolLeft (a : SymbolTuple F m) : K F n →ₗ[ℤ] K F (m + n) :=
  lift (fun b => symbol (Fin.append a b)) {
    map_mul := by
      intro b i c d
      simp only [Fin.append_update_right]
      exact symbol_mul _ _ _ _
    steinberg := by
      intro b i j hij h
      apply steinberg _ (Fin.natAdd m i) (Fin.natAdd m j)
      · simp only [Fin.val_natAdd]
        omega
      · simpa only [Fin.append_right] using h }

@[simp] theorem productSymbolLeft_symbol (a : SymbolTuple F m) (b : SymbolTuple F n) :
    productSymbolLeft a (symbol b) = symbol (Fin.append a b) := lift_symbol _ _ _

/-- The actual bilinear Milnor product, obtained by descending both quotient relations. -/
def product (m n : ℕ) : K F m →ₗ[ℤ] K F n →ₗ[ℤ] K F (m + n) :=
  lift productSymbolLeft {
    map_mul := by
      intro a i b c
      apply linearMap_ext
      intro d
      simp only [LinearMap.add_apply, productSymbolLeft_symbol, Fin.append_update_left]
      exact symbol_mul _ _ _ _
    steinberg := by
      intro a i j hij h
      apply linearMap_ext
      intro b
      simp only [productSymbolLeft_symbol, LinearMap.zero_apply]
      apply steinberg _ (Fin.castAdd n i) (Fin.castAdd n j) hij
      simpa only [Fin.append_left] using h }

/-- Multiplication of quotient symbols is ordered concatenation. -/
@[simp] theorem product_symbol (a : SymbolTuple F m) (b : SymbolTuple F n) :
    product m n (symbol a) (symbol b) = symbol (Fin.append a b) := by
  simp [product]

/-- Additivity holds in the first quotient class, not only on symbols. -/
theorem product_add_left (x x' : K F m) (y : K F n) :
    product m n (x + x') y = product m n x y + product m n x' y := by
  simp only [map_add, LinearMap.add_apply]

/-- Additivity holds in the second quotient class. -/
theorem product_add_right (x : K F m) (y y' : K F n) :
    product m n x (y + y') = product m n x y + product m n x y' := map_add _ _ _

variable {E : Type v} [Field E]

/-- Field maps commute with multiplication in any pair of degrees. -/
theorem map_product (f : F →+* E) (x : K F m) (y : K F n) :
    map (m + n) f (product m n x y) = product m n (map m f x) (map n f y) := by
  have h : (product m n).compr₂ (map (m + n) f) =
      (product m n).compl₁₂ (map m f) (map n f) := by
    apply linearMap_ext
    intro a
    apply linearMap_ext
    intro b
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, product_symbol, map_symbol]
    congr 1
    funext i
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;> simp
  exact LinearMap.congr_fun₂ h x y

/-- The empty symbol is a left unit after the stated degree transport. -/
theorem product_empty_left (x : K F n) :
    degreeCongr (Nat.zero_add n) (product 0 n (symbol Fin.elim0) x) = x := by
  have h : (degreeCongr (Nat.zero_add n)).toLinearMap.comp
      (product 0 n (symbol (F := F) Fin.elim0)) = LinearMap.id := by
    apply linearMap_ext
    intro a
    simp only [LinearMap.comp_apply, product_symbol, LinearEquiv.coe_coe, degreeCongr_symbol,
      Fin.elim0_append, LinearMap.id_apply]
    congr 1
  exact LinearMap.congr_fun h x

/-- The empty symbol is a right unit after the stated degree transport. -/
theorem product_empty_right (x : K F m) :
    degreeCongr (Nat.add_zero m) (product m 0 x (symbol Fin.elim0)) = x := by
  have h : (degreeCongr (Nat.add_zero m)).toLinearMap.comp
      ((product m 0).flip (symbol (F := F) Fin.elim0)) = LinearMap.id := by
    apply linearMap_ext
    intro a
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, product_symbol,
      LinearEquiv.coe_coe, degreeCongr_symbol, Fin.append_elim0, LinearMap.id_apply]
    congr 1
  exact LinearMap.congr_fun h x

/-- Every degree-zero class acts on the left by its canonical integer value. -/
theorem product_zero_left (z : K F 0) (x : K F n) :
    degreeCongr (Nat.zero_add n) (product 0 n z x) = zeroEquiv F z • x := by
  have hz : z = zeroEquiv F z • symbol Fin.elim0 :=
    ((zeroEquiv F).symm_apply_apply z).symm
  rw [hz, map_smul, LinearMap.smul_apply, map_smul, product_empty_left]
  simp

/-- Every degree-zero class acts on the right by its canonical integer value. -/
theorem product_zero_right (x : K F m) (z : K F 0) :
    degreeCongr (Nat.add_zero m) (product m 0 x z) = zeroEquiv F z • x := by
  have hz : z = zeroEquiv F z • symbol Fin.elim0 :=
    ((zeroEquiv F).symm_apply_apply z).symm
  rw [hz, map_smul, map_smul, product_empty_right]
  simp

/-- Associativity with the explicit reassociation of degree and finite coordinates. -/
theorem product_assoc (x : K F m) (y : K F n) (z : K F p) :
    degreeCongr (Nat.add_assoc m n p) (product (m + n) p (product m n x y) z) =
      product m (n + p) x (product n p y z) := by
  let t : K F ((m + n) + p) →ₗ[ℤ] K F (m + (n + p)) :=
    (degreeCongr (Nat.add_assoc m n p)).toLinearMap
  have h : (product m n).compr₂ ((product (m + n) p).compr₂ t) =
      (LinearMap.llcomp ℤ (K F p) (K F (n + p)) (K F (m + (n + p)))).compl₁₂
        (product m (n + p)) (product n p) := by
    apply linearMap_ext
    intro a
    apply linearMap_ext
    intro b
    apply linearMap_ext
    intro c
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.llcomp_apply,
      product_symbol,
      t, LinearEquiv.coe_coe, degreeCongr_symbol]
    congr 1
    rw [Fin.append_assoc]
    funext i
    simp
  exact LinearMap.congr_fun (LinearMap.congr_fun₂ h x y) z

end MilnorK
