/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Residue.DVR

/-!
# Left local-unit projection formula for Milnor tame residues

The last-slot residue commutes with multiplication on the left by an actual
local-unit symbol. The other factor is an arbitrary Milnor class, so its
coordinates may have negative valuations and repeated uniformizers. The DVR
version reduces the ring units by the literal residue homomorphism.
-/

@[expose] public noncomputable section

namespace MilnorK

universe u v w

variable {F : Type u} [Field F] {m n : ℕ}

/-- Appending one unit associates with the actual graded product. The degrees
`(m + n) + 1` and `m + (n + 1)` are definitionally equal. -/
theorem product_productUnit (x : K F m) (y : K F n) (b : Additive Fˣ) :
    productUnit (m + n) (product m n x y) b =
      product m (n + 1) x (productUnit n y b) := by
  exact product_assoc x y (unitsToOne F b)

variable {L : Type u} {κ : Type v} [Field L] [Field κ]

open MilnorK.K2 (DiscreteResidueData UnitReductionCompatible)

/-- Unit-part specialization preserves products, despite not being induced by a
field homomorphism. -/
theorem specialize_product (d : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (x : K L m) (y : K L n) :
    specialize d hd (m + n) (product m n x y) =
      product m n (specialize d hd m x) (specialize d hd n y) := by
  have h : (product m n).compr₂ (specialize d hd (m + n)) =
      (product m n).compl₁₂ (specialize d hd m) (specialize d hd n) := by
    apply linearMap_ext
    intro a
    apply linearMap_ext
    intro b
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, product_symbol,
      specialize_symbol]
    congr 1
    funext i
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;> simp
  exact LinearMap.congr_fun₂ h x y

/-- An arbitrary last coordinate after local units contributes its signed
integer valuation, including zero and negative valuations. -/
theorem residue_symbol_snoc_units (d : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (m : ℕ) (a : SymbolTuple L m)
    (ha : ∀ i, d.value (Additive.ofMul (a i)) = 0) (b : Lˣ) :
    residue d hd m (symbol (Fin.snoc a b)) =
      d.value (Additive.ofMul b) • specialize d hd m (symbol a) := by
  cases m with
  | zero =>
      rw [residue_symbol, residueSymbol_zero, specialize_symbol]
      congr 1
      congr 1
      funext i
      exact Fin.elim0 i
  | succ m =>
      rw [residue_symbol_snoc, residue_symbol_units d hd m a ha,
        map_zero, LinearMap.zero_apply, sub_zero]

/-- The left local-unit product formula first on symbols. No valuation
restriction is imposed on the right symbol. -/
theorem residue_product_symbol_units_left (d : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (m n : ℕ) (a : SymbolTuple L m)
    (ha : ∀ i, d.value (Additive.ofMul (a i)) = 0) (b : SymbolTuple L (n + 1)) :
    residue d hd (m + n) (product m (n + 1) (symbol a) (symbol b)) =
      product m n (specialize d hd m (symbol a)) (residue d hd n (symbol b)) := by
  induction n with
  | zero =>
      change residue d hd m (product m 1 (symbol a) (symbol b)) = _
      rw [product_symbol, Fin.append_right_eq_snoc, residue_symbol_snoc_units d hd m a ha,
        residue_symbol, residueSymbol_zero, map_smul]
      exact congrArg (d.value (Additive.ofMul (b 0)) • ·)
        (product_empty_right (specialize d hd m (symbol a))).symm
  | succ n ih =>
      have hb : b = Fin.snoc (Fin.init b) (b (Fin.last (n + 1))) :=
        (Fin.snoc_init_self b).symm
      rw [hb, product_symbol, Fin.append_snoc]
      change residue d hd ((m + n) + 1)
        (symbol (Fin.snoc (@Fin.append m (n + 1) Lˣ a (Fin.init b))
          (b (Fin.last (n + 1))))) = _
      rw [residue_symbol_snoc d hd (m + n), residue_symbol_snoc d hd n]
      have hs := specialize_product d hd (symbol a) (symbol (Fin.init b))
      change specialize d hd (m + n + 1)
        (product m (n + 1) (symbol a) (symbol (Fin.init b))) = _ at hs
      rw [← product_symbol, hs, ih (Fin.init b), product_productUnit, map_sub, map_smul]

/-- The projection formula for a local-unit symbol and an arbitrary right-hand
Milnor class, descended by generation of the actual quotient by symbols. -/
theorem residue_product_units_left (d : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (m n : ℕ) (a : SymbolTuple L m)
    (ha : ∀ i, d.value (Additive.ofMul (a i)) = 0) (z : K L (n + 1)) :
    residue d hd (m + n) (product m (n + 1) (symbol a) z) =
      product m n (symbol (fun i => (d.unitPart (Additive.ofMul (a i))).toMul))
        (residue d hd n z) := by
  have h : (residue d hd (m + n)).comp (product m (n + 1) (symbol a)) =
      (product m n (specialize d hd m (symbol a))).comp (residue d hd n) := by
    apply linearMap_ext
    intro b
    exact residue_product_symbol_units_left d hd m n a ha b
  simpa only [LinearMap.comp_apply, specialize_symbol] using LinearMap.congr_fun h z

/-- The same projection formula displays the input reassociation of degrees
explicitly. -/
theorem residue_product_units_left_degreeCongr (d : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (m n : ℕ) (a : SymbolTuple L m)
    (ha : ∀ i, d.value (Additive.ofMul (a i)) = 0) (z : K L (n + 1)) :
    residue d hd (m + n)
      (degreeCongr (Nat.add_assoc m n 1).symm (product m (n + 1) (symbol a) z)) =
      product m n (symbol (fun i => (d.unitPart (Additive.ofMul (a i))).toMul))
        (residue d hd n z) :=
  residue_product_units_left d hd m n a ha z

namespace DVR

variable (R L : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]

/-- The canonical actual-DVR residue is linear over a left symbol of actual
ring units, reduced by the literal residue map. -/
theorem residue_product_ring_units_left (m n : ℕ) (a : Fin m → Rˣ)
    (z : K L (n + 1)) :
    residue R L (m + n)
      (degreeCongr (Nat.add_assoc m n 1).symm
        (product m (n + 1) (symbol (MilnorK.K2.DVR.fieldUnits R L ∘ a)) z)) =
      product m n (symbol (Units.map (IsLocalRing.residue R).toMonoidHom ∘ a))
        (residue R L n z) := by
  have h := residue_product_units_left_degreeCongr (MilnorK.K2.DVR.chosenData R L)
    (MilnorK.K2.DVR.chosenData_unitReductionCompatible R L) m n
    (MilnorK.K2.DVR.fieldUnits R L ∘ a)
    (fun i => MilnorK.K2.DVR.value_fieldUnits R L (a i)) z
  refine h.trans ?_
  congr 2
  apply congrArg symbol
  funext i
  exact MilnorK.K2.DVR.unitResidue_fieldUnits
    (IsDiscreteValuationRing.exists_irreducible R).choose_spec (a i)

/-- A field mapping into the actual valuation ring acts by arbitrary Milnor
classes. Its elements are embedded through genuine ring units, so no
unrestricted fraction-field factor is declared to have valuation zero. -/
theorem residue_product_base_field_left {F : Type w} [Field F] (f : F →+* R)
    (m n : ℕ) (x : K F m) (z : K L (n + 1)) :
    residue R L (m + n)
      (degreeCongr (Nat.add_assoc m n 1).symm
        (product m (n + 1) (map m ((algebraMap R L).comp f) x) z)) =
      product m n (map m ((IsLocalRing.residue R).comp f) x) (residue R L n z) := by
  have h : (residue R L (m + n)).comp
      (((product m (n + 1)).flip z).comp (map m ((algebraMap R L).comp f))) =
      ((product m n).flip (residue R L n z)).comp
        (map m ((IsLocalRing.residue R).comp f)) := by
    apply linearMap_ext
    intro a
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, map_symbol]
    exact residue_product_ring_units_left R L m n (Units.map f.toMonoidHom ∘ a) z
  exact LinearMap.congr_fun h x

end DVR

end MilnorK
