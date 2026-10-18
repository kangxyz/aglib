/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Residue.Restriction
public import Aglib.KTheory.MilnorK.K2.DVR.RamifiedRestriction

/-!
# Ramified restriction of actual DVR residues in every degree

A genuine local DVR map, a commuting fraction-field map, and the literal
uniformizer equation `j(π) = u * ϖ^e` give ramified restriction in every Milnor
degree. The normalized specialization retains its ramification-unit correction.
The signed recursion accounts for repeated uniformizers and the two-torsion
residue sign. No norm-residue compatibility is assumed or asserted here.
-/

@[expose] public noncomputable section

namespace MilnorK

universe u v w z

open MilnorK.K2 (DiscreteResidueData UnitReductionCompatible unitsLinear residueSign)

variable {F : Type u} {E : Type v} {κ : Type w} {κ' : Type z}
  [Field F] [Field E] [Field κ] [Field κ']

private theorem unitsLinear_sign (g : κ →+* κ') :
    unitsLinear g (residueSign κ) = residueSign κ' := by
  change Additive.ofMul (Units.map g.toMonoidHom (-1)) = Additive.ofMul (-1)
  congr 1
  apply Units.ext
  exact g.map_neg 1 |>.trans (congrArg Neg.neg g.map_one)

/-- The exact specialization correction under a field/reduction square.
Only the stated angular-component transformation is required here. -/
theorem specialize_restrict_twist (d : DiscreteResidueData F κ)
    (d' : DiscreteResidueData E κ') (hd : UnitReductionCompatible d)
    (hd' : UnitReductionCompatible d') (f : F →+* E) (g : κ →+* κ')
    (c : Additive κ'ˣ)
    (hunit : ∀ a, d'.unitPart (unitsLinear f a) = unitsLinear g (d.unitPart a) - d.value a • c)
    (n : ℕ) :
    (specialize d' hd' (n + 1)).comp (map (n + 1) f) =
      (map (n + 1) g).comp (specialize d hd (n + 1)) -
        ((productUnit n).flip c).comp ((map n g).comp (residue d hd n)) := by
  induction n with
  | zero =>
    apply linearMap_ext
    intro a
    have ha : a = fun _ => a 0 := funext (fun i => congrArg a (Fin.ext (by omega)))
    have hempty : Units.map g.toMonoidHom ∘ (Fin.elim0 : SymbolTuple κ 0) = Fin.elim0 :=
      funext (fun i => Fin.elim0 i)
    rw [ha]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.flip_apply,
      map_symbol, specialize_symbol, residue_symbol, residueSymbol_zero, map_smul,
      hempty, productUnit_empty]
    change unitsToOne κ' (d'.unitPart (unitsLinear f (Additive.ofMul (a 0)))) =
      unitsToOne κ' (unitsLinear g (d.unitPart (Additive.ofMul (a 0)))) -
        d.value (Additive.ofMul (a 0)) • unitsToOne κ' c
    rw [hunit, map_sub, map_smul]
  | succ n ih =>
    apply linearMap_ext
    intro a
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.flip_apply]
    rw [← Fin.snoc_init_self a, map_symbol, Fin.comp_snoc,
      specialize_symbol_snoc, specialize_symbol_snoc, map_productUnit,
      residue_symbol_snoc, map_sub, map_smul, map_productUnit]
    have hi := LinearMap.congr_fun ih (symbol (Fin.init a))
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.flip_apply, map_symbol] at hi
    rw [hi]
    change productUnit (n + 1) _ (d'.unitPart
      (unitsLinear f (Additive.ofMul (a (Fin.last (n + 1)))))) = _
    rw [hunit]
    simp only [unitPartTwist_apply, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, unitsLinear_sign]
    rw [productUnit_pair_skew n
      (map n g (residue d hd n (symbol (Fin.init a)))) c
      (unitsLinear g (d.unitPart (Additive.ofMul (a (Fin.last (n + 1)))))),
      productUnit_pair_self]
    module

private theorem residue_scaling_algebra (n : ℕ) (x : K κ' n) (s : K κ' (n + 1))
    (a c : Additive κ'ˣ) (v e : ℤ) :
    (e * v) • (s - productUnit n x c) -
        productUnit n (e • x) (a - v • c - (e * v) • residueSign κ') =
      e • (v • s - productUnit n x (a - v • residueSign κ')) := by
  have htwo : productUnit n x (residueSign κ') + productUnit n x (residueSign κ') = 0 := by
    rw [← map_add, MilnorK.K2.residueSign_add_self, map_zero]
  calc
    _ = e • (v • s - productUnit n x (a - v • residueSign κ')) +
        v • ((e * e - e) • productUnit n x (residueSign κ')) := by
      simp only [map_sub, map_smul, LinearMap.smul_apply]
      module
    _ = _ := by
      rw [MilnorK.K2.square_sub_smul_eq_zero _ htwo e, smul_zero, add_zero]

/-- Ramification scales the actual tame residue, with the full signed recursion
and its two-torsion sign contribution retained. -/
theorem residue_restrict_ramified (d : DiscreteResidueData F κ)
    (d' : DiscreteResidueData E κ') (hd : UnitReductionCompatible d)
    (hd' : UnitReductionCompatible d') (f : F →+* E) (g : κ →+* κ')
    (e : ℤ) (c : Additive κ'ˣ)
    (hvalue : ∀ a, d'.value (unitsLinear f a) = e * d.value a)
    (hunit : ∀ a, d'.unitPart (unitsLinear f a) = unitsLinear g (d.unitPart a) - d.value a • c)
    (n : ℕ) :
    (residue d' hd' n).comp (map (n + 1) f) =
      e • ((map n g).comp (residue d hd n)) := by
  induction n with
  | zero =>
    apply linearMap_ext
    intro a
    have hempty : Units.map g.toMonoidHom ∘ (Fin.elim0 : SymbolTuple κ 0) = Fin.elim0 :=
      funext (fun i => Fin.elim0 i)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_symbol,
      residue_symbol, residueSymbol_zero, map_smul, hempty]
    change d'.value (unitsLinear f (Additive.ofMul (a 0))) • symbol Fin.elim0 = _
    rw [hvalue, mul_smul]
  | succ n ih =>
    apply linearMap_ext
    intro a
    simp only [LinearMap.comp_apply, LinearMap.smul_apply]
    rw [← Fin.snoc_init_self a, map_symbol, Fin.comp_snoc,
      residue_symbol_snoc, residue_symbol_snoc, map_sub, map_smul, map_productUnit]
    have hs := LinearMap.congr_fun
      (specialize_restrict_twist d d' hd hd' f g c hunit n) (symbol (Fin.init a))
    have hr := LinearMap.congr_fun ih (symbol (Fin.init a))
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.flip_apply,
      LinearMap.smul_apply, map_symbol] at hs hr
    rw [hs, hr]
    change d'.value (unitsLinear f (Additive.ofMul (a (Fin.last (n + 1))))) • _ -
      productUnit n _ (unitPartTwist d' (residueSign κ')
        (unitsLinear f (Additive.ofMul (a (Fin.last (n + 1)))))) = _
    simp only [unitPartTwist_apply, hvalue, hunit, map_sub, map_smul, unitsLinear_sign]
    simpa only [map_sub, map_smul, LinearMap.smul_apply] using residue_scaling_algebra n
      (map n g (residue d hd n (symbol (Fin.init a))))
      (map (n + 1) g (specialize d hd (n + 1) (symbol (Fin.init a))))
      (unitsLinear g (d.unitPart (Additive.ofMul (a (Fin.last (n + 1)))))) c
      (d.value (Additive.ofMul (a (Fin.last (n + 1))))) e

namespace DVR

variable {R S K M : Type*}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field M] [Algebra S M] [IsFractionRing S M]
  (j : R →+* S) [IsLocalHom j] (f : K →+* M)
  (hf : ∀ r : R, f (algebraMap R K r) = algebraMap S M (j r))
  {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
  (u : Sˣ) (e : ℕ) (hπmap : j π = (u : S) * ϖ ^ e)

include hf hπ hϖ hπmap

/-- The all-degree tame square for an actual ramified DVR map. The integer
`e` is its literal uniformizer exponent; localness and irreducibility already
force positivity, so no independent positivity assumption is inserted. -/
theorem residue_ramified_restrict (n : ℕ) :
    (residue S M n).comp (map (n + 1) f) =
      (e : ℤ) • ((map n (IsLocalRing.ResidueField.map j)).comp (residue R K n)) := by
  rw [residue_eq R K hπ n, residue_eq S M hϖ n]
  exact residue_restrict_ramified (MilnorK.K2.DVR.data (K := K) hπ)
    (MilnorK.K2.DVR.data (K := M) hϖ) (MilnorK.K2.DVR.unitReductionCompatible hπ)
    (MilnorK.K2.DVR.unitReductionCompatible hϖ) f (IsLocalRing.ResidueField.map j)
    (e : ℤ) (-MilnorK.K2.DVR.ramificationUnitResidue u)
    (MilnorK.K2.DVR.ramified_value_map j f hf hπ hϖ u e hπmap)
    (fun a => by
      simpa only [MilnorK.K2.DVR.data, zsmul_neg, sub_neg_eq_add] using
        MilnorK.K2.DVR.ramified_unitPart_map j f hf hπ hϖ u e hπmap a) n

/-- The canonical ramified tame identity on every original quotient class. -/
theorem residue_ramified_restrict_apply (n : ℕ) (x : MilnorK.K K (n + 1)) :
    residue S M n (map (n + 1) f x) =
      (e : ℤ) • map n (IsLocalRing.ResidueField.map j) (residue R K n x) :=
  LinearMap.congr_fun (residue_ramified_restrict j f hf hπ hϖ u e hπmap n) x

/-- Specialization normalized by the stated uniformizers has its actual plus
correction by the residue of the ramification unit. This includes degree one
and the empty residue prefix; it is not a uniformizer-independent specialization. -/
theorem specialize_ramified_restrict (n : ℕ) :
    (specializeWithUniformizer S M hϖ (n + 1)).comp (map (n + 1) f) =
      (map (n + 1) (IsLocalRing.ResidueField.map j)).comp
          (specializeWithUniformizer R K hπ (n + 1)) +
        ((productUnit n).flip (MilnorK.K2.DVR.ramificationUnitResidue u)).comp
          ((map n (IsLocalRing.ResidueField.map j)).comp (residue R K n)) := by
  rw [residue_eq R K hπ n]
  have hunit (a) : (MilnorK.K2.DVR.data (K := M) hϖ).unitPart (unitsLinear f a) =
      unitsLinear (IsLocalRing.ResidueField.map j) ((MilnorK.K2.DVR.data (K := K) hπ).unitPart a) -
        (MilnorK.K2.DVR.data (K := K) hπ).value a •
          (-MilnorK.K2.DVR.ramificationUnitResidue u) := by
    simpa only [MilnorK.K2.DVR.data, zsmul_neg, sub_neg_eq_add] using
      MilnorK.K2.DVR.ramified_unitPart_map j f hf hπ hϖ u e hπmap a
  have h := specialize_restrict_twist (MilnorK.K2.DVR.data (K := K) hπ)
    (MilnorK.K2.DVR.data (K := M) hϖ) (MilnorK.K2.DVR.unitReductionCompatible hπ)
    (MilnorK.K2.DVR.unitReductionCompatible hϖ) f (IsLocalRing.ResidueField.map j)
    (-MilnorK.K2.DVR.ramificationUnitResidue u) hunit n
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun h x
  simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.flip_apply, map_neg, LinearMap.neg_apply, sub_neg_eq_add,
    specializeWithUniformizer, residueWithUniformizer] using hx

end DVR

end MilnorK
