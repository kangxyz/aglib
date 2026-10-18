/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Residue.DVR
public import Aglib.KTheory.MilnorK.K3.DVRRestriction

/-!
# Unramified restriction of actual DVR residues in every Milnor degree

A local homomorphism of actual DVRs and a commuting fraction-field map give
the residue square in every degree when a source uniformizer remains
irreducible. The integer-order and unit-part comparisons are the existing
degree-independent consequences of normalized ring-unit lifts. Induction
through the full signed residue recursion then proves the square on the
actual all-degree Milnor quotients, with no bound on symbol valuations.

This is restriction with ramification index one. It is neither a norm-residue
square nor a statement of primitive-element independence of any norm.
-/

@[expose] public noncomputable section

namespace MilnorK

universe u v w z

open MilnorK.K2 (DiscreteResidueData UnitReductionCompatible unitsLinear residueSign)

variable {F : Type u} {E : Type v} [Field F] [Field E]

/-- Right multiplication by a unit is natural for actual field maps. -/
theorem map_productUnit (f : F →+* E) (n : ℕ) (x : K F n) (a : Additive Fˣ) :
    map (n + 1) f (productUnit n x a) =
      productUnit n (map n f x) (unitsLinear f a) := by
  have h : (map (n + 1) f).comp ((productUnit n).flip a) =
      ((productUnit n).flip (unitsLinear f a)).comp (map n f) := by
    apply linearMap_ext
    intro b
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, productUnit_symbol, map_symbol]
    congr 1
    exact Fin.comp_snoc (Units.map f.toMonoidHom) b a.toMul
  exact LinearMap.congr_fun h x

private theorem unitsLinear_residueSign (f : F →+* E) :
    unitsLinear f (residueSign F) = residueSign E := by
  change Additive.ofMul (Units.map f.toMonoidHom (-1)) = Additive.ofMul (-1)
  congr 1
  apply Units.ext
  change f (-1) = -1
  simp

variable {κ : Type w} {κ' : Type z} [Field κ] [Field κ']

/-- The actual specialization square follows from the unit-part comparison. -/
theorem specialize_restrict (d : DiscreteResidueData F κ) (d' : DiscreteResidueData E κ')
    (hd : UnitReductionCompatible d) (hd' : UnitReductionCompatible d')
    (f : F →+* E) (g : κ →+* κ')
    (hunit : ∀ a, d'.unitPart (unitsLinear f a) = unitsLinear g (d.unitPart a))
    (n : ℕ) :
    (map n g).comp (specialize d hd n) = (specialize d' hd' n).comp (map n f) := by
  apply linearMap_ext
  intro a
  simp only [LinearMap.comp_apply, specialize_symbol, map_symbol]
  congr 1
  funext i
  exact (congrArg Additive.toMul (hunit (Additive.ofMul (a i)))).symm

/-- Compatible valuations and unit parts preserve the complete signed residue
recursion. Actual DVR hypotheses deriving these identities are supplied below. -/
theorem residue_restrict (d : DiscreteResidueData F κ) (d' : DiscreteResidueData E κ')
    (hd : UnitReductionCompatible d) (hd' : UnitReductionCompatible d')
    (f : F →+* E) (g : κ →+* κ')
    (hvalue : ∀ a, d'.value (unitsLinear f a) = d.value a)
    (hunit : ∀ a, d'.unitPart (unitsLinear f a) = unitsLinear g (d.unitPart a))
    (n : ℕ) :
    (map n g).comp (residue d hd n) = (residue d' hd' n).comp (map (n + 1) f) := by
  have htwist (a : Additive Fˣ) :
      unitPartTwist d' (residueSign κ') (unitsLinear f a) =
        unitsLinear g (unitPartTwist d (residueSign κ) a) := by
    simp only [unitPartTwist_apply, hunit, hvalue, map_sub, map_smul,
      unitsLinear_residueSign]
  induction n with
  | zero =>
      apply linearMap_ext
      intro a
      simp only [LinearMap.comp_apply, map_symbol, residue_symbol, residueSymbol_zero,
        map_smul]
      change d.value (Additive.ofMul (a 0)) •
          symbol (Units.map g.toMonoidHom ∘ Fin.elim0) =
        d'.value (unitsLinear f (Additive.ofMul (a 0))) • symbol Fin.elim0
      rw [hvalue]
      congr 2
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      apply linearMap_ext
      intro a
      simp only [LinearMap.comp_apply]
      rw [← Fin.snoc_init_self a, residue_symbol_snoc, map_symbol]
      have hs := LinearMap.congr_fun (specialize_restrict d d' hd hd' f g hunit (n + 1))
        (symbol (Fin.init a))
      have hr := LinearMap.congr_fun ih (symbol (Fin.init a))
      simp only [LinearMap.comp_apply] at hs hr
      rw [Fin.comp_snoc, residue_symbol_snoc, map_sub, map_smul, map_productUnit, hs, hr]
      change d.value (Additive.ofMul (a (Fin.last (n + 1)))) • _ -
          productUnit n _ (unitsLinear g
            (unitPartTwist d (residueSign κ) (Additive.ofMul (a (Fin.last (n + 1)))))) =
        d'.value (unitsLinear f (Additive.ofMul (a (Fin.last (n + 1))))) • _ -
          productUnit n _ (unitPartTwist d' (residueSign κ')
            (unitsLinear f (Additive.ofMul (a (Fin.last (n + 1))))))
      simp only [hvalue, htwist, map_symbol]

namespace DVR

variable {R S L M : Type*}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field L] [Algebra R L] [IsFractionRing R L]
  [Field M] [Algebra S M] [IsFractionRing S M]
  (j : R →+* S) [IsLocalHom j] (f : L →+* M)
  (hf : ∀ r : R, f (algebraMap R L r) = algebraMap S M (j r))

include hf

/-- For every degree, a genuine unramified local map preserves the canonical
tame residue. The unit-part and integer-order comparisons are proved from
the local and fraction-field maps, rather than assumed as additional data. -/
theorem residue_restrict {π : R} (hπ : Irreducible π) (hjπ : Irreducible (j π)) (n : ℕ) :
    (map n (IsLocalRing.ResidueField.map j)).comp (residue R L n) =
      (residue S M n).comp (map (n + 1) f) := by
  rw [residue_eq R L hπ n, residue_eq S M hjπ n]
  exact MilnorK.residue_restrict (MilnorK.K2.DVR.data (K := L) hπ)
    (MilnorK.K2.DVR.data (K := M) hjπ) (MilnorK.K2.DVR.unitReductionCompatible hπ)
    (MilnorK.K2.DVR.unitReductionCompatible hjπ) f (IsLocalRing.ResidueField.map j)
    (MilnorK.K3.DVR.value_map j f hf hπ hjπ) (MilnorK.K3.DVR.unitPart_map j f hf hπ hjπ) n

/-- The canonical unramified square evaluated on any quotient class. -/
theorem residue_restrict_apply {π : R} (hπ : Irreducible π) (hjπ : Irreducible (j π))
    (n : ℕ) (x : K L (n + 1)) :
    map n (IsLocalRing.ResidueField.map j) (residue R L n x) =
      residue S M n (map (n + 1) f x) :=
  LinearMap.congr_fun (residue_restrict j f hf hπ hjπ n) x

end DVR

end MilnorK
