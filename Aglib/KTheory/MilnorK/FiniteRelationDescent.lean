/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.RestrictionKernel
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Finite descent of actual Milnor relations

A relation over an algebraic field extension is already a relation over a finite
intermediate field. The proof uses the original free symbol presentation and
its actual defining relation span. No norm or special-field closure is used in
the descent step. Separability is retained for the subsequent degree-retraction
and prime-to-order torsion-detection consequences.
-/

@[expose] public noncomputable section

namespace MilnorK.FiniteDescent

variable {k E L : Type*} [Field k] [Field E] [Field L]

/-- The literal coordinatewise map on the original free symbol presentation. -/
def presentationMap (n : ℕ) (φ : k →+* E) : Presentation k n →ₗ[ℤ] Presentation E n :=
  Finsupp.lmapDomain ℤ ℤ (fun a => Units.map φ.toMonoidHom ∘ a)

@[simp] theorem presentationMap_single (n : ℕ) (φ : k →+* E)
    (a : SymbolTuple k n) (z : ℤ) :
    presentationMap n φ (Finsupp.single a z) =
      Finsupp.single (Units.map φ.toMonoidHom ∘ a) z :=
  Finsupp.mapDomain_single

/-- The presentation map is compatible with the actual Milnor quotient map. -/
theorem mkQ_presentationMap (n : ℕ) (φ : k →+* E) (x : Presentation k n) :
    (relationSpan E n).mkQ (presentationMap n φ x) =
      map n φ ((relationSpan k n).mkQ x) := by
  have h : (relationSpan E n).mkQ.comp (presentationMap n φ) =
      (map n φ).comp (relationSpan k n).mkQ := by
    apply Finsupp.lhom_ext
    intro a z
    have hz : Finsupp.single a z = z • Finsupp.single a (1 : ℤ) := by simp
    rw [hz]
    simp only [LinearMap.map_smul, LinearMap.comp_apply, presentationMap_single]
    exact congrArg (z • ·) (map_symbol n φ a).symm
  exact LinearMap.congr_fun h x

/-- Field embeddings remain injective on the free symbol presentation. -/
theorem presentationMap_injective (n : ℕ) (φ : k →+* E) :
    Function.Injective (presentationMap n φ) := by
  apply Finsupp.mapDomain_injective
  intro a b hab
  funext i
  exact Units.map_injective φ.injective (congrFun hab i)

/-- Composition holds before taking the defining quotient. -/
theorem presentationMap_comp (n : ℕ) (φ : k →+* E) (ψ : E →+* L) :
    presentationMap n (ψ.comp φ) =
      (presentationMap n ψ).comp (presentationMap n φ) := by
  apply Finsupp.lhom_ext
  intro a z
  simp only [LinearMap.comp_apply, presentationMap_single]
  rfl

/-- Every actual relation is preserved by the literal presentation map. -/
theorem presentationMap_mem_relationSpan (n : ℕ) (φ : k →+* E)
    (x : Presentation k n) (hx : x ∈ relationSpan k n) :
    presentationMap n φ x ∈ relationSpan E n := by
  apply (Submodule.Quotient.mk_eq_zero _).mp
  change (relationSpan E n).mkQ (presentationMap n φ x) = 0
  have hzero : (relationSpan k n).mkQ x = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hx
  rw [mkQ_presentationMap, hzero, map_zero]

variable (k E) [Algebra k E] [Algebra.IsAlgebraic k E]

/-- A finite tuple of actual units is defined over one finite intermediate field. -/
theorem exists_finite_unit_tuple (n : ℕ) (a : SymbolTuple E n) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      ∃ b : SymbolTuple S n, Units.map S.val.toRingHom.toMonoidHom ∘ b = a := by
  let S := IntermediateField.adjoin k (Set.range fun i => (a i : E))
  have hfin : FiniteDimensional k S := IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  have ha : ∀ i, (a i : E) ∈ S := fun i =>
    IntermediateField.subset_adjoin k _ ⟨i, rfl⟩
  let b : SymbolTuple S n := fun i => Units.mk0 ⟨(a i : E), ha i⟩ (by
    intro hz
    exact (a i).ne_zero (congrArg (fun x : S => (x : E)) hz))
  refine ⟨S, hfin, b, ?_⟩
  funext i
  apply Units.ext
  rfl

/-- Every defining multiplicativity or Steinberg relation has a genuine
relation preimage over a finite intermediate field. -/
theorem exists_finite_relationGenerator (n : ℕ) (r : Presentation E n)
    (hr : r ∈ relationGenerators E n) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      ∃ s : Presentation S n, s ∈ relationSpan S n ∧
        presentationMap n S.val.toRingHom s = r := by
  rcases hr with ⟨a, i, b, c, rfl⟩ | ⟨a, i, j, hij, hsum, rfl⟩
  · let A : SymbolTuple E (n + 2) := Fin.snoc (Fin.snoc a b) c
    obtain ⟨S, hS, B, hB⟩ := exists_finite_unit_tuple k E (n + 2) A
    let a' : SymbolTuple S n := fun j => B j.castSucc.castSucc
    let b' : Sˣ := B (Fin.last n).castSucc
    let c' : Sˣ := B (Fin.last (n + 1))
    have ha' : Units.map S.val.toRingHom.toMonoidHom ∘ a' = a := by
      funext j
      simpa only [Function.comp_apply, a', A, Fin.snoc_castSucc] using
        congrFun hB j.castSucc.castSucc
    have hb' : Units.map S.val.toRingHom.toMonoidHom b' = b := by
      simpa only [Function.comp_apply, b', A, Fin.snoc_castSucc, Fin.snoc_last] using
        congrFun hB (Fin.last n).castSucc
    have hc' : Units.map S.val.toRingHom.toMonoidHom c' = c := by
      simpa only [Function.comp_apply, c', A, Fin.snoc_last] using
        congrFun hB (Fin.last (n + 1))
    refine ⟨S, hS, Finsupp.single (Function.update a' i (b' * c')) 1 -
      Finsupp.single (Function.update a' i b') 1 -
      Finsupp.single (Function.update a' i c') 1,
      Submodule.subset_span (Or.inl ⟨a', i, b', c', rfl⟩), ?_⟩
    simp only [map_sub, presentationMap_single, Function.comp_update, map_mul, ha', hb', hc']
  · obtain ⟨S, hS, b, hb⟩ := exists_finite_unit_tuple k E n a
    have hsum' : (b i : S) + (b j : S) = 1 := by
      apply S.val.injective
      change ((b i : S) : E) + ((b j : S) : E) = 1
      have hi := congrArg Units.val (congrFun hb i)
      have hj := congrArg Units.val (congrFun hb j)
      change ((b i : S) : E) = (a i : E) at hi
      change ((b j : S) : E) = (a j : E) at hj
      rw [hi, hj]
      exact hsum
    refine ⟨S, hS, Finsupp.single b 1,
      Submodule.subset_span (Or.inr ⟨b, i, j, hij, hsum', rfl⟩), ?_⟩
    rw [presentationMap_single, hb]

/-- Every element of the actual defining relation span descends to a relation
over a finite intermediate field. Finite composita combine the witnesses. -/
theorem exists_finite_relation (n : ℕ) (r : Presentation E n)
    (hr : r ∈ relationSpan E n) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      ∃ s : Presentation S n, s ∈ relationSpan S n ∧
        presentationMap n S.val.toRingHom s = r := by
  induction hr using Submodule.span_induction with
  | mem r hr => exact exists_finite_relationGenerator k E n r hr
  | zero =>
    exact ⟨⊥, inferInstance, 0, (relationSpan _ n).zero_mem, map_zero _⟩
  | add r t _ _ ihr iht =>
    obtain ⟨S, hS, s, hs, hsr⟩ := ihr
    obtain ⟨T, hT, u, hu, hut⟩ := iht
    let := hS
    let := hT
    let U := S ⊔ T
    let iS : S →+* U := (IntermediateField.inclusion le_sup_left).toRingHom
    let iT : T →+* U := (IntermediateField.inclusion le_sup_right).toRingHom
    have hsU : presentationMap n U.val.toRingHom (presentationMap n iS s) = r := by
      rw [← LinearMap.comp_apply, ← presentationMap_comp]
      exact hsr
    have huU : presentationMap n U.val.toRingHom (presentationMap n iT u) = t := by
      rw [← LinearMap.comp_apply, ← presentationMap_comp]
      exact hut
    refine ⟨U, inferInstance, presentationMap n iS s + presentationMap n iT u,
      (relationSpan U n).add_mem (presentationMap_mem_relationSpan n iS s hs)
        (presentationMap_mem_relationSpan n iT u hu), ?_⟩
    rw [map_add, hsU, huU]
  | smul z r _ ih =>
    obtain ⟨S, hS, s, hs, hsr⟩ := ih
    refine ⟨S, hS, z • s, (relationSpan S n).smul_mem z hs, ?_⟩
    rw [LinearMap.map_smul, hsr]

/-- Vanishing after algebraic extension already occurs over some actual finite
intermediate field. Only algebraicity, not separability, is needed here. -/
theorem exists_finite_intermediate_map_eq_zero (n : ℕ) (x : K k n)
    (hx : map n (algebraMap k E) x = 0) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      map n (algebraMap k S) x = 0 := by
  obtain ⟨a, rfl⟩ := (relationSpan k n).mkQ_surjective x
  have ha : presentationMap n (algebraMap k E) a ∈ relationSpan E n := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change (relationSpan E n).mkQ (presentationMap n (algebraMap k E) a) = 0
    rwa [mkQ_presentationMap]
  obtain ⟨S, hS, b, hb, hba⟩ :=
    exists_finite_relation k E n (presentationMap n (algebraMap k E) a) ha
  have hcomp : S.val.toRingHom.comp (algebraMap k S) = algebraMap k E := by
    ext c
    exact S.val.commutes c
  have hbeq : b = presentationMap n (algebraMap k S) a := by
    apply presentationMap_injective n S.val.toRingHom
    rw [hba, ← LinearMap.comp_apply, ← presentationMap_comp, hcomp]
  refine ⟨S, hS, ?_⟩
  rw [← mkQ_presentationMap, ← hbeq]
  exact (Submodule.Quotient.mk_eq_zero _).mpr hb

/-- Equality after algebraic extension is witnessed over one finite
intermediate field, on the original Milnor groups. -/
theorem exists_finite_intermediate_map_eq (n : ℕ) (x y : K k n)
    (hxy : map n (algebraMap k E) x = map n (algebraMap k E) y) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      map n (algebraMap k S) x = map n (algebraMap k S) y := by
  obtain ⟨S, hS, h⟩ := exists_finite_intermediate_map_eq_zero k E n (x - y)
    (by rw [map_sub, hxy, sub_self])
  exact ⟨S, hS, sub_eq_zero.mp (by simpa only [map_sub] using h)⟩

omit [Algebra.IsAlgebraic k E] in
/-- Separable algebraic restriction detects torsion when every finite
intermediate degree is coprime to its order bound. The degree condition is
explicit; no special extension satisfying it is constructed here. -/
theorem eq_zero_of_map_eq_zero_of_finite_degrees_coprime [Algebra.IsSeparable k E]
    (n m : ℕ)
    (hdeg : ∀ S : IntermediateField k E, FiniteDimensional k S →
      m.Coprime (Module.finrank k S))
    (x : K k n) (hx : map n (algebraMap k E) x = 0) (hxm : (m : ℤ) • x = 0) : x = 0 := by
  obtain ⟨S, hS, hxS⟩ := exists_finite_intermediate_map_eq_zero k E n x hx
  let := hS
  exact MilnorK.eq_zero_of_map_eq_zero_of_coprime k S n m (hdeg S hS) x hxS hxm

omit [Algebra.IsAlgebraic k E] in
/-- Prime-to-`p` finite intermediate degrees detect every `p`-power torsion
class after separable algebraic extension. No primality is needed for this
arithmetic consequence, and no injectivity on arbitrary Milnor classes is claimed. -/
theorem eq_zero_of_map_eq_zero_of_finite_degrees_coprime_pow [Algebra.IsSeparable k E]
    (n p r : ℕ)
    (hdeg : ∀ S : IntermediateField k E, FiniteDimensional k S →
      p.Coprime (Module.finrank k S))
    (x : K k n) (hx : map n (algebraMap k E) x = 0)
    (hxp : ((p ^ r : ℕ) : ℤ) • x = 0) : x = 0 :=
  eq_zero_of_map_eq_zero_of_finite_degrees_coprime k E n (p ^ r)
    (fun S hS => (hdeg S hS).pow_left r) x hx hxp

end MilnorK.FiniteDescent
