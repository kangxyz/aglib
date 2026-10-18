/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.BaseChange.Projective
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Projective cokernels of bounded projective complexes exact in positive degrees

Let `K` be a cochain complex of projective modules over a commutative ring `A`, strictly in
degrees `≤ n`, whose homology vanishes in every positive degree. Descending induction shows that
every cokernel `coker(d^q)`, `q ≥ 0`, is projective: `coker(d^n) = 0`, and from the exact sequence
`0 ⟶ H^q ⟶ coker(d^{q-1}) ⟶ K^{q+1} ⟶ coker(d^q) ⟶ 0` with `H^q = 0` and `coker(d^q)` projective,
`coker(d^{q-1})` is a direct summand of `K^{q+1}`
(`ShortComplex.projective_homology_iff_projective_opcycles_of_projective_cokernel`).

* `CochainComplex.projective_cokernel_d_pred`: one descending step;
* `CochainComplex.projective_cokernel_d_sub_of_vanishing`,
  `CochainComplex.projective_cokernel_d_of_vanishing`: projectivity of every cokernel;
* `CochainComplex.projective_homology_zero_of_vanishing`: if moreover `K` is strictly in degrees
  `≥ 0`, then `H^0(K)` is projective;
* `CochainComplex.extendScalarsHomologyMap_isIso_of_vanishing`: scalar extension along any ring
  map commutes with homology in every degree `q ≥ 0`
  (`ModuleCat.homologyBaseChangeMap_isIso_of_projective_cokernel`).

The consumer is the base-change theorem for coherent sheaves with vanishing higher cohomology on
projective space, `Cohomology/Projective/VanishingProjective`, applied to the finite-projective
model of the cohomology.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

namespace CochainComplex

variable {A : Type u} [CommRing A] (K : CochainComplex (ModuleCat.{u} A) ℤ)

/-- **One descending step.** For a complex of projective modules with `H^j(K) = 0`, projectivity of
`coker(d^j)` gives projectivity of `coker(d^{j-1})`. -/
theorem projective_cokernel_d_pred [∀ j, Module.Projective A (K.X j)] (j : ℤ)
    (hj : IsZero (K.homology j)) (h : Projective (cokernel (K.d j (j + 1)))) :
    Projective (cokernel (K.d (j - 1) j)) := by
  have hn : (ComplexShape.up ℤ).next j = j + 1 := (ComplexShape.up ℤ).next_eq' rfl
  have hp : (ComplexShape.up ℤ).prev j = j - 1 :=
    (ComplexShape.up ℤ).prev_eq' (by change (j - 1) + 1 = j; omega)
  have : Projective (K.sc j).X₃ := by
    change Projective (K.X ((ComplexShape.up ℤ).next j))
    exact ModuleCat.projective_of_categoryTheory_projective _
  have : Projective (cokernel (K.sc j).g) := by
    change Projective (cokernel (K.d j ((ComplexShape.up ℤ).next j)))
    rw [hn]
    exact h
  have hH : Projective (K.sc j).homology := Projective.of_iso hj.isoZero.symm inferInstance
  have hO : Projective (K.sc j).opcycles :=
    ((K.sc j).projective_homology_iff_projective_opcycles_of_projective_cokernel).mp hH
  have hC : Projective (cokernel (K.d ((ComplexShape.up ℤ).prev j) j)) :=
    Projective.of_iso (K.sc j).opcyclesIsoCokernel hO
  rw [hp] at hC
  exact hC

/-- **Descending induction.** For a complex of projective modules, strictly `≤ n`, with vanishing
homology in positive degrees, every cokernel `coker(d^{n - t})`, `t ≤ n`, is projective. -/
theorem projective_cokernel_d_sub_of_vanishing [∀ j, Module.Projective A (K.X j)] (n : ℕ)
    [K.IsStrictlyLE (n : ℤ)] (hvan : ∀ q : ℕ, q ≠ 0 → IsZero (K.homology (q : ℤ))) :
    ∀ t : ℕ, t ≤ n → Projective (cokernel (K.d ((n : ℤ) - t) ((n : ℤ) - t + 1))) := by
  intro t
  induction t with
  | zero =>
    intro _
    have hz : IsZero (K.X ((n : ℤ) - ((0 : ℕ) : ℤ) + 1)) :=
      K.isZero_of_isStrictlyLE (n : ℤ) _ (by omega)
    have : Epi (K.d ((n : ℤ) - ((0 : ℕ) : ℤ)) ((n : ℤ) - ((0 : ℕ) : ℤ) + 1)) := hz.epi _
    exact Projective.of_iso (isZero_cokernel_of_epi _).isoZero.symm inferInstance
  | succ t ih =>
    intro ht
    have e0 : (((n - t : ℕ)) : ℤ) = (n : ℤ) - t := by omega
    have hz : IsZero (K.homology ((n : ℤ) - t)) := e0 ▸ hvan (n - t) (by omega)
    have h := K.projective_cokernel_d_pred ((n : ℤ) - t) hz (ih (by omega))
    have e1 : (n : ℤ) - ((t + 1 : ℕ) : ℤ) = (n : ℤ) - t - 1 := by push_cast; ring
    have e2 : (n : ℤ) - t - 1 + 1 = (n : ℤ) - t := by ring
    rw [e1, e2]
    exact h

/-- Every cokernel `coker(d^q)`, `q ≥ 0`, of such a complex is projective. -/
theorem projective_cokernel_d_of_vanishing [∀ j, Module.Projective A (K.X j)] (n : ℕ)
    [K.IsStrictlyLE (n : ℤ)] (hvan : ∀ q : ℕ, q ≠ 0 → IsZero (K.homology (q : ℤ))) (q : ℕ) :
    Projective (cokernel (K.d (q : ℤ) ((q : ℤ) + 1))) := by
  by_cases hq : q ≤ n
  · have h := K.projective_cokernel_d_sub_of_vanishing n hvan (n - q) (by omega)
    have e : (n : ℤ) - ((n - q : ℕ) : ℤ) = q := by omega
    rw [e] at h
    exact h
  · have hz : IsZero (K.X ((q : ℤ) + 1)) := K.isZero_of_isStrictlyLE (n : ℤ) _ (by omega)
    have : Epi (K.d (q : ℤ) ((q : ℤ) + 1)) := hz.epi _
    exact Projective.of_iso (isZero_cokernel_of_epi _).isoZero.symm inferInstance

/-- **Projective `H^0`.** A complex of projective modules, strictly in degrees `[0, n]`, with
vanishing homology in positive degrees has projective `H^0`. -/
theorem projective_homology_zero_of_vanishing [∀ j, Module.Projective A (K.X j)] (n : ℕ)
    [K.IsStrictlyGE 0] [K.IsStrictlyLE (n : ℤ)]
    (hvan : ∀ q : ℕ, q ≠ 0 → IsZero (K.homology (q : ℤ))) :
    Module.Projective A (K.homology 0) := by
  have hn : (ComplexShape.up ℤ).next 0 = 0 + 1 := (ComplexShape.up ℤ).next_eq' rfl
  have hp : (ComplexShape.up ℤ).prev 0 = -1 := (ComplexShape.up ℤ).prev_eq' (by norm_num)
  have hP : Projective (cokernel (K.d 0 (0 + 1))) := by
    have h := K.projective_cokernel_d_of_vanishing n hvan 0
    exact h
  have : Projective (K.sc 0).X₃ := by
    change Projective (K.X ((ComplexShape.up ℤ).next 0))
    exact ModuleCat.projective_of_categoryTheory_projective _
  have : Projective (cokernel (K.sc 0).g) := by
    change Projective (cokernel (K.d 0 ((ComplexShape.up ℤ).next 0)))
    rw [hn]
    exact hP
  have hz : IsZero (K.sc 0).X₁ := by
    change IsZero (K.X ((ComplexShape.up ℤ).prev 0))
    rw [hp]
    exact K.isZero_of_isStrictlyGE 0 (-1) (by norm_num)
  have hf : (K.sc 0).f = 0 := hz.eq_of_src _ _
  have : IsIso (K.sc 0).pOpcycles := (K.sc 0).isIso_pOpcycles hf
  have h2 : Projective (K.sc 0).X₂ := by
    change Projective (K.X 0)
    exact ModuleCat.projective_of_categoryTheory_projective _
  have hO : Projective (K.sc 0).opcycles := Projective.of_iso (asIso (K.sc 0).pOpcycles) h2
  have hH : Projective (K.homology 0) :=
    ((K.sc 0).projective_homology_iff_projective_opcycles_of_projective_cokernel).mpr hO
  exact ModuleCat.projective_of_module_projective (K.homology 0)

/-- **Base change.** For a complex of projective modules, strictly `≤ n`, with vanishing homology in
positive degrees, scalar extension commutes with homology in every degree `q ≥ 0`. -/
theorem extendScalarsHomologyMap_isIso_of_vanishing [∀ j, Module.Projective A (K.X j)] (n : ℕ)
    [K.IsStrictlyLE (n : ℤ)] (hvan : ∀ q : ℕ, q ≠ 0 → IsZero (K.homology (q : ℤ)))
    {B : Type u} [CommRing B] (σ : A →+* B) (q : ℕ) :
    IsIso (extendScalarsHomologyMap σ K (q : ℤ)) := by
  have hn : (ComplexShape.up ℤ).next (q : ℤ) = (q : ℤ) + 1 := (ComplexShape.up ℤ).next_eq' rfl
  have hP := K.projective_cokernel_d_of_vanishing n hvan q
  have : Module.Projective A (K.sc (q : ℤ)).X₃ := by
    change Module.Projective A (K.X ((ComplexShape.up ℤ).next (q : ℤ)))
    infer_instance
  have : Module.Projective A (cokernel (K.sc (q : ℤ)).g : ModuleCat.{u} A) := by
    change Module.Projective A
      (cokernel (K.d (q : ℤ) ((ComplexShape.up ℤ).next (q : ℤ))) : ModuleCat.{u} A)
    rw [hn]
    exact ModuleCat.projective_of_module_projective _
  exact ModuleCat.homologyBaseChangeMap_isIso_of_projective_cokernel.{u, u, u} σ (K.sc (q : ℤ))

end CochainComplex
