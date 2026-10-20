/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Module.FiniteParametrix
public import Aglib.Algebra.Homology.MappingCone.Parametrix
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.RingTheory.Finiteness.Prod

/-! # Finite-projective cochain replacement from actual defect maps

The original complex is the cone of its degree-zero single map, with terms in
degrees minus one and zero. The explicit split-kernel replacement retains the
signed maps and actual homotopies. Both finite defect factorizations make its
terms finite projective. Applications to Cech degrees zero and one require a shift.
-/

/-!
Source: `quillen-k-theory/Quillen/Aglib/Algebra/Homology/ModuleCat/FiniteParametrix.lean` from the
supplied frozen Quillen snapshot.
SHA-256: `0fb76611b82aba1e27e11ab95a78025bbb045e9dad8fb7d06c6442a7a6d4bba9`.
Only native objects, maps and mathematical namespaces are used in this extraction.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] Abelian.hasFiniteBiproducts

namespace ModuleCat

open Module
variable {R : Type u} [CommRing R]
  {A B F : Type v} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup F] [Module R F]
  (d : A →ₗ[R] B) (s : B →ₗ[R] A) (t : F →ₗ[R] B) (r : B →ₗ[R] F)
  (hr : d.comp s + t.comp r = LinearMap.id)

/-- The actual two-term cochain complex is the cone of the original single map. -/
def linearMapCone : CochainComplex (ModuleCat.{v} R) ℤ :=
  CochainComplex.mappingCone
    ((HomologicalComplex.single (ModuleCat.{v} R) (.up ℤ) 0).map (ModuleCat.ofHom d))

/-- The specified defect splitting gives an actual homotopy equivalence to the replacement cone. -/
def parametrixConeHomotopyEquiv :
    HomotopyEquiv (linearMapCone d) (linearMapCone (parametrixReplacementDifferential d t)) := by
  let S := HomologicalComplex.single (ModuleCat.{v} R) (.up ℤ) 0
  let f₀ := parametrixForwardSource d s t r hr
  let g₀ := parametrixBackwardSource d t
  let δ := parametrixReplacementDifferential d t
  let hK := parametrixReplacementHomotopy d s t r hr
  refine CochainComplex.mappingCone.homotopyEquivOfParametrices
    (S.map (ModuleCat.ofHom d)) (S.map (ModuleCat.ofHom δ))
    (S.map (ModuleCat.ofHom f₀)) (S.map (ModuleCat.ofHom (-r)))
    (S.map (ModuleCat.ofHom g₀)) (S.map (ModuleCat.ofHom (-t)))
    ?_ ?_ (S.map (ModuleCat.ofHom s)) (S.map (ModuleCat.ofHom hK)) ?_ ?_ ?_ ?_
  · rw [← Functor.map_comp, ← Functor.map_comp]
    apply congrArg S.map
    exact ModuleCat.hom_ext (parametrixForward_chain d s t r hr).symm
  · rw [← Functor.map_comp, ← Functor.map_comp]
    apply congrArg S.map
    exact ModuleCat.hom_ext (parametrixBackward_chain d t).symm
  · rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add, ← CategoryTheory.Functor.map_id]
    apply congrArg S.map
    apply ModuleCat.hom_ext
    change s.comp d + g₀.comp f₀ = LinearMap.id
    rw [parametrixBackward_forward_zero]
    abel
  · rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add, ← CategoryTheory.Functor.map_id]
    apply congrArg S.map
    apply ModuleCat.hom_ext
    change d.comp s + (-t).comp (-r) = LinearMap.id
    rw [parametrixBackward_forward_one d s t r hr]
    abel
  · rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add, ← CategoryTheory.Functor.map_id]
    apply congrArg S.map
    apply ModuleCat.hom_ext
    change hK.comp δ + f₀.comp g₀ = LinearMap.id
    rw [add_comm]
    exact parametrixForward_backward_zero_add d s t r hr
  · rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add, ← CategoryTheory.Functor.map_id]
    apply congrArg S.map
    apply ModuleCat.hom_ext
    change δ.comp hK + (-r).comp (-t) = LinearMap.id
    rw [add_comm]
    exact parametrixForward_backward_one_add d s t r hr

end ModuleCat

namespace ModuleCat

open Module
variable {R : Type u} [CommRing R]
  {A B : Type v} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  (d : A →ₗ[R] B)

/-- The original single-map cone has terms only in degrees minus one and zero. -/
theorem linearMapCone_isZero_X (n : ℤ) (hn : n ≠ -1) (h0 : n ≠ 0) :
    IsZero ((linearMapCone d).X n) := by
  apply (CochainComplex.mappingCone.isZero_X_iff _ n).mpr
  exact ⟨HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R A) (n + 1)
      (by omega), HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R B) n h0⟩

/-- Each original single term of a finite-projective module is finite projective. -/
theorem single_finite_projective (M : ModuleCat.{v} R)
    [Module.Finite R M] [Module.Projective R M] (n : ℤ) :
    Module.Finite R (((HomologicalComplex.single (ModuleCat.{v} R) (.up ℤ) 0).obj M).X n) ∧
    Module.Projective R (((HomologicalComplex.single (ModuleCat.{v} R) (.up ℤ) 0).obj M).X n) := by
  by_cases hn : n = 0
  · subst n
    rw [HomologicalComplex.single_obj_X_self]
    exact ⟨inferInstance, inferInstance⟩
  · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M n hn
    let := ModuleCat.isZero_iff_subsingleton.mp hz
    exact ⟨inferInstance, inferInstance⟩

/-- Original single-map cone terms are finite projective when both original endpoints are. -/
theorem linearMapCone_finite_projective
    [Module.Finite R A] [Module.Projective R A]
    [Module.Finite R B] [Module.Projective R B] (n : ℤ) :
    Module.Finite R ((linearMapCone d).X n) ∧ Module.Projective R ((linearMapCone d).X n) := by
  let K := (HomologicalComplex.single (ModuleCat.{v} R) (.up ℤ) 0).obj (ModuleCat.of R A)
  let L := (HomologicalComplex.single (ModuleCat.{v} R) (.up ℤ) 0).obj (ModuleCat.of R B)
  obtain ⟨hKf, hKp⟩ := single_finite_projective (ModuleCat.of R A) (n + 1)
  obtain ⟨hLf, hLp⟩ := single_finite_projective (ModuleCat.of R B) n
  let e : (linearMapCone d).X n ≅ ModuleCat.of R (K.X (n + 1) × L.X n) :=
    HomologicalComplex.homotopyCofiber.XIsoBiprod
      ((HomologicalComplex.single (ModuleCat.{v} R) (.up ℤ) 0).map (ModuleCat.ofHom d))
      n (n + 1) rfl ≪≫ ModuleCat.biprodIsoProd _ _
  exact ⟨Module.Finite.equiv e.toLinearEquiv.symm,
    Module.Projective.of_equiv e.toLinearEquiv.symm⟩

/-- The actual finite defect factorizations yield a bounded finite-projective cochain model. -/
theorem exists_finite_projective_parametrix_model
    {F G : Type v} [AddCommGroup F] [Module R F] [AddCommGroup G] [Module R G]
    [Module.Projective R A] [Module.Projective R F] [Module.Finite R F] [Module.Finite R G]
    (s : B →ₗ[R] A) (t : F →ₗ[R] B) (r : B →ₗ[R] F)
    (hr : d.comp s + t.comp r = LinearMap.id)
    (u : G →ₗ[R] A) (v : A →ₗ[R] G) (hl : s.comp d + u.comp v = LinearMap.id) :
    ∃ P : CochainComplex (ModuleCat.{v} R) ℤ,
      (∀ n, n ≠ -1 → n ≠ 0 → IsZero (P.X n)) ∧
      (∀ n, Module.Finite R (P.X n) ∧ Module.Projective R (P.X n)) ∧
      Nonempty (HomotopyEquiv (linearMapCone d) P) := by
  obtain ⟨hKf, hKp⟩ := finite_projective_parametrixKernel d s t r hr u v hl
  refine ⟨linearMapCone (parametrixReplacementDifferential d t),
    linearMapCone_isZero_X _, linearMapCone_finite_projective _, ?_⟩
  exact ⟨parametrixConeHomotopyEquiv d s t r hr⟩

end ModuleCat
