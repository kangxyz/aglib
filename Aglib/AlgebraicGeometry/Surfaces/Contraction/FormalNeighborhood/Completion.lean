/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.Affine
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.Local
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Coefficient
public import Aglib.RingTheory.AdicCompletion.CompatibleLifts
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Completion and finite Nakayama for the original maps

The completion descent preserves the original ring map and ideal. The transition-correction result
retains its explicit correction input. Proper formal functions and finite Nakayama also descend
objectwise quotient H1 vanishing.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Surfaces.Contraction.FormalNeighborhood

universe u v w t

section OriginalCompletion

variable {R : Type u} [CommRing R] (I : Ideal R)
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]

/-- Surjectivity of the original completed map descends by finite Nakayama.
The original ideal only needs to lie in the Jacobson radical. -/
theorem surjective_of_completionMap_surjective [Module.Finite R N]
    (f : M →ₗ[R] N) (hI : I ≤ (⊥ : Ideal R).jacobson)
    (hf : Function.Surjective (AdicCompletion.map I f)) : Function.Surjective f := by
  apply LinearMap.surjective_of_surjective_comp_mkQ f I hI
  intro q
  obtain ⟨b, rfl⟩ := (I • (⊤ : Submodule R N)).mkQ_surjective q
  obtain ⟨z, hz⟩ := hf (AdicCompletion.of I N b)
  obtain ⟨a, ha⟩ := (I ^ 1 • (⊤ : Submodule R M)).mkQ_surjective
    (AdicCompletion.eval I M 1 z)
  refine ⟨a, ?_⟩
  have h := congrArg (AdicCompletion.eval I N 1) hz
  change (f.reduceModIdeal (I ^ 1)) (AdicCompletion.eval I M 1 z) =
    AdicCompletion.eval I N 1 (AdicCompletion.of I N b) at h
  rw [← ha] at h
  change (Submodule.Quotient.mk (f a) : N ⧸ (I ^ 1 • (⊤ : Submodule R N))) =
    Submodule.Quotient.mk b at h
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
  apply (Submodule.Quotient.eq _).mpr
  have hm := (Submodule.Quotient.eq (I ^ 1 • (⊤ : Submodule R N))).mp h
  have he : I ^ 1 • (⊤ : Submodule R N) = I • (⊤ : Submodule R N) :=
    congrArg (fun J : Ideal R => J • (⊤ : Submodule R N)) (pow_one I)
  exact he ▸ hm

variable (Q : ℕᵒᵖ ⥤ ModuleCat.{t} R)
  (uMap : ∀ n : ℕ, N →ₗ[R] Q.obj (op n))
  (hu : ∀ {m n : ℕ} (h : m ≤ n),
    (AdicCompletion.towerTransition Q h).comp (uMap n) = uMap m)
  (hpow : ∀ n : ℕ, I ^ n • (⊤ : Submodule R N) ≤ (uMap n).ker)

include hpow in
private theorem compositeReduction_pow_le_ker (f : M →ₗ[R] N) (n : ℕ) :
    I ^ n • (⊤ : Submodule R M) ≤ ((uMap n).comp f).ker := by
  intro x hx
  apply hpow n
  have hm : (I ^ n • (⊤ : Submodule R M)).map f ≤ I ^ n • (⊤ : Submodule R N) := by
    rw [Submodule.map_smul'']
    exact smul_mono_right _ le_top
  exact hm ⟨x, hx, rfl⟩

include hu in
private theorem compositeReduction_compatible (f : M →ₗ[R] N)
    {m n : ℕ} (h : m ≤ n) :
    (AdicCompletion.towerTransition Q h).comp ((uMap n).comp f) = (uMap m).comp f := by
  ext x
  exact LinearMap.congr_fun (hu h) (f x)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem completionToSections_comp_map (f : M →ₗ[R] N)
    (z : AdicCompletion I M) :
    AdicCompletion.completionToSections I Q uMap hu hpow (AdicCompletion.map I f z) =
      AdicCompletion.completionToSections I Q (fun n => (uMap n).comp f)
        (compositeReduction_compatible Q uMap hu f)
        (compositeReduction_pow_le_ker I Q uMap hpow f) z := by
  apply Subtype.ext
  funext j
  let n := j.unop
  have hq (q : M ⧸ (I ^ n • (⊤ : Submodule R M))) :
      (I ^ n • (⊤ : Submodule R N)).liftQ (uMap n) (hpow n)
          (f.reduceModIdeal (I ^ n) q) =
        (I ^ n • (⊤ : Submodule R M)).liftQ ((uMap n).comp f)
          (compositeReduction_pow_le_ker I Q uMap hpow f n) q := by
    induction q using Submodule.Quotient.induction_on with
    | _ a => rfl
  exact hq (AdicCompletion.eval I M n z)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Original transition corrections imply surjectivity of the original completed
map whenever its target's canonical tower comparison is injective. -/
theorem completionMap_surjective_of_transitionCorrections
    [Subsingleton (Q.obj (op 0))] (f : M →ₗ[R] N)
    (hcor : ∀ n, (AdicCompletion.towerTransition Q (Nat.le_succ n)).ker ≤
      (I ^ n • (⊤ : Submodule R M)).map ((uMap (n + 1)).comp f))
    (hinj : Function.Injective (AdicCompletion.completionToSections I Q uMap hu hpow)) :
    Function.Surjective (AdicCompletion.map I f) := by
  intro y
  let x := AdicCompletion.completionToSections I Q uMap hu hpow y
  obtain ⟨z, hz⟩ := AdicCompletion.exists_compatible_lift I
    (fun n => (uMap n).comp f)
    (fun n => AdicCompletion.towerTransition Q (Nat.le_succ n))
    (fun n => compositeReduction_compatible Q uMap hu f (Nat.le_succ n)) hcor
    (fun n => x.val (op n))
    (fun n => x.property (homOfLE (Nat.le_succ n)).op)
    (compositeReduction_pow_le_ker I Q uMap hpow f)
  refine ⟨z, hinj ?_⟩
  refine (completionToSections_comp_map I Q uMap hu hpow f z).trans ?_
  apply Subtype.ext
  funext j
  exact hz j.unop

end OriginalCompletion

/-- Coefficients of an original homogeneous polynomial lift through the original
surjective ring map, without a coefficient-field section. -/
theorem exists_homogeneous_coefficient_lift
    {R : Type u} [CommRing R] {K : Type v} [CommRing K] {J : Type w}
    (β : R →+* K) (hβ : Function.Surjective β) (n : ℕ)
    (p : MvPolynomial.homogeneousSubmodule J K n) :
    ∃ q : MvPolynomial.homogeneousSubmodule J R n, MvPolynomial.map β q.val = p.val := by
  classical
  let γ : K → R := fun a => if a = 0 then 0 else (hβ a).choose
  have hγ₀ : γ 0 = 0 := ite_eq_left rfl
  have hβγ (a : K) : β (γ a) = a := by
    by_cases h : a = 0
    · subst a
      exact (congrArg β hγ₀).trans (map_zero β)
    · have ha : γ a = (hβ a).choose := ite_eq_right h
      exact (congrArg β ha).trans (hβ a).choose_spec
  let q : MvPolynomial J R :=
    AddMonoidAlgebra.ofCoeff (Finsupp.mapRange γ hγ₀ p.val.coeff)
  have hq : q.IsHomogeneous n := by
    intro e he
    apply p.property
    intro hp
    apply he
    change γ (p.val.coeff e) = 0
    rw [hp, hγ₀]
  refine ⟨⟨q, hq⟩, ?_⟩
  ext e
  rw [MvPolynomial.coeff_map]
  change β (γ (p.val.coeff e)) = p.val.coeff e
  exact hβγ _

section CanonicalStructureClass

variable {R : Type u} [CommRing R] (X : Scheme.{u}) (α : R →+* Γ(X, ⊤))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original structural scalar, as the actual original degree-zero structure-module class. -/
def structuralH0Class : R →ₗ[R]
    (moduleCohomologyFunctorOfHom X α 0).obj (SheafOfModules.unit X.ringCatSheaf) := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  letI := moduleCohomologyModuleOfHom X α O 0
  letI : Module R (O.val.obj (op ⊤)) := Module.compHom _ α
  let c : R →ₗ[R] O.val.obj (op ⊤) :=
    { toFun := α
      map_add' := map_add α
      map_smul' := fun r a => show α (r * a) = α r * α a from map_mul α r a }
  exact (moduleH0EquivOfHom X α O).symm.toLinearMap.comp c

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Reading the original degree-zero class recovers exactly the original structural coefficient. -/
theorem structuralH0Class_sections (r : R) :
    moduleH0EquivOfHom X α (SheafOfModules.unit X.ringCatSheaf)
      (structuralH0Class X α r) = α r :=
  (moduleH0EquivOfHom X α (SheafOfModules.unit X.ringCatSheaf)).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Surjectivity of the original structural class map is precisely surjectivity
of the original structural ring homomorphism. -/
theorem structuralH0Class_surjective_iff :
    Function.Surjective (structuralH0Class X α) ↔ Function.Surjective α := by
  let e := moduleH0EquivOfHom X α (SheafOfModules.unit X.ringCatSheaf)
  constructor
  · intro h b
    obtain ⟨a, ha⟩ := h (e.symm b)
    refine ⟨a, ?_⟩
    exact (structuralH0Class_sections X α a).symm.trans
      ((congrArg e ha).trans (e.apply_symm_apply b))
  · intro h x
    obtain ⟨a, ha⟩ := h (e x)
    refine ⟨a, e.injective ?_⟩
    exact (structuralH0Class_sections X α a).trans ha

end CanonicalStructureClass

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Proper formal functions and finite Nakayama descend actual original tower
corrections to surjectivity of the original structural ring map. -/
theorem structuralMap_surjective_of_transitionCorrections
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    (hI : I ≤ (⊥ : Ideal R).jacobson)
    (hcor :
      let α := affineFormalFunctionsScalar f
      let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
      let Q := idealPowerQuotientCohomology X α O I 0
      ∀ n, (AdicCompletion.towerTransition Q (Nat.le_succ n)).ker ≤
        (I ^ n • (⊤ : Submodule R R)).map
          ((idealPowerCohomologyReductionMap X α O I 0 (n + 1)).comp
            (structuralH0Class X α))) :
    Function.Surjective (affineFormalFunctionsScalar f) := by
  let α := affineFormalFunctionsScalar f
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let Q := idealPowerQuotientCohomology X α O I 0
  let M := (moduleCohomologyFunctorOfHom X α 0).obj O
  let uMap := idealPowerCohomologyReductionMap X α O I 0
  let hu : ∀ {m n : ℕ} (h : m ≤ n),
      (AdicCompletion.towerTransition Q h).comp (uMap n) = uMap m :=
    fun h => idealPowerCohomologyReductionMap_compatible X α O I 0 h
  let hpow := fun n => idealPowerQuotientReduction_pow_le_ker X α O I n 0
  have hzero : IsZero (Q.obj (op 0)) :=
    Functor.map_isZero (moduleCohomologyFunctorOfHom X α 0)
      (idealPowerQuotient_zero_isZero X α O I)
  let _ : Subsingleton (Q.obj (op 0)) := ModuleCat.subsingleton_of_isZero hzero
  let _ : Module.Finite R M :=
    moduleCohomology_finite_of_proper R f O (affineLocallyFiniteType_unit X) 0
  have hinj : Function.Injective (AdicCompletion.completionToSections I Q uMap hu hpow) :=
    (moduleCohomologyFormalFunctions_bijective I f O (affineLocallyFiniteType_unit X) 0).injective
  have hs : Function.Surjective (AdicCompletion.map I (structuralH0Class X α)) :=
    completionMap_surjective_of_transitionCorrections I Q uMap hu hpow
      (structuralH0Class X α) hcor hinj
  exact (structuralH0Class_surjective_iff X α).mp
    (surjective_of_completionMap_surjective I (structuralH0Class X α) hI hs)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual proper formal functions and finite Nakayama turn per-object
vanishing of the ORIGINAL quotient H1 into vanishing of the original H1.
No transition-coordinate comparison is needed for this zero inverse limit. -/
theorem h1_subsingleton_of_quotient_h1_subsingleton
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    (F : X.Modules) (hF : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType X F)
    (hI : I ≤ (⊥ : Ideal R).jacobson)
    (hQ : ∀ n : ℕ, Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf X (idealPowerQuotient X (affineFormalFunctionsScalar f) F I n)) 1)) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X F) 1) := by
  let α := affineFormalFunctionsScalar f
  let M := (moduleCohomologyFunctorOfHom X α 1).obj F
  let _ : Module.Finite R M := moduleCohomology_finite_of_proper R f F hF 1
  have hinj := (moduleCohomologyFormalFunctions_bijective I f F hF 1).injective
  let _ : Subsingleton (AdicCompletion I M) := ⟨fun x y => hinj (by
    apply Subtype.ext
    funext j
    exact @Subsingleton.elim _ (hQ j.unop) _ _)⟩
  have hs : Function.Surjective (AdicCompletion.map I (0 : R →ₗ[R] M)) :=
    fun z => ⟨0, Subsingleton.elim _ _⟩
  have h0 : Function.Surjective (0 : R →ₗ[R] M) :=
    surjective_of_completionMap_surjective I 0 hI hs
  have hz (x : M) : x = 0 := by
    obtain ⟨a, ha⟩ := h0 x
    exact ha.symm
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finite Nakayama descends the ORIGINAL structural ring map once the actual
residue restriction has no kernel beyond the original base-ideal multiple.
The coefficient lifting is only surjectivity of the original composite. -/
theorem ringHom_surjective_of_finite_residue_kernel
    {R B k : Type u} [CommRing R] [CommRing B] [CommRing k]
    (α : R →+* B) (δ : B →+* k) (I : Ideal R) (hα : α.Finite)
    (hJac : I ≤ (⊥ : Ideal R).jacobson)
    (hres : Function.Surjective (δ.comp α))
    (hker : letI : Algebra R B := α.toAlgebra
      ∀ b : B, δ b = 0 → b ∈ I • (⊤ : Submodule R B)) :
    Function.Surjective α := by
  let : Algebra R B := α.toAlgebra
  let _ : Module.Finite R B := hα
  let u : R →ₗ[R] B := Algebra.linearMap R B
  let P : Submodule R B := I • ⊤
  have hq : Function.Surjective (P.mkQ.comp u) := by
    intro q
    obtain ⟨b, rfl⟩ := P.mkQ_surjective q
    obtain ⟨a, ha⟩ := hres (δ b)
    refine ⟨a, ?_⟩
    apply (Submodule.Quotient.eq P).mpr
    apply hker (α a - b)
    rw [map_sub]
    exact sub_eq_zero.mpr ha
  exact LinearMap.surjective_of_surjective_comp_mkQ u I hJac hq

end AlgebraicGeometry.Scheme.Surfaces.Contraction.FormalNeighborhood
