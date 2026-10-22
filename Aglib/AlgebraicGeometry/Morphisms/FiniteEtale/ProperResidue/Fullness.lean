/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.ProperResidue
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Graph
public import Aglib.RingTheory.Henselian.FiniteAlgebraIdempotents
public import Aglib.AlgebraicGeometry.Cohomology.Exact.Modules
public import Aglib.AlgebraicGeometry.Modules.Invertible.Power.TrivializedPower
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Aglib.AlgebraicGeometry.Cohomology.Proper.Finiteness
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Coefficient
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FlatPullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.SMulRegular
public import Aglib.AlgebraicGeometry.Modules.Invertible.ScalarAutomorphisms

/-!
# Fullness for proper flat models over Henselian DVRs

Actual scalar cokernels and finite first cohomology lift closed-fibre clopens
to global idempotents. Applying this construction to the original residue
graph proves fullness of the literal finite-etale pullback functor. Properness
and flatness remain explicit; essential surjectivity is not asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower

namespace AlgebraicGeometry.Scheme.FiniteEtale.ProperResidue

universe u v

/-- Power torsion in a Noetherian module cannot supply a nonzero element
with arbitrarily deep compatible divisions. -/
theorem eq_zero_of_torsion_power_lifts
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [_root_.IsNoetherian R M] (r : R) (x : M)
    (h : ∀ n : ℕ, ∃ y : M, r ^ (n + 1) • y = 0 ∧ r ^ n • y = x) : x = 0 := by
  let f : M →ₗ[R] M := LinearMap.lsmul R M r
  have hpow (n : ℕ) (y : M) : (f ^ n) y = r ^ n • y := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      change r • (r ^ n • y) = r ^ (n + 1) • y
      rw [← mul_smul, pow_succ']
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (LinearMap.eventually_iSup_ker_pow_eq f)
  obtain ⟨y, hy, hxy⟩ := h N
  have hyker : y ∈ LinearMap.ker (f ^ (N + 1)) := by
    change (f ^ (N + 1)) y = 0
    rwa [hpow]
  have hyall : y ∈ ⨆ n : ℕ, LinearMap.ker (f ^ n) :=
    Submodule.mem_iSup_of_mem (N + 1) hyker
  rw [hN N le_rfl] at hyall
  have hyzero : r ^ N • y = 0 := by
    change (f ^ N) y = 0 at hyall
    rwa [hpow] at hyall
  rw [← hxy, hyzero]

section ScalarCokernels

variable (X : Scheme.{u}) {R : Type u} [CommRing R]
  (α : R →+* Γ(X, ⊤)) (M : X.Modules) (r : R)

/-- The actual scalar-power map, before taking its module-sheaf cokernel. -/
abbrev scalarPower (n : ℕ) : M ⟶ M := scalarMap X M (α (r ^ (n + 1)))

/-- The original cokernel sequence of multiplication by a scalar power. -/
abbrev scalarSequence (n : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk (scalarPower X α M r n) (cokernel.π (scalarPower X α M r n))
    (cokernel.condition _)

/-- Actual monicity makes the native scalar-cokernel sequence short exact. -/
theorem scalarSequence_shortExact (n : ℕ) [Mono (scalarPower X α M r n)] :
    (scalarSequence X α M r n).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The native scalar power factors through the original first power. -/
theorem scalarPower_factor (n : ℕ) :
    scalarMap X M (α (r ^ n)) ≫ scalarPower X α M r 0 = scalarPower X α M r n := by
  change scalarMap X M (α (r ^ n)) ≫ scalarMap X M (α (r ^ 1)) =
    scalarMap X M (α (r ^ (n + 1)))
  rw [pow_one, AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.scalarMap_mul,
    ← map_mul, pow_succ]

/-- The actual map from the `(n+1)`st power sequence to the first sequence.
Its kernel coefficient is multiplication by `r^n`, and its middle map is the identity. -/
def scalarSequenceToFirst (n : ℕ) :
    scalarSequence X α M r n ⟶ scalarSequence X α M r 0 where
  τ₁ := scalarMap X M (α (r ^ n))
  τ₂ := 𝟙 M
  τ₃ := cokernel.map (scalarPower X α M r n) (scalarPower X α M r 0)
    (scalarMap X M (α (r ^ n))) (𝟙 M)
    ((Category.comp_id _).trans (scalarPower_factor X α M r n).symm)
  comm₁₂ := (scalarPower_factor X α M r n).trans (Category.comp_id _).symm
  comm₂₃ := by simp [scalarSequence]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finite original first cohomology kills the boundary of a compatible
family in the actual scalar cokernels. No degree-zero base-change
surjectivity is assumed. -/
theorem exists_lift_scalar_cokernel_class_of_compatible [IsNoetherianRing R]
    (hm : ∀ n, Mono (scalarPower X α M r n))
    (z : ∀ n, Sheaf.H.{u + 1}
      (moduleAddSheaf X (scalarSequence X α M r n).X₃) 0)
    (hz : ∀ n, moduleCohomologyMapOfHom X α (scalarSequenceToFirst X α M r n).τ₃ 0
      (z n) = z 0) :
    letI := moduleCohomologyModuleOfHom X α M 1
    Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf X M) 1) →
    ∃ x : Sheaf.H.{u + 1} (moduleAddSheaf X M) 0,
      moduleCohomologyMapOfHom X α (scalarSequence X α M r 0).g 0 x = z 0 := by
  let := moduleCohomologyModuleOfHom X α M 1
  intro hfinite
  let : Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf X M) 1) := hfinite
  let : ∀ n, Mono (scalarPower X α M r n) := hm
  let δ (n : ℕ) := moduleCohomologyConnectingOfHom X α
    (scalarSequence X α M r n) (scalarSequence_shortExact X α M r n) 0
  have hzero : δ 0 (z 0) = 0 := by
    apply eq_zero_of_torsion_power_lifts r
    intro n
    refine ⟨δ n (z n), ?_, ?_⟩
    · have he := (moduleCohomologyConnectingOfHom_exact_right X α
        (scalarSequence X α M r n) (scalarSequence_shortExact X α M r n) 0).apply_apply_eq_zero
        (z n)
      exact he
    · have he := moduleCohomologyConnectingOfHom_naturality X α
        (scalarSequence_shortExact X α M r n) (scalarSequence_shortExact X α M r 0)
        (scalarSequenceToFirst X α M r n) 0 (z n)
      rw [hz n] at he
      exact he.symm
  exact ((moduleCohomologyConnectingOfHom_exact_left X α
    (scalarSequence X α M r 0) (scalarSequence_shortExact X α M r 0) 0) (z 0)).mp hzero

end ScalarCokernels

section TwoOpenPatch

variable (X : Scheme.{u}) {R : Type u} [CommRing R]
  (α : R →+* Γ(X, ⊤)) (r : R)

/-- The structure sheaf of `X` regarded as the unit module over itself. -/
abbrev structureUnit : X.Modules := SheafOfModules.unit X.ringCatSheaf

/-- The module-sheaf cokernel of multiplication by the global scalar `α (r ^ (n + 1))`
on the structure sheaf. -/
abbrev scalarQuotient (n : ℕ) : X.Modules :=
  (scalarSequence X α (structureUnit X) r n).X₃

/-- The cokernel projection from the structure sheaf to its quotient by multiplication
by `α (r ^ (n + 1))`. -/
abbrev scalarQuotientMap (n : ℕ) : structureUnit X ⟶ scalarQuotient X α r n :=
  (scalarSequence X α (structureUnit X) r n).g

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarQuotient_one_res (n : ℕ) {U V : X.Opens} (h : V ≤ U) :
    (scalarQuotient X α r n).val.map (homOfLE h).op
      ((scalarQuotientMap X α r n).val.app (op U) (1 : Γ(X, U))) =
        (scalarQuotientMap X α r n).val.app (op V) (1 : Γ(X, V)) := by
  have hn := PresheafOfModules.naturality_apply (scalarQuotientMap X α r n).val
    (homOfLE h).op (1 : Γ(X, U))
  change (scalarQuotientMap X α r n).val.app (op V)
      (X.presheaf.map (homOfLE h).op (1 : Γ(X, U))) =
    (scalarQuotient X α r n).val.map (homOfLE h).op
      ((scalarQuotientMap X α r n).val.app (op U) (1 : Γ(X, U))) at hn
  rw [map_one] at hn
  exact hn.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarQuotient_one_eq_zero (n : ℕ) (U : X.Opens)
    (hr : IsUnit (globalRestriction X U (α r))) :
    (scalarQuotientMap X α r n).val.app (op U) (1 : Γ(X, U)) = 0 := by
  have hrn : IsUnit (globalRestriction X U (α (r ^ (n + 1)))) := by
    simpa only [map_pow] using hr.pow (n + 1)
  obtain ⟨w, hw⟩ := hrn
  have hc := congrArg
    (fun f : structureUnit X ⟶ scalarQuotient X α r n => f.val.app (op U) (↑(w⁻¹) : Γ(X, U)))
    (cokernel.condition (scalarPower X α (structureUnit X) r n))
  change (scalarQuotientMap X α r n).val.app (op U)
    (globalRestriction X U (α (r ^ (n + 1))) * (↑(w⁻¹) : Γ(X, U))) = 0 at hc
  rw [← hw, Units.mul_inv] at hc
  exact hc

private def twoOpenCover (U V : X.Opens) : Bool → X.Opens
  | true => U
  | false => V

private def scalarQuotientLocalPatch (n : ℕ) (U V : X.Opens) :
    ∀ b, Γ(scalarQuotient X α r n, twoOpenCover X U V b)
  | true => (scalarQuotientMap X α r n).val.app (op U) (1 : Γ(X, U))
  | false => 0

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- One and zero glue in the actual scalar cokernel when the scalar is a
unit on the overlap. This is a construction on the original scheme. -/
theorem exists_scalar_quotient_patch (n : ℕ) (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (hr : IsUnit (globalRestriction X (U ⊓ V) (α r))) :
    ∃ y : Γ(scalarQuotient X α r n, ⊤),
      (scalarQuotient X α r n).val.map (homOfLE le_top : U ⟶ ⊤).op y =
        (scalarQuotientMap X α r n).val.app (op U) (1 : Γ(X, U)) ∧
      (scalarQuotient X α r n).val.map (homOfLE le_top : V ⟶ ⊤).op y = 0 := by
  let Q := scalarQuotient X α r n
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨Q.presheaf, Q.isSheaf⟩
  let cover := twoOpenCover X U V
  let s := scalarQuotientLocalPatch X α r n U V
  have hcover : (⊤ : X.Opens) ≤ iSup cover := by
    rw [← hUV]
    exact sup_le (le_iSup cover true) (le_iSup cover false)
  have hs : TopCat.Presheaf.IsCompatible Q.presheaf cover s := by
    intro b c
    cases b <;> cases c
    · rfl
    · change Q.val.map (homOfLE inf_le_left : V ⊓ U ⟶ V).op 0 =
        Q.val.map (homOfLE inf_le_right : V ⊓ U ⟶ U).op
          ((scalarQuotientMap X α r n).val.app (op U) (1 : Γ(X, U)))
      rw [map_zero, scalarQuotient_one_res]
      symm
      apply scalarQuotient_one_eq_zero
      rw [inf_comm V U]
      exact hr
    · change Q.val.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op
          ((scalarQuotientMap X α r n).val.app (op U) (1 : Γ(X, U))) =
        Q.val.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op 0
      rw [map_zero, scalarQuotient_one_res]
      exact scalarQuotient_one_eq_zero X α r n (U ⊓ V) hr
    · rfl
  obtain ⟨y, hy, _⟩ := F.existsUnique_gluing' cover ⊤ (fun _ => homOfLE le_top)
    hcover s hs
  exact ⟨y, hy true, hy false⟩

end TwoOpenPatch

section CompatiblePatches

variable (X : Scheme.{u}) {R : Type u} [CommRing R]
  (α : R →+* Γ(X, ⊤)) (r : R)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The one-zero patch sections can be chosen compatibly in the actual
scalar-cokernel tower. -/
theorem exists_compatible_scalar_quotient_patches (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (hr : IsUnit (globalRestriction X (U ⊓ V) (α r))) :
    ∃ y : ∀ n, Γ(scalarQuotient X α r n, ⊤),
      (∀ n,
        (scalarQuotient X α r n).val.map (homOfLE le_top : U ⟶ ⊤).op (y n) =
          (scalarQuotientMap X α r n).val.app (op U) (1 : Γ(X, U)) ∧
        (scalarQuotient X α r n).val.map (homOfLE le_top : V ⟶ ⊤).op (y n) = 0) ∧
      ∀ n, (scalarSequenceToFirst X α (structureUnit X) r n).τ₃.val.app (op ⊤)
        (y n) = y 0 := by
  choose y hy using fun n => exists_scalar_quotient_patch X α r n U V hUV hr
  refine ⟨y, hy, ?_⟩
  intro n
  let Q := scalarQuotient X α r 0
  let t := (scalarSequenceToFirst X α (structureUnit X) r n).τ₃
  have ht : scalarQuotientMap X α r n ≫ t = scalarQuotientMap X α r 0 := by
    simp [t, scalarQuotientMap, scalarSequenceToFirst]
  apply TopCat.Sheaf.eq_of_locally_eq₂ ⟨Q.presheaf, Q.isSheaf⟩
    (homOfLE le_top : U ⟶ ⊤) (homOfLE le_top : V ⟶ ⊤) (by rw [hUV])
  · calc
      Q.val.map (homOfLE le_top : U ⟶ ⊤).op (t.val.app (op ⊤) (y n)) =
          t.val.app (op U)
            ((scalarQuotient X α r n).val.map (homOfLE le_top : U ⟶ ⊤).op (y n)) :=
        (PresheafOfModules.naturality_apply t.val (homOfLE le_top : U ⟶ ⊤).op (y n)).symm
      _ = t.val.app (op U) ((scalarQuotientMap X α r n).val.app (op U) (1 : Γ(X, U))) :=
        congrArg (fun x => t.val.app (op U) x) (hy n).1
      _ = (scalarQuotientMap X α r 0).val.app (op U) (1 : Γ(X, U)) :=
        congrArg (fun f => f.val.app (op U) (1 : Γ(X, U))) ht
      _ = Q.val.map (homOfLE le_top : U ⟶ ⊤).op (y 0) := (hy 0).1.symm
  · calc
      Q.val.map (homOfLE le_top : V ⟶ ⊤).op (t.val.app (op ⊤) (y n)) =
          t.val.app (op V)
            ((scalarQuotient X α r n).val.map (homOfLE le_top : V ⟶ ⊤).op (y n)) :=
        (PresheafOfModules.naturality_apply t.val (homOfLE le_top : V ⟶ ⊤).op (y n)).symm
      _ = t.val.app (op V) 0 := congrArg (fun x => t.val.app (op V) x) (hy n).2
      _ = 0 := map_zero _
      _ = Q.val.map (homOfLE le_top : V ⟶ ⊤).op (y 0) := (hy 0).2.symm

end CompatiblePatches

section GlobalPatchLift

variable (X : Scheme.{u}) {R : Type u} [CommRing R] [IsNoetherianRing R]
  (α : R →+* Γ(X, ⊤)) (r : R)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finite original H1 lifts the constructed one-zero patch through the
first scalar quotient map. The compatible classes are constructed, not
assumed, by sheaf gluing on the given two-open cover. -/
theorem exists_global_lift_of_two_open_patch
    (hm : ∀ n, Mono (scalarPower X α (structureUnit X) r n))
    (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (hr : IsUnit (globalRestriction X (U ⊓ V) (α r))) :
    letI := moduleCohomologyModuleOfHom X α (structureUnit X) 1
    Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf X (structureUnit X)) 1) →
    ∃ a : Γ(X, ⊤),
      (scalarQuotientMap X α r 0).val.app (op U) (globalRestriction X U a) =
        (scalarQuotientMap X α r 0).val.app (op U) (1 : Γ(X, U)) ∧
      (scalarQuotientMap X α r 0).val.app (op V) (globalRestriction X V a) = 0 := by
  let := moduleCohomologyModuleOfHom X α (structureUnit X) 1
  intro hfinite
  obtain ⟨y, hy, hcompat⟩ := exists_compatible_scalar_quotient_patches X α r U V hUV hr
  let z (n : ℕ) := (moduleH0EquivOfHom X α (scalarQuotient X α r n)).symm (y n)
  have hz (n : ℕ) : moduleCohomologyMapOfHom X α
      (scalarSequenceToFirst X α (structureUnit X) r n).τ₃ 0 (z n) = z 0 := by
    apply (moduleH0EquivOfHom X α (scalarQuotient X α r 0)).injective
    have hn := Sheaf.H.equiv₀_naturality isTerminalTop
      ((SheafOfModules.toSheaf X.ringCatSheaf).map
        (scalarSequenceToFirst X α (structureUnit X) r n).τ₃) (z n)
    change (scalarSequenceToFirst X α (structureUnit X) r n).τ₃.val.app (op ⊤)
      ((moduleH0EquivOfHom X α (scalarQuotient X α r n)) (z n)) =
      (moduleH0EquivOfHom X α (scalarQuotient X α r 0))
        (moduleCohomologyMapOfHom X α
          (scalarSequenceToFirst X α (structureUnit X) r n).τ₃ 0 (z n)) at hn
    simpa only [z, LinearEquiv.apply_symm_apply, hcompat n] using hn.symm
  obtain ⟨x, hx⟩ := exists_lift_scalar_cokernel_class_of_compatible X α
    (structureUnit X) r hm z hz hfinite
  let a : Γ(X, ⊤) := moduleH0EquivOfHom X α (structureUnit X) x
  have ha : (scalarQuotientMap X α r 0).val.app (op ⊤) a = y 0 := by
    have hn := Sheaf.H.equiv₀_naturality isTerminalTop
      ((SheafOfModules.toSheaf X.ringCatSheaf).map (scalarQuotientMap X α r 0)) x
    change (scalarQuotientMap X α r 0).val.app (op ⊤) a =
      (moduleH0EquivOfHom X α (scalarQuotient X α r 0))
        (moduleCohomologyMapOfHom X α (scalarQuotientMap X α r 0) 0 x) at hn
    rw [hx] at hn
    simpa only [z, LinearEquiv.apply_symm_apply] using hn
  refine ⟨a, ?_, ?_⟩
  · have hn := PresheafOfModules.naturality_apply (scalarQuotientMap X α r 0).val
      (homOfLE le_top : U ⟶ ⊤).op a
    change (scalarQuotientMap X α r 0).val.app (op U) (globalRestriction X U a) =
      (scalarQuotient X α r 0).val.map (homOfLE le_top : U ⟶ ⊤).op
        ((scalarQuotientMap X α r 0).val.app (op ⊤) a) at hn
    rw [ha] at hn
    exact hn.trans (hy 0).1
  · have hn := PresheafOfModules.naturality_apply (scalarQuotientMap X α r 0).val
      (homOfLE le_top : V ⟶ ⊤).op a
    change (scalarQuotientMap X α r 0).val.app (op V) (globalRestriction X V a) =
      (scalarQuotient X α r 0).val.map (homOfLE le_top : V ⟶ ⊤).op
        ((scalarQuotientMap X α r 0).val.app (op ⊤) a) at hn
    rw [ha] at hn
    exact hn.trans (hy 0).2

end GlobalPatchLift

section IdempotentPatch

variable (X : Scheme.{u}) {R : Type u} [CommRing R]
  (α : R →+* Γ(X, ⊤)) (r : R)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact evaluation of the scalar sequence gives actual divisibility
on every open, without assuming that evaluation preserves cokernels. -/
theorem exists_local_division_of_scalar_quotient_eq_zero
    [Mono (scalarPower X α (structureUnit X) r 0)]
    (U : X.Opens) (a : Γ(X, U))
    (ha : (scalarQuotientMap X α r 0).val.app (op U) a = 0) :
    ∃ b : Γ(X, U), globalRestriction X U (α r) * b = a := by
  let E : X.Modules ⥤ ModuleCat Γ(X, U) := SheafOfModules.evaluation X.ringCatSheaf (op U)
  have : PreservesLimits E := inferInstanceAs
    (PreservesLimits (SheafOfModules.evaluation X.ringCatSheaf (op U)))
  have hS := scalarSequence_shortExact X α (structureUnit X) r 0
  have hE := hS.exact.map_of_mono_of_preservesKernel E hS.mono_f inferInstance
  obtain ⟨b, hb⟩ := (ShortComplex.moduleCat_exact_iff _).mp hE a ha
  let b' : Γ(X, U) := b
  refine ⟨b', ?_⟩
  change globalRestriction X U (α (r ^ (0 + 1))) * b' = a at hb
  simpa only [zero_add, pow_one] using hb

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exists_division_of_scalar_quotient_eq_zero
    [Mono (scalarPower X α (structureUnit X) r 0)]
    (a : Γ(X, ⊤)) (ha : (scalarQuotientMap X α r 0).val.app (op ⊤) a = 0) :
    ∃ b : Γ(X, ⊤), α r * b = a := by
  simpa only [globalRestriction_top_apply] using
    exists_local_division_of_scalar_quotient_eq_zero X α r ⊤ a ha

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalar_quotient_idempotent_patch_eq_zero
    (a : Γ(X, ⊤)) (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (hU : (scalarQuotientMap X α r 0).val.app (op U) (globalRestriction X U a) =
      (scalarQuotientMap X α r 0).val.app (op U) (1 : Γ(X, U)))
    (hV : (scalarQuotientMap X α r 0).val.app (op V) (globalRestriction X V a) = 0) :
    (scalarQuotientMap X α r 0).val.app (op ⊤) (a * a - a) = 0 := by
  let Q := scalarQuotient X α r 0
  let q := scalarQuotientMap X α r 0
  apply TopCat.Sheaf.eq_of_locally_eq₂ ⟨Q.presheaf, Q.isSheaf⟩
    (homOfLE le_top : U ⟶ ⊤) (homOfLE le_top : V ⟶ ⊤) (by rw [hUV])
  · have hn := PresheafOfModules.naturality_apply q.val
      (homOfLE le_top : U ⟶ ⊤).op (a * a - a)
    change q.val.app (op U) (globalRestriction X U (a * a - a)) =
      Q.val.map (homOfLE le_top : U ⟶ ⊤).op (q.val.app (op ⊤) (a * a - a)) at hn
    change Q.val.map (homOfLE le_top : U ⟶ ⊤).op
      (q.val.app (op ⊤) (a * a - a)) = Q.val.map (homOfLE le_top : U ⟶ ⊤).op 0
    rw [map_zero, ← hn, map_sub, map_mul, map_sub]
    let b := globalRestriction X U a
    have hmul := (q.val.app (op U)).hom.map_smul b b
    change q.val.app (op U) (b * b) = b • q.val.app (op U) b at hmul
    rw [hmul, hU]
    have hone := (q.val.app (op U)).hom.map_smul b (1 : Γ(X, U))
    change q.val.app (op U) (b * (1 : Γ(X, U))) = b • q.val.app (op U) (1 : Γ(X, U)) at hone
    rw [mul_one] at hone
    rw [← hone, hU, sub_self]
  · have hn := PresheafOfModules.naturality_apply q.val
      (homOfLE le_top : V ⟶ ⊤).op (a * a - a)
    change q.val.app (op V) (globalRestriction X V (a * a - a)) =
      Q.val.map (homOfLE le_top : V ⟶ ⊤).op (q.val.app (op ⊤) (a * a - a)) at hn
    change Q.val.map (homOfLE le_top : V ⟶ ⊤).op
      (q.val.app (op ⊤) (a * a - a)) = Q.val.map (homOfLE le_top : V ⟶ ⊤).op 0
    rw [map_zero, ← hn, map_sub, map_mul, map_sub]
    let b := globalRestriction X V a
    have hmul := (q.val.app (op V)).hom.map_smul b b
    change q.val.app (op V) (b * b) = b • q.val.app (op V) b at hmul
    rw [hmul, hV, smul_zero, sub_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A one-zero scalar patch on a proper-style two-open cover lifts to an
actual global idempotent when global functions and H1 are finite over a
Noetherian Henselian local base with principal maximal ideal. -/
theorem exists_idempotent_two_open_patch [IsNoetherianRing R] [HenselianLocalRing R]
    (hgen : IsLocalRing.maximalIdeal R = Ideal.span {r})
    (hm : ∀ n, Mono (scalarPower X α (structureUnit X) r n))
    (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (hr : IsUnit (globalRestriction X (U ⊓ V) (α r))) :
    letI : Algebra R Γ(X, ⊤) := α.toAlgebra
    letI := moduleCohomologyModuleOfHom X α (structureUnit X) 1
    Module.Finite R Γ(X, ⊤) →
    Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf X (structureUnit X)) 1) →
    ∃ e : Γ(X, ⊤), IsIdempotentElem e ∧
      (scalarQuotientMap X α r 0).val.app (op U) (globalRestriction X U e) =
        (scalarQuotientMap X α r 0).val.app (op U) (1 : Γ(X, U)) ∧
      (scalarQuotientMap X α r 0).val.app (op V) (globalRestriction X V e) = 0 := by
  let : Algebra R Γ(X, ⊤) := α.toAlgebra
  let := moduleCohomologyModuleOfHom X α (structureUnit X) 1
  intro hfinite hH1
  let : Module.Finite R Γ(X, ⊤) := hfinite
  let : Mono (scalarPower X α (structureUnit X) r 0) := hm 0
  obtain ⟨a, hU, hV⟩ := exists_global_lift_of_two_open_patch X α r hm U V hUV hr hH1
  have hzero := scalar_quotient_idempotent_patch_eq_zero X α r a U V hUV hU hV
  obtain ⟨b, hb⟩ := exists_division_of_scalar_quotient_eq_zero X α r (a * a - a) hzero
  let I := (IsLocalRing.maximalIdeal R).map (algebraMap R Γ(X, ⊤))
  have hrI : α r ∈ I := Ideal.mem_map_of_mem _ (by
    rw [hgen]
    exact Ideal.mem_span_singleton_self r)
  have hdiff : a * a - a ∈ I := by
    rw [← hb]
    exact I.mul_mem_right _ hrI
  have hbar : IsIdempotentElem (Ideal.Quotient.mk I a) := by
    apply sub_eq_zero.mp
    rw [← map_mul, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hdiff
  obtain ⟨e, he, her⟩ := HenselianLocalRing.exists_idempotent_lift_of_finite R Γ(X, ⊤)
    (Ideal.Quotient.mk I a) hbar
  have hea : e - a ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, her, sub_self]
  have hI : I = Ideal.span {α r} := by
    dsimp only [I]
    rw [hgen, Ideal.map_span, Set.image_singleton]
    rfl
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (hI ▸ hea)
  have hc := congrArg
    (fun f : structureUnit X ⟶ scalarQuotient X α r 0 => f.val.app (op ⊤) d)
    (cokernel.condition (scalarPower X α (structureUnit X) r 0))
  change (scalarQuotientMap X α r 0).val.app (op ⊤)
    (globalRestriction X ⊤ (α (r ^ (0 + 1))) * d) = 0 at hc
  simp only [zero_add, pow_one, globalRestriction_top_apply] at hc
  have hq : (scalarQuotientMap X α r 0).val.app (op ⊤) e =
      (scalarQuotientMap X α r 0).val.app (op ⊤) a := by
    apply sub_eq_zero.mp
    rw [← map_sub, hd]
    exact hc
  have hw (W : X.Opens) :
      (scalarQuotientMap X α r 0).val.app (op W) (globalRestriction X W e) =
        (scalarQuotientMap X α r 0).val.app (op W) (globalRestriction X W a) := by
    have hn₁ := PresheafOfModules.naturality_apply (scalarQuotientMap X α r 0).val
      (homOfLE le_top : W ⟶ ⊤).op e
    have hn₂ := PresheafOfModules.naturality_apply (scalarQuotientMap X α r 0).val
      (homOfLE le_top : W ⟶ ⊤).op a
    exact hn₁.trans ((congrArg
      (fun x => (scalarQuotient X α r 0).val.map (homOfLE le_top : W ⟶ ⊤).op x)
      hq).trans hn₂.symm)
  exact ⟨e, he, (hw U).trans hU, (hw V).trans hV⟩

end IdempotentPatch

section ProperFlatInputs

variable {R : Type u} [CommRing R]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalar_unit_spec_mono [IsDomain R] (r : R) (hr : r ≠ 0) :
    Mono (scalarMap (Spec (.of R)) (structureUnit (Spec (.of R)))
      ((Scheme.ΓSpecIso (.of R)).inv r)) := by
  let S := Spec (.of R)
  let O := structureUnit S
  let a : Γ(S, ⊤) := (Scheme.ΓSpecIso (.of R)).inv r
  have ha : a ≠ 0 := by
    intro h
    apply hr
    calc
      r = (Scheme.ΓSpecIso (.of R)).hom a :=
        (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (.of R)) r).symm
      _ = 0 := by rw [h, map_zero]
  have hreg : IsSMulRegular Γ(O, ⊤) a := by
    intro x y hxy
    change a * (show Γ(S, ⊤) from x) = a * (show Γ(S, ⊤) from y) at hxy
    have he : (show Γ(S, ⊤) from x) = (show Γ(S, ⊤) from y) :=
      mul_left_cancel₀ ha hxy
    exact he
  let : O.IsQuasicoherent := Scheme.Modules.QuasiCoherent.quasicoherent_of_affineCharts O
    (fun A j _ => (Scheme.Modules.affineLocallyFiniteType_unit S A j).1)
  have hlocal (U : S.Opens) :
      IsSMulRegular Γ(O, U) (globalRestriction S U a) :=
    Scheme.Modules.QuasiCoherent.AffineOpenSections.isSMulRegular_restrict O
      (isAffineOpen_top S) hreg le_top
  constructor
  intro M f g hfg
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  apply hlocal U
  exact congrArg (fun h : M ⟶ O => h.val.app (op U) x) hfg

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Flatness of the actual structural morphism supplies monicity of every
nonzero scalar power on its original structure module. -/
theorem scalarPower_mono_of_flat [IsDomain R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Flat f]
    (r : R) (hr : r ≠ 0) (n : ℕ) :
    Mono (scalarPower X (f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
      (structureUnit X) r n) := by
  let a : Γ(Spec (.of R), ⊤) := (Scheme.ΓSpecIso (.of R)).inv (r ^ (n + 1))
  let m := scalarMap (Spec (.of R)) (structureUnit (Spec (.of R))) a
  have : Mono m := scalar_unit_spec_mono (r ^ (n + 1)) (pow_ne_zero _ hr)
  let : (structureUnit (Spec (.of R))).IsQuasicoherent :=
    Scheme.Modules.QuasiCoherent.quasicoherent_of_affineCharts (structureUnit (Spec (.of R)))
      (fun A j _ => (Scheme.Modules.affineLocallyFiniteType_unit (Spec (.of R)) A j).1)
  have : Mono ((Scheme.Modules.pullback f).map m) :=
    Scheme.Modules.QuasiCoherent.mono_pullback_affineTarget f m
  have hmono : Mono ((Scheme.Modules.pullback f).map m ≫
      (Scheme.Modules.pullbackUnitIso f).hom) := inferInstance
  rw [Scheme.Modules.Invertible.ScalarAutomorphisms.pullback_scalar_unit] at hmono
  rw [mono_comp_iff_of_isIso] at hmono
  exact hmono

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Proper Noetherian finiteness transfers to the actual global-section
algebra, using the original structural ring map. -/
theorem globalSections_finite_of_proper [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] :
    letI : Algebra R Γ(X, ⊤) :=
      (f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
    Module.Finite R Γ(X, ⊤) := by
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let : Algebra R Γ(X, ⊤) := α.toAlgebra
  let := moduleCohomologyModuleOfHom X α (structureUnit X) 0
  have : Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf X (structureUnit X)) 0) :=
    moduleCohomology_finite_of_proper R f (structureUnit X)
      (Scheme.Modules.affineLocallyFiniteType_unit X) 0
  exact Module.Finite.equiv (moduleH0EquivOfHom X α (structureUnit X))

end ProperFlatInputs

section ClopenLifting

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem principal_closedFiber_range (r : R)
    (hgen : IsLocalRing.maximalIdeal R = Ideal.span {r}) :
    Set.range (LocalRing.ResidueFiber.projection f) =
      (X.basicOpen (f.appTop ((Scheme.ΓSpecIso (.of R)).inv r)) : Set X)ᶜ := by
  classical
  have hb : f ⁻¹ᵁ PrimeSpectrum.basicOpen r =
      X.basicOpen (f.appTop ((Scheme.ΓSpecIso (.of R)).inv r)) := by
    have he : (Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv r) =
        (show (Spec (.of R)).Opens from PrimeSpectrum.basicOpen r) :=
      basicOpen_eq_of_affine (R := CommRingCat.of R) r
    exact (congrArg (fun U : (Spec (.of R)).Opens => f ⁻¹ᵁ U) he.symm).trans
      (Scheme.preimage_basicOpen_top f _)
  rw [Scheme.Pullback.range_fst, ← hb]
  ext x
  change f x ∈ Set.range (LocalRing.residueSpecMap R) ↔ ¬r ∉ (f x).asIdeal
  rw [not_not]
  constructor
  · rintro ⟨z, hz⟩
    have he : LocalRing.residueSpecMap R z = IsLocalRing.closedPoint R :=
      IsLocalRing.PrimeSpectrum.comap_residue R z
    rw [← hz, he]
    change r ∈ IsLocalRing.maximalIdeal R
    rw [hgen]
    exact Ideal.mem_span_singleton_self r
  · intro hr
    have he : IsLocalRing.maximalIdeal R = (f x).asIdeal :=
      (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le Ideal.IsPrime.ne_top'
        (by rw [hgen]; exact (Ideal.span_singleton_le_iff_mem _).mpr hr)
    refine ⟨IsLocalRing.closedPoint (IsLocalRing.ResidueField R), ?_⟩
    rw [show LocalRing.residueSpecMap R (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) =
      IsLocalRing.closedPoint R from IsLocalRing.comap_closedPoint (IsLocalRing.residue R)]
    exact PrimeSpectrum.ext he

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem isUnit_globalRestriction_of_le_basicOpen (a : Γ(X, ⊤))
    (U : X.Opens) (hU : U ≤ X.basicOpen a) : IsUnit (globalRestriction X U a) := by
  have hu := (X.toRingedSpace.isUnit_res_basicOpen a).map
    (X.presheaf.map (homOfLE hU).op).hom
  change IsUnit (X.presheaf.map (homOfLE hU).op
    (X.presheaf.map (homOfLE (X.basicOpen_le a)).op a)) at hu
  have he : X.presheaf.map (homOfLE hU).op
      (X.presheaf.map (homOfLE (X.basicOpen_le a)).op a) = globalRestriction X U a := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  exact he ▸ hu

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem evaluation_globalRestriction (U : X.Opens) (x : X) (hx : x ∈ U)
    (a : Γ(X, ⊤)) :
    X.evaluation U x hx (globalRestriction X U a) = X.Γevaluation x a := by
  change X.residue x (X.presheaf.germ U x hx
      (X.presheaf.map (homOfLE le_top).op a)) =
    X.residue x (X.presheaf.germ ⊤ x trivial a)
  rw [TopCat.Presheaf.germ_res_apply]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem isClosed_basicOpen_of_idempotent (e : Γ(X, ⊤)) (he : IsIdempotentElem e) :
    IsClosed (X.basicOpen e : Set X) := by
  rw [← X.toSpecΓ_preimage_basicOpen e]
  exact (PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩).isClosed.preimage X.toSpecΓ.continuous

end ClopenLifting

section ProperClopenLifting

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [HenselianLocalRing R]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every actual clopen of the closed fibre of a proper flat scheme over a
Noetherian Henselian local domain with principal maximal ideal lifts to a
clopen of the same scheme. -/
theorem exists_clopen_closedFiber_lift (r : R) (hr : r ≠ 0)
    (hgen : IsLocalRing.maximalIdeal R = Ideal.span {r})
    (W : (LocalRing.ResidueFiber.obj f).Opens)
    (hW : IsClosed (W : Set (LocalRing.ResidueFiber.obj f))) :
    ∃ U : X.Opens, IsClosed (U : Set X) ∧ LocalRing.ResidueFiber.projection f ⁻¹ᵁ U = W := by
  classical
  let i := LocalRing.ResidueFiber.projection f
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let A : Set X := i '' (W : Set (LocalRing.ResidueFiber.obj f))
  let B : Set X := i '' (W : Set (LocalRing.ResidueFiber.obj f))ᶜ
  have hA : IsClosed A := i.isClosedMap _ hW
  have hB : IsClosed B := i.isClosedMap _ W.isOpen.isClosed_compl
  let U : X.Opens := ⟨Bᶜ, hB.isOpen_compl⟩
  let V : X.Opens := ⟨Aᶜ, hA.isOpen_compl⟩
  have hAB (x : X) (ha : x ∈ A) (hb : x ∈ B) : False := by
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, hba⟩ := hb
    have he : b = a := i.isClosedEmbedding.injective hba
    exact hb (he.symm ▸ ha)
  have hUV : U ⊔ V = ⊤ := by
    ext x
    change (x ∉ B ∨ x ∉ A) ↔ True
    simp only [iff_true]
    by_cases hx : x ∈ B
    · exact Or.inr (fun ha => hAB x ha hx)
    · exact Or.inl hx
  have hRange : Set.range i = (X.basicOpen (α r) : Set X)ᶜ :=
    principal_closedFiber_range f r hgen
  have hOverlap : U ⊓ V ≤ X.basicOpen (α r) := by
    intro x hx
    by_contra hn
    have hxi : x ∈ Set.range i := by rw [hRange]; exact hn
    obtain ⟨z, rfl⟩ := hxi
    by_cases hz : z ∈ W
    · exact hx.2 ⟨z, hz, rfl⟩
    · exact hx.1 ⟨z, hz, rfl⟩
  have hunit := isUnit_globalRestriction_of_le_basicOpen (α r) (U ⊓ V) hOverlap
  have hm (n : ℕ) : Mono (scalarPower X α (structureUnit X) r n) :=
    scalarPower_mono_of_flat f r hr n
  let : Algebra R Γ(X, ⊤) := α.toAlgebra
  have hfinite : Module.Finite R Γ(X, ⊤) := globalSections_finite_of_proper f
  let := moduleCohomologyModuleOfHom X α (structureUnit X) 1
  have hH1 : Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf X (structureUnit X)) 1) :=
    moduleCohomology_finite_of_proper R f (structureUnit X)
      (Scheme.Modules.affineLocallyFiniteType_unit X) 1
  obtain ⟨e, he, heU, heV⟩ := exists_idempotent_two_open_patch X α r
    hgen hm U V hUV hunit hfinite hH1
  let : Mono (scalarPower X α (structureUnit X) r 0) := hm 0
  refine ⟨X.basicOpen e, isClosed_basicOpen_of_idempotent e he, ?_⟩
  ext z
  change i z ∈ X.basicOpen e ↔ z ∈ W
  have htr : X.Γevaluation (i z) (α r) = 0 := by
    apply (X.evaluation_eq_zero_iff_notMem_basicOpen (U := ⊤) (i z) trivial (α r)).mpr
    have hz : i z ∈ Set.range i := ⟨z, rfl⟩
    rw [hRange] at hz
    exact hz
  by_cases hzW : z ∈ W
  · have hzU : i z ∈ U := by
      intro hzB
      exact hAB (i z) ⟨z, hzW, rfl⟩ hzB
    have hzero : (scalarQuotientMap X α r 0).val.app (op U)
        (globalRestriction X U e - (1 : Γ(X, U))) = 0 := by
      rw [map_sub, heU, sub_self]
    obtain ⟨b, hb⟩ := exists_local_division_of_scalar_quotient_eq_zero X α r U
      (globalRestriction X U e - (1 : Γ(X, U))) hzero
    have hv := congrArg (fun a : Γ(X, U) => X.evaluation U (i z) hzU a) hb
    rw [map_mul, evaluation_globalRestriction, htr, zero_mul, map_sub,
      evaluation_globalRestriction, map_one] at hv
    have heval : X.Γevaluation (i z) e = 1 := sub_eq_zero.mp hv.symm
    have hmem : i z ∈ X.basicOpen e :=
      (X.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) (i z) trivial e).mp
        (by rw [heval]; exact one_ne_zero)
    exact ⟨fun _ => hzW, fun _ => hmem⟩
  · have hzV : i z ∈ V := by
      rintro ⟨z', hz', heq⟩
      exact hzW (i.isClosedEmbedding.injective heq ▸ hz')
    obtain ⟨b, hb⟩ := exists_local_division_of_scalar_quotient_eq_zero X α r V
      (globalRestriction X V e) heV
    have hv := congrArg (fun a : Γ(X, V) => X.evaluation V (i z) hzV a) hb
    rw [map_mul, evaluation_globalRestriction, htr, zero_mul,
      evaluation_globalRestriction] at hv
    have hnot : i z ∉ X.basicOpen e :=
      (X.evaluation_eq_zero_iff_notMem_basicOpen (U := ⊤) (i z) trivial e).mp hv.symm
    exact ⟨fun h => (hnot h).elim, fun h => (hzW h).elim⟩

end ProperClopenLifting


section ProperGraphLift

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [HenselianLocalRing R]
  {Y : Scheme.{u}} (π : Y ⟶ Spec (.of R)) [IsProper π] [Flat π]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exists_residue_subcover_lift (r : R) (hr : r ≠ 0)
    (hgen : IsLocalRing.maximalIdeal R = Ideal.span {r}) (P : FiniteEtale Y)
    {T : FiniteEtale (LocalRing.ResidueFiber.obj π)}
    (m : T ⟶ (baseChange (LocalRing.ResidueFiber.projection π)).obj P) [Mono m] :
    ∃ (W : FiniteEtale Y) (j : W ⟶ P)
      (e : T ≅ (baseChange (LocalRing.ResidueFiber.projection π)).obj W),
      e.hom ≫ (baseChange (LocalRing.ResidueFiber.projection π)).map j = m := by
  let c := LocalRing.residueSpecMap R
  let i := LocalRing.ResidueFiber.projection π
  let F := baseChange i
  let : IsOpenImmersion m.hom.left := Connectedness.isOpenImmersion_of_mono m
  let a := pullbackRightPullbackFstIso π c P.obj.hom
  let U₀ := m.hom.left.opensRange
  have hU₀ : IsClosed (U₀ : Set (F.obj P).obj.left) :=
    (Connectedness.hom_range_isClopen m).isClosed
  let V₀ := a.inv ⁻¹ᵁ U₀
  have hV₀ : IsClosed (V₀ : Set (LocalRing.ResidueFiber.obj (P.obj.hom ≫ π))) :=
    hU₀.preimage a.inv.continuous
  obtain ⟨U, hU, hrestrict⟩ := exists_clopen_closedFiber_lift (P.obj.hom ≫ π)
    r hr hgen V₀ hV₀
  have hpre : pullback.fst P.obj.hom i ⁻¹ᵁ U = U₀ := by
    calc
      _ = a.hom ⁻¹ᵁ (LocalRing.ResidueFiber.projection (P.obj.hom ≫ π) ⁻¹ᵁ U) := by
        rw [← Scheme.Hom.comp_preimage]
        exact congrArg (fun q => q ⁻¹ᵁ U)
          (pullbackRightPullbackFstIso_hom_fst π c P.obj.hom).symm
      _ = a.hom ⁻¹ᵁ (a.inv ⁻¹ᵁ U₀) := by rw [hrestrict]
      _ = U₀ := by rw [← Scheme.Hom.comp_preimage, Iso.hom_inv_id]; rfl
  let W := Connectedness.clopenCover P U hU
  let j : W ⟶ P := Connectedness.clopenCoverι P U hU
  let j₀ := F.map j
  let : IsOpenImmersion j.hom.left := by change IsOpenImmersion U.ι; infer_instance
  let : IsOpenImmersion j₀.hom.left :=
    MorphismProperty.of_isPullback (baseChange_map_isPullback i j).flip inferInstance
  have hj : Set.range j.hom.left = (U : Set P.obj.left) := by
    change Set.range U.ι = (U : Set P.obj.left)
    exact Scheme.Opens.range_ι U
  have heq : Set.range m.hom.left = Set.range j₀.hom.left := by
    rw [baseChange_map_range, hj]
    exact (congrArg (fun V : (F.obj P).obj.left.Opens => (V : Set (F.obj P).obj.left)) hpre).symm
  exact ⟨W, j, coverIsoOfRangeEq m j₀ heq, coverIsoOfRangeEq_hom m j₀ heq⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The literal finite-etale closed-fibre pullback of a proper flat model
over a Noetherian Henselian local domain is full when the maximal ideal has
a supplied nonzero generator. No cover-algebraization premise is used. -/
theorem closedFiber_baseChange_full_of_principal (r : R) (hr : r ≠ 0)
    (hgen : IsLocalRing.maximalIdeal R = Ideal.span {r}) :
    (baseChange (pullback.fst π (LocalRing.residueSpecMap R))).Full where
  map_surjective {C D} φ := by
    let i := LocalRing.ResidueFiber.projection π
    let F := baseChange i
    let P := productCover C D
    let m : F.obj C ⟶ F.obj P := residueGraph i φ
    have : Mono (m ≫ F.map (productFirst C D)) := by
      rw [residueGraph_first]
      infer_instance
    let : Mono m := mono_of_mono m (F.map (productFirst C D))
    obtain ⟨W, j, e, he⟩ := exists_residue_subcover_lift π r hr hgen P m
    let p : W ⟶ C := j ≫ productFirst C D
    have hep : e.hom ≫ F.map p = 𝟙 (F.obj C) := by
      rw [Functor.map_comp, ← Category.assoc, he]
      exact residueGraph_first i φ
    have hpmap : F.map p = e.inv := by
      apply (cancel_epi e.hom).mp
      rw [hep, Iso.hom_inv_id]
    have : IsIso (F.map p) := by rw [hpmap]; infer_instance
    have : IsIso p := isIso_of_reflects_iso p F
    have hinv : F.map (inv p) = e.hom := by
      apply (cancel_mono (F.map p)).mp
      have hl : F.map (inv p) ≫ F.map p = 𝟙 _ := by
        rw [← Functor.map_comp, IsIso.inv_hom_id]
        exact F.map_id C
      exact hl.trans hep.symm
    refine ⟨inv p ≫ j ≫ productSecond C D, ?_⟩
    change F.map (inv p ≫ j ≫ productSecond C D) = φ
    rw [Functor.map_comp, Functor.map_comp, hinv, ← Category.assoc, he]
    exact residueGraph_second i φ

end ProperGraphLift

section DVR

variable {R : Type u} [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] [HenselianLocalRing R]
  {Y : Scheme.{u}} (π : Y ⟶ Spec (.of R)) [IsProper π] [Flat π]

/-- Actual finite-etale closed-fibre pullback is full for every proper flat
model over a Henselian DVR. This does not assert essential surjectivity. -/
instance closedFiber_baseChange_full_of_henselianDVR :
    (baseChange (pullback.fst π (LocalRing.residueSpecMap R))).Full := by
  obtain ⟨r, hr⟩ := IsDiscreteValuationRing.exists_irreducible R
  exact closedFiber_baseChange_full_of_principal π r hr.ne_zero hr.maximalIdeal_eq

end DVR

end AlgebraicGeometry.Scheme.FiniteEtale.ProperResidue
