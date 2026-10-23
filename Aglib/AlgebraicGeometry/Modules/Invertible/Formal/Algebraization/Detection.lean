/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FullFaithful
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.PullbackQuotient
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.QuotientCompletionUnit
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.Finite.Quotient
public import Aglib.AlgebraicGeometry.Modules.Coherent.FinitePresentation
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.StructureQuotient

/-!
# Detecting actual ideal sheaves by proper completion

The original positive geometric reductions detect isomorphisms and zero
coherent modules. Applied to the actual structure-module quotient, this
reflects the zero and unit ideal-sheaf conditions. The base ideal is arbitrary;
the base is Noetherian and complete for that ideal, and the morphism is proper.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Invertible

open Coherent

universe u

private theorem isZero_of_killedBy_top {X : Scheme.{u}} (M : X.Modules)
    (h : killedByIdealSheaf ⊤ M) : IsZero M := by
  apply (IsZero.iff_id_eq_zero M).mpr
  apply moduleHom_ext_affine
  intro U
  ext m
  simpa using h U 1 (by trivial) m

private theorem idealSheafQuotient_top_isZero {X : Scheme.{u}} (M : X.Modules) :
    IsZero ((idealSheafQuotientFunctor X ⊤).obj M) :=
  isZero_of_killedBy_top _ (idealSheafQuotient_killed X ⊤ M)

private theorem idealSheafQuotientUnit_bot_isIso {X : Scheme.{u}} (M : X.Modules) :
    IsIso ((idealSheafQuotientUnit X ⊥).app M) := by
  apply (pullbackPushforwardUnit_isIso_iff_killedByIdealSheaf
    (⊥ : X.IdealSheafData).subschemeι M).mpr
  rw [IdealSheafData.ker_subschemeι]
  intro U a ha m
  have ha' : a = 0 := ha
  rw [ha', zero_smul]

section Proper

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  (I : Ideal R) [IsAdicComplete I R] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]

/-- The original positive geometric reductions detect isomorphisms of
coherent modules on a proper scheme over a complete Noetherian base. -/
theorem isIso_of_positiveThickening_pullback_isIso {M N : X.CoherentSheaf}
    (φ : M ⟶ N)
    (hφ : ∀ n : ℕ, 0 < n →
      IsIso ((pullback (idealThickeningι f (I ^ n))).map φ.hom)) : IsIso φ := by
  let K := idealThickeningIdealSheaf f I
  let C := completionFunctor X K
  have hcomp : ∀ n : ℕ,
      IsIso ((idealSheafQuotientFunctor X (K ^ n)).map φ.hom) := by
    intro n
    by_cases hn : n = 0
    · subst n
      rw [show K ^ (0 : ℕ) = ⊤ by ext V : 2; simp]
      exact (idealSheafQuotient_top_isZero M.obj).isIso
        (idealSheafQuotient_top_isZero N.obj) _
    · let a := (idealThickeningSubschemeIso f (I ^ n)).hom
      have hbase : IsIso ((pullback (idealThickeningι f (I ^ n))).map φ.hom) :=
        hφ n (Nat.pos_of_ne_zero hn)
      have hiter : IsIso ((pullback a).map
          ((pullback (idealThickeningι f (I ^ n))).map φ.hom)) := inferInstance
      have hc : IsIso ((pullback (a ≫ idealThickeningι f (I ^ n))).map φ.hom) :=
        (NatIso.isIso_map_iff (pullbackComp a _) φ.hom).mp hiter
      have he : a ≫ idealThickeningι f (I ^ n) =
          (idealThickeningIdealSheaf f (I ^ n)).subschemeι :=
        idealThickeningSubschemeIso_hom_ι f (I ^ n)
      rw [he] at hc
      have : IsIso ((pullback (K ^ n).subschemeι).map φ.hom) := by
        rw [show K ^ n = idealThickeningIdealSheaf f (I ^ n) from
          idealThickeningIdealSheaf_pow f I n]
        exact hc
      exact inferInstanceAs
        (IsIso ((pushforward (K ^ n).subschemeι).map
          ((pullback (K ^ n).subschemeι).map φ.hom)))
  have : ∀ n : ℕᵒᵖ, IsIso ((C.map φ).hom.app n) := fun n => hcomp n.unop
  have : IsIso (C.map φ).hom := NatIso.isIso_of_isIso_app _
  have : IsIso ((adicSystemToDiagram X K).map (C.map φ)) := this
  have : IsIso (C.map φ) := isIso_of_reflects_iso _ (adicSystemToDiagram X K)
  let ff := Scheme.Cohomology.completionFunctorFullyFaithful I f
  let := ff.full
  let := ff.faithful
  exact isIso_of_reflects_iso φ C

/-- Vanishing on the original positive thickenings detects a zero coherent
module. The detection uses the original zero endomorphism. -/
theorem isZero_of_positiveThickening_pullback_isZero (M : X.CoherentSheaf)
    (hM : ∀ n : ℕ, 0 < n →
      IsZero ((pullback (idealThickeningι f (I ^ n))).obj M.obj)) : IsZero M.obj := by
  have : IsIso (0 : M ⟶ M) :=
    isIso_of_positiveThickening_pullback_isIso I f 0 (fun n hn =>
      (hM n hn).isIso (hM n hn) _)
  have : IsIso (0 : M.obj ⟶ M.obj) :=
    inferInstanceAs (IsIso ((QuasiCoherent.affineLocallyFiniteType X).ι.map (0 : M ⟶ M)))
  exact (isIsoZero_iff_source_target_isZero M.obj M.obj).mp this |>.1

/-- The zero ideal is detected by its actual pullbacks to every positive
thickening of a proper scheme over a complete Noetherian base. -/
theorem idealSheaf_eq_bot_of_positiveThickening_comap_eq_bot (J : X.IdealSheafData)
    (hJ : ∀ n : ℕ, 0 < n → J.comap (idealThickeningι f (I ^ n)) = ⊥) : J = ⊥ := by
  let U : X.CoherentSheaf :=
    ⟨SheafOfModules.unit X.ringCatSheaf, Coherent.Support.unit_coherent X⟩
  have : U.obj.IsQuasicoherent := Coherent.coherent_obj_quasicoherent U
  let q := idealSheafCoherentQuotientUnit X J U
  have : IsIso q := by
    apply isIso_of_positiveThickening_pullback_isIso I f q
    intro n hn
    let i := idealThickeningι f (I ^ n)
    let e := idealSheafPullbackQuotientIso i J U.obj
    have : IsIso ((pullback i).map q.hom ≫ e.hom) := by
      change IsIso ((pullback i).map ((idealSheafQuotientUnit X J).app U.obj) ≫
        (idealSheafPullbackQuotientIso i J U.obj).hom)
      rw [idealSheafPullbackQuotientIso_unit]
      change IsIso ((idealSheafQuotientUnit _ (J.comap i)).app _)
      rw [hJ n hn]
      exact idealSheafQuotientUnit_bot_isIso _
    exact IsIso.of_isIso_comp_right _ e.hom
  have : IsIso q.hom := inferInstanceAs
    (IsIso ((QuasiCoherent.affineLocallyFiniteType X).ι.map q))
  have hkill : killedByIdealSheaf J U.obj := by
    have h := (pullbackPushforwardUnit_isIso_iff_killedByIdealSheaf J.subschemeι U.obj).mp
      (show IsIso ((idealSheafQuotientUnit X J).app U.obj) from inferInstanceAs (IsIso q.hom))
    simpa only [IdealSheafData.ker_subschemeι] using h
  apply bot_unique
  intro V a ha
  change a = 0
  simpa only [smul_eq_mul, mul_one] using hkill V a ha (1 : Γ(X, V))

/-- The unit ideal is detected by its actual pullbacks to every positive
thickening of a proper scheme over a complete Noetherian base. -/
theorem idealSheaf_eq_top_of_positiveThickening_comap_eq_top (J : X.IdealSheafData)
    (hJ : ∀ n : ℕ, 0 < n → J.comap (idealThickeningι f (I ^ n)) = ⊤) : J = ⊤ := by
  let U : X.CoherentSheaf :=
    ⟨SheafOfModules.unit X.ringCatSheaf, Coherent.Support.unit_coherent X⟩
  have : U.obj.IsQuasicoherent := Coherent.coherent_obj_quasicoherent U
  let Q := idealSheafCoherentQuotient X J U
  have hQ : IsZero Q.obj := by
    apply isZero_of_positiveThickening_pullback_isZero I f Q
    intro n hn
    let i := idealThickeningι f (I ^ n)
    let e := idealSheafPullbackQuotientIso i J U.obj
    apply IsZero.of_iso (Y := (idealSheafQuotientFunctor _ (J.comap i)).obj
      ((pullback i).obj U.obj)) _ e
    rw [hJ n hn]
    exact idealSheafQuotient_top_isZero _
  have hq : (idealSheafQuotientUnit X J).app U.obj = 0 := hQ.eq_of_tgt _ _
  have hs : Scheme.Hom.structureModuleMap J.subschemeι = 0 := by
    have h := pullbackUnitIso_homEquiv J.subschemeι
    change (idealSheafQuotientUnit X J).app U.obj ≫
      (pushforward J.subschemeι).map (pullbackUnitIso J.subschemeι).hom =
        Scheme.Hom.structureModuleMap J.subschemeι at h
    rw [hq, zero_comp] at h
    exact h.symm
  apply top_unique
  intro V a _
  rw [← IdealSheafData.ker_subschemeι J, Scheme.Hom.ker_apply]
  change J.subschemeι.app V.val a = 0
  exact congrArg (fun g => g.val.app (op V.val) a) hs

end Proper

end AlgebraicGeometry.Scheme.Modules.Invertible
