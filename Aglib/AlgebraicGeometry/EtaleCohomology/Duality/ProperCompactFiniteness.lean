/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.ConstantOnePerfectness
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.FiniteTracePairing
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteEtalePresentation
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.Tactic.IntervalCases

/-!
# Finiteness of original proper compact cohomology for finite local systems

The original unit groups, finite unit powers and actual finite-cover unit
comparison supply the base groups. The native cofree mono gives degree zero;
the native free epi and genuine kernel C3 vanishing give degree two; the
original compact exact row gives degree one. The argument does not assume
general local-system duality, reflexivity or a rank formula. All group scalars
remain the existing ZMod action on the original unit-Ext carriers.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u wX wA a b c

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients Scheme.OverField

attribute [local instance] hasSheafifyLarge hasSheafifyModules moduleSheafExtZModModule
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard
  Abelian.hasFiniteBiproducts

private theorem finite_middle_of_exact_zmod (n : ℕ) [NeZero n]
    {A : Type a} {B : Type b} {C : Type c}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module (ZMod n) A] [Module (ZMod n) B] [Module (ZMod n) C]
    [Finite A] [Finite C] (f : A →ₗ[ZMod n] B) (g : B →ₗ[ZMod n] C)
    (hfg : Function.Exact f g) : Finite B := by
  let : Module.Finite (ZMod n) A := Module.Finite.of_finite
  let : Finite (LinearMap.range g) := inferInstance
  let : Module.Finite (ZMod n) (LinearMap.range g) := Module.Finite.of_finite
  have h' : Function.Exact f g.rangeRestrict := by
    intro x
    constructor
    · intro hx
      have hzero : g x = 0 := congrArg Subtype.val hx
      exact (hfg x).mp hzero
    · intro hx
      apply Subtype.ext
      exact (hfg x).mpr hx
  have hg : Function.Surjective g.rangeRestrict := by
    intro z
    obtain ⟨x, hx⟩ := z.property
    exact ⟨x, Subtype.ext hx⟩
  let : Module.Finite (ZMod n) B := Module.Finite.of_exact h' hg
  exact Module.finite_of_finite (ZMod n)

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
  [HasExt.{wX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)]

omit hX hn [IsAlgClosed k]
  [HasExt.{wX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)] in
include hunit in
private theorem proper_finite_level_unit : IsUnit (n : Γ(X.left, ⊤)) := by
  simpa only [map_natCast] using
    hunit.map (((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop).hom)

include hX hn hunit

private theorem proper_unit_source_two_finite :
    Finite (Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      (moduleRootsOfUnity X.left n) 2) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let Λ := ULift.{u + 1} (ZMod n)
  let A := moduleUnit X.left Λ
  let N := moduleRootsOfUnity X.left n
  let E : Ext.{wX} A N 2 ≃+
      Ext.{wX} A ((moduleLowerShriek (𝟙 X.left) Λ).obj N) 2 :=
    ((extFunctorObj A 2).mapIso
      ((moduleLowerShriekIdIso Λ X.left).app N).symm).addCommGroupIsoToAddEquiv
  let T := moduleCompactSupportTraceAddEquiv.{u, wX, wA}
    X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp) n hn hunit
      (proper_finite_level_unit X n hunit)
  exact Finite.of_injective (E.trans T) (E.trans T).injective

private theorem proper_unit_compact_finite (q : ℕ) (hq : q ≤ 2) :
    Finite (Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek (𝟙 X.left) (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit X.left (ULift.{u + 1} (ZMod n)))) q) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  interval_cases q
  · let : Finite (Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
        (moduleRootsOfUnity X.left n) 2) := proper_unit_source_two_finite X hX n hn hunit
    have h := moduleDualityMap_unit_zero_isPerfPair.{u, wX, wX, wA}
      X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp) n hn hunit
        (proper_finite_level_unit X n hunit)
    exact Finite.of_injective _ h.bijective_left.injective
  · exact (moduleUnit_one_finite_and_natCard_eq.{u, wX, wX, wA} X hX n hn hunit).2.1
  · let Λ := ULift.{u + 1} (ZMod n)
    let A := moduleUnit X.left Λ
    let L := moduleLowerShriek (𝟙 X.left) Λ
    let E : Ext.{wX} A (L.obj (moduleUnit X.left Λ)) 2 ≃+
        Ext.{wX} A (L.obj (moduleRootsOfUnity X.left n)) 2 :=
      ((extFunctorObj A 2).mapIso
        (L.mapIso (moduleUnitRootsIso k n hn hunit X.hom))).addCommGroupIsoToAddEquiv
    let T := moduleCompactSupportTraceAddEquiv.{u, wX, wA}
      X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp) n hn hunit
        (proper_finite_level_unit X n hunit)
    exact Finite.of_injective (E.trans T) (E.trans T).injective

private theorem proper_unit_power_compact_finite (m q : ℕ) (hq : q ≤ 2) :
    Finite (Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek (𝟙 X.left) (ULift.{u + 1} (ZMod n))).obj
        (⨁ fun _ : Fin m => moduleUnit X.left (ULift.{u + 1} (ZMod n)))) q) := by
  let Λ := ULift.{u + 1} (ZMod n)
  let A := moduleUnit X.left Λ
  let L := moduleLowerShriek (𝟙 X.left) Λ
  let P := fun _ : Fin m => moduleUnit X.left Λ
  let (i : Fin m) : Finite (Ext.{wX} A ((L.obj ∘ P) i) q) := by
    change Finite (Ext.{wX} A (L.obj (moduleUnit X.left Λ)) q)
    exact proper_unit_compact_finite X hX n hn hunit q hq
  let E : Ext.{wX} A (L.obj (⨁ P)) q ≃+
      ∀ i : Fin m, Ext.{wX} A ((L.obj ∘ P) i) q :=
    Ext.addEquivBiproduct A
      (Functor.mapFiniteBiconeIsBilimit L (biproduct.isBilimit P)) q
  exact Finite.of_injective E E.injective

omit [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)] in
private theorem proper_lowerShriek_unit_power_compact_finite
    (Y : Scheme.FiniteEtale X.left) [ConnectedSpace Y.obj.left]
    (m q : ℕ) (hq : q ≤ 2) :
    Finite (Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek (𝟙 X.left) (ULift.{u + 1} (ZMod n))).obj
        ((moduleLowerShriek Y.obj.hom (ULift.{u + 1} (ZMod n))).obj
          (⨁ fun _ : Fin m => moduleUnit Y.obj.left (ULift.{u + 1} (ZMod n))))) q) := by
  let : ConnectedSpace X.left := Curve.curveProperties_connectedSpace hX
  let Z : FScheme k := Over.mk (Y.obj.hom ≫ X.hom)
  let hZ : Curve.Properties Z := Curves.curveProperties_of_connected_finiteEtale X hX Y
  let hExtY : HasExt.{u + 2}
      (ModuleSheaf Y.obj.left (ULift.{u + 1} (ZMod n))) :=
    SheafOfModules.hasExt (constantRing Y.obj.left (ULift.{u + 1} (ZMod n)))
  let : HasExt.{u + 2} (ModuleSheaf Y.obj.left (ULift.{u + 1} (ZMod n))) := hExtY
  let : HasExt.{u + 2} (ModuleSheaf Z.left (ULift.{u + 1} (ZMod n))) := hExtY
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Z.left) := hasExtStandard Z.left
  let P := ⨁ fun _ : Fin m => moduleUnit Y.obj.left (ULift.{u + 1} (ZMod n))
  let x : X.left := Classical.ofNonempty
  let d := Y.obj.hom.finrank x
  have hd : ∀ z : X.left, Y.obj.hom.finrank z = d := fun z =>
    Y.obj.hom.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace z x
  let : Finite (Ext.{u + 2} (moduleUnit Y.obj.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek (𝟙 Y.obj.left) (ULift.{u + 1} (ZMod n))).obj P) q) :=
    proper_unit_power_compact_finite.{u, u + 2, u + 2} Z hZ n hn hunit m q hq
  let E : Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek (𝟙 X.left) (ULift.{u + 1} (ZMod n))).obj
        ((moduleLowerShriek Y.obj.hom (ULift.{u + 1} (ZMod n))).obj P)) q ≃+
      Ext.{u + 2} (moduleUnit Y.obj.left (ULift.{u + 1} (ZMod n)))
        ((moduleLowerShriek (𝟙 Y.obj.left) (ULift.{u + 1} (ZMod n))).obj P) q :=
    moduleFiniteLowerShriekCompactExtAddEquiv.{u, wX, u + 2} Y.obj.hom n d hd P q
  exact Finite.of_injective E E.injective

omit [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)] in
private theorem proper_directImage_unit_power_compact_finite
    (Y : Scheme.FiniteEtale X.left) [ConnectedSpace Y.obj.left]
    (m q : ℕ) (hq : q ≤ 2) :
    Finite (Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek (𝟙 X.left) (ULift.{u + 1} (ZMod n))).obj
        ((moduleDirectImage Y.obj.hom (ULift.{u + 1} (ZMod n))).obj
          (⨁ fun _ : Fin m => moduleUnit Y.obj.left (ULift.{u + 1} (ZMod n))))) q) := by
  let : ConnectedSpace X.left := Curve.curveProperties_connectedSpace hX
  let Λ := ULift.{u + 1} (ZMod n)
  let A := moduleUnit X.left Λ
  let L := moduleLowerShriek (𝟙 X.left) Λ
  let P := ⨁ fun _ : Fin m => moduleUnit Y.obj.left Λ
  let x : X.left := Classical.ofNonempty
  let d := Y.obj.hom.finrank x
  have hd : ∀ z : X.left, Y.obj.hom.finrank z = d := fun z =>
    Y.obj.hom.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace z x
  let : Finite (Ext.{wX} A (L.obj ((moduleLowerShriek Y.obj.hom Λ).obj P)) q) :=
    proper_lowerShriek_unit_power_compact_finite X hX n hn hunit Y m q hq
  let E : Ext.{wX} A (L.obj ((moduleDirectImage Y.obj.hom Λ).obj P)) q ≃+
      Ext.{wX} A (L.obj ((moduleLowerShriek Y.obj.hom Λ).obj P)) q :=
    ((extFunctorObj A q).mapIso
      (L.mapIso ((moduleFiniteEtaleLowerShriekDirectImageIso Y.obj.hom n d hd).app P).symm))
        |>.addCommGroupIsoToAddEquiv
  exact Finite.of_injective E E.injective

omit [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)] in
private theorem proper_compact_zero_finite
    (F : ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))
    (hF : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence X.left (ULift.{u + 1} (ZMod n))).inverse.obj F)) :
    Finite (Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek (𝟙 X.left) (ULift.{u + 1} (ZMod n))).obj F) 0) := by
  let : ConnectedSpace X.left := Curve.curveProperties_connectedSpace hX
  obtain ⟨Y, _, hc, _, m, a, ha⟩ := exists_galois_unit_biproduct_directImage_mono n hn F hF
  let : ConnectedSpace Y.obj.left := hc
  let : Mono a := ha
  let Λ := ULift.{u + 1} (ZMod n)
  let A := moduleUnit X.left Λ
  let L := moduleLowerShriek (𝟙 X.left) Λ
  let : Finite (Ext.{wX} A (L.obj ((moduleDirectImage Y.obj.hom Λ).obj
      (⨁ fun _ : Fin m => moduleUnit Y.obj.left Λ))) 0) :=
    proper_directImage_unit_power_compact_finite X hX n hn hunit Y m 0 (by decide)
  have hi := Ext.postcomp_mk₀_injective_of_mono A (L.map a)
  exact Finite.of_injective _ hi

private theorem proper_compact_two_finite
    (F : ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))
    (hF : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence X.left (ULift.{u + 1} (ZMod n))).inverse.obj F)) :
    Finite (Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek (𝟙 X.left) (ULift.{u + 1} (ZMod n))).obj F) 2) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : ConnectedSpace X.left := Curve.curveProperties_connectedSpace hX
  obtain ⟨Y, _, hc, _, m, a, ha⟩ := exists_galois_unit_biproduct_lowerShriek_epi n hn F hF
  let : ConnectedSpace Y.obj.left := hc
  let Λ := ULift.{u + 1} (ZMod n)
  let A := moduleUnit X.left Λ
  let L := moduleLowerShriek (𝟙 X.left) Λ
  let P := ⨁ fun _ : Fin m => moduleUnit Y.obj.left Λ
  let x : X.left := Classical.ofNonempty
  let d := Y.obj.hom.finrank x
  have hd : ∀ z : X.left, Y.obj.hom.finrank z = d := fun z =>
    Y.obj.hom.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace z x
  have hBLC := (Constructible.Modules.isFiniteTypeLocallyConstant_iff_of_iso
    ((moduleSheafEquivalence X.left Λ).inverse.mapIso
      ((moduleFiniteEtaleLowerShriekDirectImageIso Y.obj.hom n d hd).app P))).mpr
    (moduleDirectImage_isFiniteTypeLocallyConstant Λ Y.obj.hom P
      (moduleUnitBiproduct_isFiniteTypeLocallyConstant Y.obj.left Λ m))
  have hKLC := moduleKernel_isFiniteTypeLocallyConstant X.left Λ a hBLC hF
  let S := ShortComplex.kernelSequence a
  have hS : S.ShortExact := { exact := ShortComplex.kernelSequence_exact a, epi_g := ha }
  let : Subsingleton (Ext.{wX} A
      (S.map (moduleLowerShriek (𝟙 X.left) Λ)).X₁ 3) := by
    change Subsingleton (Ext.{wX} A (L.obj S.X₁) 3)
    exact moduleUnitCompactIdExt_subsingleton_of_finiteLocallyConstant.{u, wX, wA}
      X hX n hn hunit S.X₁ hKLC 3 (by decide)
  let : Finite (Ext.{wX} A (L.obj S.X₂) 2) :=
    proper_lowerShriek_unit_power_compact_finite X hX n hn hunit Y m 2 (by decide)
  have hs : Function.Surjective ((Ext.mk₀ (L.map S.g)).postcomp A (add_zero 2)) := by
    intro z
    obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₃ A
      (shortExact_moduleLowerShriek (𝟙 X.left) Λ hS) z
      (show 2 + 1 = 3 from rfl) (Subsingleton.elim _ _)
    exact ⟨b, hb⟩
  exact Finite.of_surjective _ hs

/-- Every original proper compact unit-Ext group of a finite local system is
finite. Positive composite levels and level one are included. The proof uses
actual coefficient epis/monos and exact rows, not general duality/reflexivity. -/
theorem moduleUnitCompactIdExt_finite_of_finiteLocallyConstant
    (F : ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))
    (hF : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence X.left (ULift.{u + 1} (ZMod n))).inverse.obj F)) (q : ℕ) :
    Finite (Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek (𝟙 X.left) (ULift.{u + 1} (ZMod n))).obj F) q) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  by_cases hq : q ≤ 2
  · interval_cases q
    · exact proper_compact_zero_finite X hX n hn hunit F hF
    · let : ConnectedSpace X.left := Curve.curveProperties_connectedSpace hX
      obtain ⟨Y, _, hc, _, m, a, ha⟩ := exists_galois_unit_biproduct_lowerShriek_epi n hn F hF
      let : ConnectedSpace Y.obj.left := hc
      let Λ := ULift.{u + 1} (ZMod n)
      let A := moduleUnit X.left Λ
      let L := moduleLowerShriek (𝟙 X.left) Λ
      let P := ⨁ fun _ : Fin m => moduleUnit Y.obj.left Λ
      let x : X.left := Classical.ofNonempty
      let d := Y.obj.hom.finrank x
      have hd : ∀ z : X.left, Y.obj.hom.finrank z = d := fun z =>
        Y.obj.hom.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace z x
      have hBLC := (Constructible.Modules.isFiniteTypeLocallyConstant_iff_of_iso
        ((moduleSheafEquivalence X.left Λ).inverse.mapIso
          ((moduleFiniteEtaleLowerShriekDirectImageIso Y.obj.hom n d hd).app P))).mpr
        (moduleDirectImage_isFiniteTypeLocallyConstant Λ Y.obj.hom P
          (moduleUnitBiproduct_isFiniteTypeLocallyConstant Y.obj.left Λ m))
      have hKLC := moduleKernel_isFiniteTypeLocallyConstant X.left Λ a hBLC hF
      let S := ShortComplex.kernelSequence a
      have hS : S.ShortExact := { exact := ShortComplex.kernelSequence_exact a, epi_g := ha }
      let : Finite (Ext.{wX} A (L.obj S.X₂) 1) :=
        proper_lowerShriek_unit_power_compact_finite X hX n hn hunit Y m 1 (by decide)
      let : Finite (Ext.{wX} A (L.obj S.X₁) 2) :=
        proper_compact_two_finite X hX n hn hunit S.X₁ hKLC
      let f : Ext.{wX} A (L.obj S.X₂) 1 →ₗ[ZMod n] Ext.{wX} A (L.obj S.X₃) 1 :=
        AddMonoidHom.toZModLinearMap n ((Ext.mk₀ (L.map S.g)).postcomp A (add_zero 1))
      let g : Ext.{wX} A (L.obj S.X₃) 1 →ₗ[ZMod n] Ext.{wX} A (L.obj S.X₁) 2 :=
        AddMonoidHom.toZModLinearMap n
          ((shortExact_moduleLowerShriek (𝟙 X.left) Λ hS).extClass.postcomp A
            (show 1 + 1 = 2 from rfl))
      have hfg : Function.Exact f g := by
        have h := Ext.covariant_sequence_exact₃' A
          (shortExact_moduleLowerShriek (𝟙 X.left) Λ hS) 1 2 rfl
        rw [ShortComplex.ab_exact_iff_function_exact] at h
        exact h
      exact finite_middle_of_exact_zmod n f g hfg
    · exact proper_compact_two_finite X hX n hn hunit F hF
  · let : Subsingleton (Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
        ((moduleLowerShriek (𝟙 X.left) (ULift.{u + 1} (ZMod n))).obj F) q) :=
      moduleUnitCompactIdExt_subsingleton_of_finiteLocallyConstant.{u, wX, wA}
        X hX n hn hunit F hF q (by omega)
    infer_instance

end AlgebraicGeometry.Scheme.EtaleCohomology
