/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.CoefficientExactness
public import Mathlib.Tactic.Abel

/-!
# Original coefficient sequences and their trace-duality adjoints

The exact rows use the actual native coefficient maps and unsigned extension
classes. Native value equations are fixed before presentation substitution.
The positive-ZMod dual reverses the original compact rows on arbitrary
carriers. The top and middle adjoint transfers are then proved on those SAME
rows. Proper and open finite-local-system applications supply their geometric
vanishing and cover-unit pairings separately.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u wU wX wA uC vC wC

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients Scheme.OverField

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard moduleSheafExtZModModule

section SourceChase
variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{wU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)]
/-- Whole coefficient naturality for the ORIGINAL adjoint, on its canonical
Ext scalar parents. It follows by evaluating the proved trace-pairing law. -/
theorem moduleDualityMap_naturality
    {F F' : ModuleSheaf U (ULift.{u + 1} (ZMod n))} (f : F ⟶ F')
    (r : ℕ) (hr : r ≤ 2) :
    (moduleDualityMap X hX D hfin hclosed j hD n hn hunit hinv F' r hr).comp
        (AddMonoidHom.toZModLinearMap n
          ((Ext.mk₀ ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).map f)).postcomp
            (moduleUnit X.left (ULift.{u + 1} (ZMod n))) (add_zero r))) =
      (AddMonoidHom.toZModLinearMap n
        ((Ext.mk₀ f).precomp (moduleRootsOfUnity U n) (zero_add (2 - r)))).dualMap.comp
          (moduleDualityMap X hX D hfin hclosed j hD n hn hunit hinv F r hr) := by
  have h := moduleTracePairingLinearMap_naturality X hX D hfin hclosed j hD
    n hn hunit hinv f r (2 - r) (by lia)
  ext c e
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) e
/-- The original compact-zero/source-one unsigned boundary square, in native
adjoint form. No supplied commutativity equation or signed Ext.δ is used. -/
theorem moduleDualityMap_zero_one_extClass
    {S : ShortComplex (ModuleSheaf U (ULift.{u + 1} (ZMod n)))} (hS : S.ShortExact) :
    (moduleDualityMap X hX D hfin hclosed j hD n hn hunit hinv S.X₁ 1 (by decide)).comp
        (AddMonoidHom.toZModLinearMap n
          ((shortExact_moduleLowerShriek j (ULift.{u + 1} (ZMod n)) hS).extClass.postcomp
            (moduleUnit X.left (ULift.{u + 1} (ZMod n))) (show 0 + 1 = 1 from rfl))) =
      (AddMonoidHom.toZModLinearMap n
        (hS.extClass.precomp (moduleRootsOfUnity U n) (show 1 + 1 = 2 from rfl))).dualMap.comp
          (moduleDualityMap X hX D hfin hclosed j hD n hn hunit hinv S.X₃ 0 (by decide)) := by
  have h := moduleTracePairingLinearMap_extClass X hX D hfin hclosed j hD n hn hunit hinv
    hS 0 1 1 2 rfl rfl rfl rfl
  ext c e
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) e

end SourceChase

private theorem originalAddMonoidHom_toZModLinearMap_apply
    (n : ℕ) {M : Type uC} {N : Type vC} [AddCommGroup M] [AddCommGroup N]
    [Module (ZMod n) M] [Module (ZMod n) N] (f : M →+ N) (x : M) :
    (AddMonoidHom.toZModLinearMap n f) x = f x := rfl

private theorem originalExt_precomp_apply
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{wC} C]
    {A B N : C} (f : A ⟶ B) (q : ℕ) (e : Ext.{wC} B N q) :
    ((Ext.mk₀ f).precomp N (zero_add q)) e = (Ext.mk₀ f).comp e (zero_add q) := rfl

section TopTransposeExactness

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{wU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)]

/-- Evaluation of the original whole naturality law at a variable coefficient
map, before any presentation or local row aliases are substituted. -/
private theorem moduleDualityTransposeMap_two_naturality_apply
    {F G : ModuleSheaf U (ULift.{u + 1} (ZMod n))} (f : F ⟶ G)
    (b : Ext.{wU} G (moduleRootsOfUnity U n) 2) :
    moduleDualityTransposeMap.{u, wU, wX, wA} X hX D hfin hclosed j hD
      n hn hunit hinv F 2 le_rfl ((Ext.mk₀ f).comp b (zero_add 2)) =
    (AddMonoidHom.toZModLinearMap n
      ((Ext.mk₀ ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).map f)).postcomp
        (moduleUnit X.left (ULift.{u + 1} (ZMod n))) (add_zero 0))).dualMap
      (moduleDualityTransposeMap.{u, wU, wX, wA} X hX D hfin hclosed j hD
        n hn hunit hinv G 2 le_rfl b) := by
  have h := LinearMap.congr_fun
    (moduleDualityTransposeMap_naturality.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv f 2 le_rfl) b
  simpa only [LinearMap.comp_apply, originalAddMonoidHom_toZModLinearMap_apply,
    originalExt_precomp_apply] using h

/-- Surjectivity of the original source-degree-two adjoint descends to an
actual subcoefficient. Self-injectivity of the existing positive ZMod scalar
ring extends functionals along the original compact degree-zero injection. -/
theorem moduleDualityTransposeMap_two_surjective_of_shortExact
    {S : ShortComplex (ModuleSheaf U (ULift.{u + 1} (ZMod n)))} (hS : S.ShortExact)
    (hB : Function.Surjective (moduleDualityTransposeMap.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv S.X₂ 2 le_rfl)) :
    Function.Surjective (moduleDualityTransposeMap.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv S.X₁ 2 le_rfl) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let i := AddMonoidHom.toZModLinearMap n
    ((Ext.mk₀ ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).map S.f)).postcomp
      (moduleUnit X.left (ULift.{u + 1} (ZMod n))) (add_zero 0))
  let : Mono ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).map S.f) :=
    (shortExact_moduleLowerShriek j (ULift.{u + 1} (ZMod n)) hS).mono_f
  have hi : Function.Injective i :=
    Ext.postcomp_mk₀_injective_of_mono (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).map S.f)
  intro l
  obtain ⟨v, hv⟩ := ZMod.dualMap_surjective n i hi l
  obtain ⟨b, hb⟩ := hB v
  refine ⟨(Ext.mk₀ S.f).comp b (zero_add 2), ?_⟩
  have h := moduleDualityTransposeMap_two_naturality_apply.{u, wU, wX, wA}
    X hX D hfin hclosed j hD n hn hunit hinv S.f b
  have hFinal := h.trans ((congrArg i.dualMap hb).trans hv)
  exact hFinal

/-- Once source-degree-two surjectivity is known uniformly, the original
cofree sequence gives injectivity. The sole extra vanishing is original E3
of its actual cokernel; the dual row uses the same positive-ZMod action. -/
theorem moduleDualityTransposeMap_two_injective_of_shortExact
    {S : ShortComplex (ModuleSheaf U (ULift.{u + 1} (ZMod n)))} (hS : S.ShortExact)
    [Subsingleton (Ext.{wU} S.X₃ (moduleRootsOfUnity U n) 3)]
    (hB : Function.Injective (moduleDualityTransposeMap.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv S.X₂ 2 le_rfl))
    (hC : Function.Surjective (moduleDualityTransposeMap.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv S.X₃ 2 le_rfl)) :
    Function.Injective (moduleDualityTransposeMap.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv S.X₁ 2 le_rfl) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let i := AddMonoidHom.toZModLinearMap n
    ((Ext.mk₀ ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).map S.f)).postcomp
      (moduleUnit X.left (ULift.{u + 1} (ZMod n))) (add_zero 0))
  let g := AddMonoidHom.toZModLinearMap n
    ((Ext.mk₀ ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).map S.g)).postcomp
      (moduleUnit X.left (ULift.{u + 1} (ZMod n))) (add_zero 0))
  have hig : Function.Exact i g := by
    have h := Ext.covariant_sequence_exact₂' (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      (shortExact_moduleLowerShriek j (ULift.{u + 1} (ZMod n)) hS) 0
    rw [ShortComplex.ab_exact_iff_function_exact] at h
    exact h
  apply (injective_iff_map_eq_zero _).mpr
  intro e he
  obtain ⟨b, hb⟩ := Ext.contravariant_sequence_exact₁ hS (moduleRootsOfUnity U n)
    e (show 1 + 2 = 3 from rfl) (Subsingleton.elim _ _)
  let v := moduleDualityTransposeMap.{u, wU, wX, wA} X hX D hfin hclosed j hD
    n hn hunit hinv S.X₂ 2 le_rfl b
  have hiv : i.dualMap v = 0 := by
    have h := moduleDualityTransposeMap_two_naturality_apply.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv S.f b
    have hInput := congrArg (moduleDualityTransposeMap.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv S.X₁ 2 le_rfl) hb
    have hFinal := h.symm.trans (hInput.trans he)
    exact hFinal
  obtain ⟨vC, hvC⟩ := (ZMod.dualMap_exact n i g hig v).mp hiv
  obtain ⟨c, hc⟩ := hC vC
  have hcb : (Ext.mk₀ S.g).comp c (zero_add 2) = b := by
    apply hB
    have h := moduleDualityTransposeMap_two_naturality_apply.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv S.g c
    have hFinal := h.trans ((congrArg g.dualMap hc).trans hvC)
    exact hFinal
  rw [← hb, ← hcb, Ext.mk₀_comp_mk₀_assoc, S.zero, Ext.mk₀_zero, Ext.zero_comp]

end TopTransposeExactness

private theorem originalExt_precomp_any_apply
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{wC} C]
    {A B N : C} {p q r : ℕ} (d : Ext.{wC} A B p) (h : p + q = r)
    (e : Ext.{wC} B N q) : d.precomp N h e = d.comp e h := rfl

section MiddleTransposeExactness

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{wU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)]

private theorem moduleDualityTransposeMap_one_naturality_apply
    {F G : ModuleSheaf U (ULift.{u + 1} (ZMod n))} (f : F ⟶ G)
    (b : Ext.{wU} G (moduleRootsOfUnity U n) 1) :
    moduleDualityTransposeMap.{u, wU, wX, wA} X hX D hfin hclosed j hD
      n hn hunit hinv F 1 (by decide) ((Ext.mk₀ f).comp b (zero_add 1)) =
    (AddMonoidHom.toZModLinearMap n
      ((Ext.mk₀ ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).map f)).postcomp
        (moduleUnit X.left (ULift.{u + 1} (ZMod n))) (add_zero 1))).dualMap
      (moduleDualityTransposeMap.{u, wU, wX, wA} X hX D hfin hclosed j hD
        n hn hunit hinv G 1 (by decide) b) := by
  have h := LinearMap.congr_fun
    (moduleDualityTransposeMap_naturality.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv f 1 (by decide)) b
  simpa only [LinearMap.comp_apply, originalAddMonoidHom_toZModLinearMap_apply,
    originalExt_precomp_apply] using h

private theorem moduleDualityTransposeMap_one_two_boundary_apply
    {S : ShortComplex (ModuleSheaf U (ULift.{u + 1} (ZMod n)))} (hS : S.ShortExact)
    (e : Ext.{wU} S.X₁ (moduleRootsOfUnity U n) 1) :
    moduleDualityTransposeMap.{u, wU, wX, wA} X hX D hfin hclosed j hD
      n hn hunit hinv S.X₃ 2 le_rfl (hS.extClass.comp e (show 1 + 1 = 2 from rfl)) =
    (AddMonoidHom.toZModLinearMap n
      ((shortExact_moduleLowerShriek j (ULift.{u + 1} (ZMod n)) hS).extClass.postcomp
        (moduleUnit X.left (ULift.{u + 1} (ZMod n))) (show 0 + 1 = 1 from rfl))).dualMap
      (moduleDualityTransposeMap.{u, wU, wX, wA} X hX D hfin hclosed j hD
        n hn hunit hinv S.X₁ 1 (by decide) e) := by
  have h := LinearMap.congr_fun
    (moduleDualityTransposeMap_extClass.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv hS 1 (by decide)) e
  dsimp only [ShortComplex.map] at h ⊢
  simpa only [LinearMap.comp_apply, originalAddMonoidHom_toZModLinearMap_apply,
    originalExt_precomp_any_apply] using h

/-- The original unsigned boundary row gives source-degree-one surjectivity
on an actual subcoefficient after source-degree-two is known. -/
theorem moduleDualityTransposeMap_one_surjective_of_shortExact
    {S : ShortComplex (ModuleSheaf U (ULift.{u + 1} (ZMod n)))} (hS : S.ShortExact)
    (hB₁ : Function.Surjective (moduleDualityTransposeMap.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv S.X₂ 1 (by decide)))
    (hC₂ : Function.Surjective (moduleDualityTransposeMap.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv S.X₃ 2 le_rfl))
    (hB₂ : Function.Injective (moduleDualityTransposeMap.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv S.X₂ 2 le_rfl)) :
    Function.Surjective (moduleDualityTransposeMap.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv S.X₁ 1 (by decide)) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let A := moduleUnit X.left (ULift.{u + 1} (ZMod n))
  let dc := AddMonoidHom.toZModLinearMap n
    ((shortExact_moduleLowerShriek j (ULift.{u + 1} (ZMod n)) hS).extClass.postcomp
      (moduleUnit X.left (ULift.{u + 1} (ZMod n))) (show 0 + 1 = 1 from rfl))
  let cf := AddMonoidHom.toZModLinearMap n
    ((Ext.mk₀ ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).map S.f)).postcomp
      (moduleUnit X.left (ULift.{u + 1} (ZMod n))) (add_zero 1))
  let cg := AddMonoidHom.toZModLinearMap n
    ((Ext.mk₀ ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).map S.g)).postcomp
      (moduleUnit X.left (ULift.{u + 1} (ZMod n))) (add_zero 0))
  have hgd : Function.Exact cg dc := by
    have h := Ext.covariant_sequence_exact₃' A (shortExact_moduleLowerShriek j _ hS) 0 1 rfl
    rw [ShortComplex.ab_exact_iff_function_exact] at h
    exact h
  have hdf : Function.Exact dc cf := by
    have h := Ext.covariant_sequence_exact₁' A (shortExact_moduleLowerShriek j _ hS) 0 1 rfl
    rw [ShortComplex.ab_exact_iff_function_exact] at h
    exact h
  intro l
  obtain ⟨a, ha⟩ := hC₂ (dc.dualMap l)
  have hzero : (Ext.mk₀ S.g).comp a (zero_add 2) = 0 := by
    apply hB₂
    rw [map_zero]
    have h := moduleDualityTransposeMap_two_naturality_apply.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv S.g a
    have hdual : cg.dualMap (dc.dualMap l) = 0 :=
      (ZMod.dualMap_exact n cg dc hgd _).mpr ⟨l, rfl⟩
    have hFinal := h.trans ((congrArg cg.dualMap ha).trans hdual)
    exact hFinal
  obtain ⟨e, he⟩ := Ext.contravariant_sequence_exact₃ hS (moduleRootsOfUnity U n)
    a hzero (n₀ := 1) rfl
  let v := moduleDualityTransposeMap.{u, wU, wX, wA} X hX D hfin hclosed j hD
    n hn hunit hinv S.X₁ 1 (by decide) e
  have hδ : dc.dualMap (l - v) = 0 := by
    have h := moduleDualityTransposeMap_one_two_boundary_apply.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv hS e
    rw [he, ha] at h
    rw [map_sub]
    exact sub_eq_zero.mpr h
  obtain ⟨vB, hvB⟩ := (ZMod.dualMap_exact n dc cf hdf _).mp hδ
  obtain ⟨b, hb⟩ := hB₁ vB
  refine ⟨e + (Ext.mk₀ S.f).comp b (zero_add 1), ?_⟩
  have h := moduleDualityTransposeMap_one_naturality_apply.{u, wU, wX, wA}
    X hX D hfin hclosed j hD n hn hunit hinv S.f b
  have hb' := h.trans ((congrArg cf.dualMap hb).trans hvB)
  rw [map_add, hb']
  change v + (l - v) = l
  abel

/-- Uniform degree-one surjectivity on the cokernel and the original
unsigned boundary yield injectivity, without an H1 killing premise. -/
theorem moduleDualityTransposeMap_one_injective_of_shortExact
    {S : ShortComplex (ModuleSheaf U (ULift.{u + 1} (ZMod n)))} (hS : S.ShortExact)
    (hB₁ : Function.Injective (moduleDualityTransposeMap.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv S.X₂ 1 (by decide)))
    (hC₁ : Function.Surjective (moduleDualityTransposeMap.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv S.X₃ 1 (by decide)))
    (hC₂ : Function.Injective (moduleDualityTransposeMap.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv S.X₃ 2 le_rfl)) :
    Function.Injective (moduleDualityTransposeMap.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv S.X₁ 1 (by decide)) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let cf := AddMonoidHom.toZModLinearMap n
    ((Ext.mk₀ ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).map S.f)).postcomp
      (moduleUnit X.left (ULift.{u + 1} (ZMod n))) (add_zero 1))
  let cg := AddMonoidHom.toZModLinearMap n
    ((Ext.mk₀ ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).map S.g)).postcomp
      (moduleUnit X.left (ULift.{u + 1} (ZMod n))) (add_zero 1))
  have hfg : Function.Exact cf cg := by
    have h := Ext.covariant_sequence_exact₂' (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      (shortExact_moduleLowerShriek j (ULift.{u + 1} (ZMod n)) hS) 1
    rw [ShortComplex.ab_exact_iff_function_exact] at h
    exact h
  apply (injective_iff_map_eq_zero _).mpr
  intro e he
  have hde : hS.extClass.comp e (show 1 + 1 = 2 from rfl) = 0 := by
    apply hC₂
    rw [map_zero]
    have h := moduleDualityTransposeMap_one_two_boundary_apply.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv hS e
    rw [he, map_zero] at h
    exact h
  obtain ⟨b, hb⟩ := Ext.contravariant_sequence_exact₁ hS (moduleRootsOfUnity U n)
    e (show 1 + 1 = 2 from rfl) hde
  let v := moduleDualityTransposeMap.{u, wU, wX, wA} X hX D hfin hclosed j hD
    n hn hunit hinv S.X₂ 1 (by decide) b
  have hfv : cf.dualMap v = 0 := by
    have h := moduleDualityTransposeMap_one_naturality_apply.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv S.f b
    have hInput := congrArg (moduleDualityTransposeMap.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv S.X₁ 1 (by decide)) hb
    have hFinal := h.symm.trans (hInput.trans he)
    exact hFinal
  obtain ⟨vC, hvC⟩ := (ZMod.dualMap_exact n cf cg hfg _).mp hfv
  obtain ⟨c, hc⟩ := hC₁ vC
  have hcb : (Ext.mk₀ S.g).comp c (zero_add 1) = b := by
    apply hB₁
    have h := moduleDualityTransposeMap_one_naturality_apply.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv S.g c
    have hFinal := h.trans ((congrArg cg.dualMap hc).trans hvC)
    exact hFinal
  rw [← hb, ← hcb, Ext.mk₀_comp_mk₀_assoc, S.zero, Ext.mk₀_zero, Ext.zero_comp]

end MiddleTransposeExactness

end AlgebraicGeometry.Scheme.EtaleCohomology
