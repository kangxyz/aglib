/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Algebra.Module.ZMod
public import Aglib.RepresentationTheory.PGroup
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Short-exact induction for finite modules with p-group action

Let `R` be a ring and `G` a finite p-group. Every finitely generated
`R`-linear representation killed by `p` is built by short exact extensions
of trivial finite representations killed by `p`. The proof chooses a finite
prime-field stable subspace spanning the module over `R`. An invariant vector
in that space generates a trivial cyclic `R`-submodule; the image of the stable
space in the actual quotient has strictly smaller prime-field dimension.

The original module need not be finite-dimensional over the prime field or
finite as a set. No Noetherian hypothesis is needed, since the submodules used
at each step are cyclic and the other terms are actual module quotients.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u g v

namespace Representation

variable (p : ℕ) [Fact p.Prime] {R : Type u} [Ring R]
  {M : Type v} [AddCommGroup M] [Module R M] [Module (ZMod p) M]
  [Module.Finite R M] {G : Type g} [Group G] [Finite G]

/-- Finite generation over the original ring supplies a finite stable
prime-field subspace spanning the module. The original ring itself need not
be an algebra over the prime field. -/
theorem exists_finiteDimensional_stable_span_zmod (ρ : Representation R G M) :
    ∃ W : Submodule (ZMod p) M, Module.Finite (ZMod p) W ∧
      (∀ g x, x ∈ W → ρ g x ∈ W) ∧ Submodule.span R (W : Set M) = ⊤ := by
  classical
  obtain ⟨s, hs, hspan⟩ := Submodule.fg_def.mp (Module.Finite.fg_top (R := R) (M := M))
  let := hs.fintype
  let O : Set M := Set.range (fun a : G × s ↦ ρ a.1 a.2.val)
  let W : Submodule (ZMod p) M := Submodule.span (ZMod p) O
  have hO : O.Finite := Set.finite_range _
  have hW : Module.Finite (ZMod p) W := Module.Finite.of_fg (Submodule.fg_span hO)
  have hstable (g : G) :
      W ≤ W.comap ((ρ g).toAddMonoidHom.toZModLinearMap p) := by
    apply Submodule.span_le.mpr
    rintro x ⟨⟨h, y⟩, rfl⟩
    change ρ g (ρ h y.val) ∈ W
    apply Submodule.subset_span
    refine ⟨(g * h, y), ?_⟩
    exact congrArg (fun f : Module.End R M ↦ f y.val) (ρ.map_mul g h)
  refine ⟨W, hW, fun g x hx ↦ hstable g hx, ?_⟩
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  intro x hx
  apply Submodule.subset_span
  apply Submodule.subset_span
  refine ⟨(1, ⟨x, hx⟩), ?_⟩
  exact congrArg (fun f : Module.End R M ↦ f x) ρ.map_one

end Representation

namespace Rep

section Ring

variable {R : Type u} [Ring R] {G : Type g} [Group G]

/-- The actual inclusion and quotient of a stable submodule are short exact,
with no field hypothesis on the coefficient ring. -/
theorem shortExact_subtype_mkQ (A : Rep.{v} R G) (W : Submodule R A)
    (hW : ∀ g, W ≤ W.comap (A.ρ g)) :
    (ShortComplex.mk (A.subtype W hW) (A.mkQ W hW) (by
      ext x
      exact (Submodule.Quotient.mk_eq_zero W).mpr x.property)).ShortExact := by
  let S := ShortComplex.mk (A.subtype W hW) (A.mkQ W hW) (by
    ext x
    exact (Submodule.Quotient.mk_eq_zero W).mpr x.property)
  change S.ShortExact
  have hmono : Mono S.f := (mono_iff_injective S.f).2 W.subtype_injective
  have hepi : Epi S.g := (epi_iff_surjective S.g).2 W.mkQ_surjective
  refine { exact := ?_, mono_f := hmono, epi_g := hepi }
  apply (S.exact_map_iff_of_faithful (forget₂ (Rep.{v} R G) (ModuleCat.{v} R))).mp
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hxW : x ∈ W := (Submodule.Quotient.mk_eq_zero W).mp hx
  exact ⟨⟨x, hxW⟩, rfl⟩

end Ring

section PrimeKilled

variable (p : ℕ) [Fact p.Prime] {R : Type u} [Ring R]
  {G : Type g} [Group G]

/-- Short-exact induction from a finite-dimensional stable prime-field
subspace spanning the original module over its coefficient ring. -/
theorem induction_of_finite_stable_span_trivial_subobject (hG : IsPGroup p G)
    (P : Rep.{v} R G → Prop)
    (htrivial : ∀ A : Rep.{v} R G, ∀ [Module.Finite R A],
      (∀ x : A, p • x = 0) → A.IsTrivial → P A)
    (hstep : ∀ S : ShortComplex (Rep.{v} R G),
      S.ShortExact → Module.Finite R S.X₁ → (∀ x : S.X₁, p • x = 0) →
        S.X₁.IsTrivial → P S.X₃ → P S.X₂)
    (A : Rep.{v} R G) [Module.Finite R A]
    [Module (ZMod p) A]
    (W : Submodule (ZMod p) A) [Module.Finite (ZMod p) W]
    (hstable : ∀ g x, x ∈ W → A.ρ g x ∈ W)
    (hspan : Submodule.span R (W : Set A) = ⊤) : P A := by
  suffices h : ∀ n : ℕ, ∀ B : Rep.{v} R G, ∀ [Module.Finite R B],
      ∀ [Module (ZMod p) B],
      ∀ V : Submodule (ZMod p) B, ∀ [Module.Finite (ZMod p) V],
      (∀ g x, x ∈ V → B.ρ g x ∈ V) →
      Submodule.span R (V : Set B) = ⊤ → Module.finrank (ZMod p) V = n → P B from
    h _ A W hstable hspan rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro B _ _ V _ hV hspanV hdim
    rcases subsingleton_or_nontrivial V with hzero | hnonzero
    · have hVzero : V = ⊥ := Submodule.subsingleton_iff_eq_bot.mp hzero
      have hBzero : (⊤ : Submodule R B) = ⊥ := by
        rw [← hspanV, hVzero]
        simp
      have hB : Subsingleton B := ⟨fun x y => by
        have hx : x = 0 := (Submodule.mem_bot R).mp (hBzero ▸ Submodule.mem_top)
        have hy : y = 0 := (Submodule.mem_bot R).mp (hBzero ▸ Submodule.mem_top)
        exact hx.trans hy.symm⟩
      let := hB
      apply htrivial B (ZModModule.char_nsmul_eq_zero p)
      constructor
      intro g
      exact Subsingleton.elim _ _
    · let := hnonzero
      let ρV : Representation (ZMod p) G V := {
        toFun g := ((B.ρ g).toAddMonoidHom.toZModLinearMap p).restrict
          (fun x hx => hV g x hx)
        map_one' := by
          apply LinearMap.ext
          intro x
          apply Subtype.ext
          exact congrArg (fun f : Module.End R B => f (x : B)) B.ρ.map_one
        map_mul' g h := by
          apply LinearMap.ext
          intro x
          apply Subtype.ext
          exact congrArg (fun f : Module.End R B => f (x : B)) (B.ρ.map_mul g h) }
      obtain ⟨x, hx, hfix⟩ :=
        Representation.exists_ne_zero_invariant_of_isPGroup p ρV hG
      have hfixB (g : G) : B.ρ g (x : B) = (x : B) :=
        congrArg Subtype.val (hfix g)
      let N : Submodule R B := Submodule.span R {(x : B)}
      have hNfix (g : G) (y : B) (hy : y ∈ N) : B.ρ g y = y := by
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
        rw [map_smul, hfixB]
      let hN : ∀ g, N ≤ N.comap (B.ρ g) := fun g y hy => by
        change B.ρ g y ∈ N
        rw [hNfix g y hy]
        exact hy
      let S := ShortComplex.mk (B.subtype N hN) (B.mkQ N hN) (by
        ext y
        exact (Submodule.Quotient.mk_eq_zero N).mpr y.property)
      apply hstep S (shortExact_subtype_mkQ B N hN)
      · exact inferInstanceAs (Module.Finite R (Submodule.span R {(x : B)}))
      · intro y
        apply Subtype.ext
        exact ZModModule.char_nsmul_eq_zero p (y : B)
      · constructor
        intro g
        ext y
        exact hNfix g y y.property
      · have hQ : ∀ y : B ⧸ N, p • y = 0 := by
          intro y
          obtain ⟨z, rfl⟩ := N.mkQ_surjective y
          rw [← map_nsmul, ZModModule.char_nsmul_eq_zero p z, map_zero]
        let qModule := AddCommGroup.zmodModule (n := p) hQ
        let q : B →ₗ[ZMod p] B ⧸ N := N.mkQ.toAddMonoidHom.toZModLinearMap p
        let V' : Submodule (ZMod p) (B ⧸ N) := V.map q
        have hV' : ∀ (g : G) (y : B ⧸ N), y ∈ V' → S.X₃.ρ g y ∈ V' := by
          intro g y hy
          obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
          exact Submodule.mem_map.mpr ⟨B.ρ g z, hV g z hz, rfl⟩
        have hspanV' : Submodule.span R (V' : Set (B ⧸ N)) = ⊤ := by
          change Submodule.span R (N.mkQ '' (V : Set B)) = ⊤
          rw [← Submodule.map_span, hspanV, Submodule.map_top,
            LinearMap.range_eq_top.mpr N.mkQ_surjective]
        have hdrop : Module.finrank (ZMod p) V' < Module.finrank (ZMod p) V := by
          by_contra hn
          have hdis := Submodule.disjoint_ker_of_finrank_le q (Nat.le_of_not_gt hn)
          have hxker : (x : B) ∈ LinearMap.ker q := by
            change N.mkQ (x : B) = 0
            apply (Submodule.Quotient.mk_eq_zero N).mpr
            exact Submodule.subset_span (by simp)
          exact hx (Subtype.ext (Submodule.disjoint_def.mp hdis x x.property hxker))
        let : Module.Finite R S.X₃ :=
          inferInstanceAs (Module.Finite R (B ⧸ N))
        exact ih (Module.finrank (ZMod p) V') (by simpa only [hdim] using hdrop)
          S.X₃ V' hV' hspanV' rfl

/-- The original short-exact induction follows from the stronger induction
whose actual left-hand subobjects are finite trivial representations. -/
theorem induction_of_finite_stable_span (hG : IsPGroup p G)
    (P : Rep.{v} R G → Prop)
    (htrivial : ∀ A : Rep.{v} R G, ∀ [Module.Finite R A],
      (∀ x : A, p • x = 0) → A.IsTrivial → P A)
    (hext : ∀ S : ShortComplex (Rep.{v} R G),
      S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    (A : Rep.{v} R G) [Module.Finite R A]
    [Module (ZMod p) A]
    (W : Submodule (ZMod p) A) [Module.Finite (ZMod p) W]
    (hstable : ∀ g x, x ∈ W → A.ρ g x ∈ W)
    (hspan : Submodule.span R (W : Set A) = ⊤) : P A := by
  apply induction_of_finite_stable_span_trivial_subobject p hG P htrivial ?_
    A W hstable hspan
  intro S hS hfinite hp htrivialS hQ
  let := hfinite
  exact hext S hS (htrivial S.X₁ hp htrivialS) hQ

variable [Finite G]

/-- Induction for finite prime-killed modules with p-group action requiring
only extension steps with an actual finite trivial left-hand subobject.
This permits geometric realization by invariant sections and actual cokernels,
without effective descent for arbitrary subrepresentations. -/
theorem induction_finite_of_prime_nsmul_trivial_subobject (hG : IsPGroup p G)
    (P : Rep.{v} R G → Prop)
    (htrivial : ∀ A : Rep.{v} R G, ∀ [Module.Finite R A],
      (∀ x : A, p • x = 0) → A.IsTrivial → P A)
    (hstep : ∀ S : ShortComplex (Rep.{v} R G),
      S.ShortExact → Module.Finite R S.X₁ → (∀ x : S.X₁, p • x = 0) →
        S.X₁.IsTrivial → P S.X₃ → P S.X₂)
    (A : Rep.{v} R G) [Module.Finite R A] (hA : ∀ x : A, p • x = 0) : P A := by
  let aModule := AddCommGroup.zmodModule (n := p) hA
  obtain ⟨W, hW, hstable, hspan⟩ :=
    Representation.exists_finiteDimensional_stable_span_zmod (R := R) (M := A) p A.ρ
  let : Module.Finite (ZMod p) W := hW
  exact induction_of_finite_stable_span_trivial_subobject p hG P htrivial hstep
    A W hstable hspan

/-- A finite p-group representation on a finitely generated original
`R`-module killed by `p` satisfies every property closed under short exact
extensions and holding for finite trivial representations killed by `p`.

The original ring need not have characteristic `p` and need not be
Noetherian. Scalar and module universes remain independent. -/
theorem induction_finite_of_prime_nsmul (hG : IsPGroup p G)
    (P : Rep.{v} R G → Prop)
    (htrivial : ∀ A : Rep.{v} R G, ∀ [Module.Finite R A],
      (∀ x : A, p • x = 0) → A.IsTrivial → P A)
    (hext : ∀ S : ShortComplex (Rep.{v} R G),
      S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    (A : Rep.{v} R G) [Module.Finite R A] (hA : ∀ x : A, p • x = 0) : P A := by
  let aModule := AddCommGroup.zmodModule (n := p) hA
  obtain ⟨W, hW, hstable, hspan⟩ :=
    Representation.exists_finiteDimensional_stable_span_zmod (R := R) (M := A) p A.ρ
  let : Module.Finite (ZMod p) W := hW
  exact induction_of_finite_stable_span p hG P htrivial hext A W hstable hspan

end PrimeKilled

section PrimeFieldAlgebra

variable (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [Algebra (ZMod p) R]
  {G : Type g} [Group G] [Finite G]

/-- Specialization to a prime-field coefficient algebra. Finite generation
is over `R`, not over the prime field. -/
theorem induction_finite_of_isPGroup (hG : IsPGroup p G)
    (P : Rep.{v} R G → Prop)
    (htrivial : ∀ A : Rep.{v} R G, ∀ [Module.Finite R A], A.IsTrivial → P A)
    (hext : ∀ S : ShortComplex (Rep.{v} R G),
      S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    (A : Rep.{v} R G) [Module.Finite R A] : P A := by
  let : Module (ZMod p) A := Module.compHom A (algebraMap (ZMod p) R)
  exact induction_finite_of_prime_nsmul p hG P (fun B _ _ => htrivial B) hext A
    (ZModModule.char_nsmul_eq_zero p)

end PrimeFieldAlgebra

end Rep
