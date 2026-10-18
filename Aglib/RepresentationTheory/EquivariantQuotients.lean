/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Equivariant characters and their marked quotients

Source: `K2-018#eq:k2018-pointed-character` and
`K2-018#prop:k2018-arithmetic-characters`,
`research/exposes/K2/018/expose.tex`, lines 341–445, at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.

This file proves the additive Galois-module step: a surjective equivariant
character has a stable kernel and marks its quotient by the coefficient group.
It also proves how changing the coefficient marking changes the character.
The statements apply beyond finite cyclic modules. Their use for `E[n]` and
`Z/n(2)` still needs the continuous fundamental-group comparison, the geometric
quotient elliptic curve, dual isogenies, and Weil pairing. None is assumed as
an axiom or encoded as a field claiming the desired isogeny equivalence.
Each declaration's source pointer below uses the module source snapshot above.
-/

@[expose] public section

namespace RepresentationTheory.EquivariantQuotients

variable (G V A : Type*) [Group G] [AddCommGroup V] [AddCommGroup A]
  [DistribMulAction G V] [DistribMulAction G A]

/-- Additive equivariant character model for `K2-018#eq:k2018-pointed-character`,
on the module source basis. No geometric or finite cyclic realization is asserted. -/
structure EquivariantAddHom extends V →+ A where
  /-- Equivariance condition in `K2-018#eq:k2018-pointed-character`. -/
  map_action : ∀ g : G, ∀ v : V, toAddMonoidHom (g • v) = g • toAddMonoidHom v

/-- Equivariant additive marking model for the auxiliary marked-quotient step
of `K2-018#prop:k2018-arithmetic-characters`, on the module source basis.
An additive equivalence with this property is an equivalence of the given
group actions; no geometric quotient is asserted. -/
structure EquivariantAddEquiv extends V ≃+ A where
  /-- Equivariance of a coefficient marking in the pointed-character model. -/
  map_action : ∀ g : G, ∀ v : V, toAddEquiv (g • v) = g • toAddEquiv v

variable {G V A}

/-- Stable-kernel algebra needed for `K2-018#prop:k2018-arithmetic-characters`'s
marked-cover step, on the module source basis. This auxiliary module statement
is not literally stated in the TeX span. -/
theorem EquivariantAddHom.kernel_stable (f : EquivariantAddHom G V A)
    (g : G) (v : V) :
    v ∈ f.toAddMonoidHom.ker ↔ g • v ∈ f.toAddMonoidHom.ker := by
  simp only [AddMonoidHom.mem_ker, f.map_action]
  constructor
  · intro h
    simp [h]
  · intro h
    have hinv := congrArg (fun a : A => g⁻¹ • a) h
    simpa using hinv

/-- Actual additive quotient action for the auxiliary stable-kernel step of
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis.
The action is constructed independently of surjectivity. Consumers install
this explicitly with `letI := f.quotientAction`. -/
@[instance_reducible]
def EquivariantAddHom.quotientAction (f : EquivariantAddHom G V A) :
    DistribMulAction G (V ⧸ f.toAddMonoidHom.ker) where
  smul g := QuotientAddGroup.map f.toAddMonoidHom.ker f.toAddMonoidHom.ker
    (DistribSMul.toAddMonoidHom V g) (by
      intro v hv
      exact (f.kernel_stable g v).mp hv)
  one_smul q := by
    refine QuotientAddGroup.induction_on q fun v => ?_
    change QuotientAddGroup.mk ((1 : G) • v) = QuotientAddGroup.mk v
    rw [one_smul]
  mul_smul g h q := by
    refine QuotientAddGroup.induction_on q fun v => ?_
    change QuotientAddGroup.mk ((g * h) • v) = QuotientAddGroup.mk (g • h • v)
    rw [mul_smul]
  smul_zero g := by
    exact (QuotientAddGroup.map f.toAddMonoidHom.ker f.toAddMonoidHom.ker
      (DistribSMul.toAddMonoidHom V g) (by
        intro v hv
        exact (f.kernel_stable g v).mp hv)).map_zero
  smul_add g q r := by
    exact (QuotientAddGroup.map f.toAddMonoidHom.ker f.toAddMonoidHom.ker
      (DistribSMul.toAddMonoidHom V g) (by
        intro v hv
        exact (f.kernel_stable g v).mp hv)).map_add q r

/-- Representative formula for the actual quotient action in the auxiliary
marked-quotient step of `K2-018#prop:k2018-arithmetic-characters`, on the
module source basis. -/
@[simp]
theorem EquivariantAddHom.quotientAction_mk (f : EquivariantAddHom G V A)
    (g : G) (v : V) :
    letI := f.quotientAction
    g • (QuotientAddGroup.mk v : V ⧸ f.toAddMonoidHom.ker) =
      QuotientAddGroup.mk (g • v) := rfl

/-- Marked-quotient algebra for `K2-018#prop:k2018-arithmetic-characters`,
on the module source basis. This auxiliary first-isomorphism step does not
construct the quotient elliptic curve or an isogeny. -/
noncomputable def EquivariantAddHom.markedQuotient (f : EquivariantAddHom G V A)
    (hf : Function.Surjective f.toAddMonoidHom) :
    V ⧸ f.toAddMonoidHom.ker ≃+ A :=
  QuotientAddGroup.quotientKerEquivOfSurjective f.toAddMonoidHom hf

/-- Representative formula for the auxiliary marked-quotient step of
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
@[simp]
theorem EquivariantAddHom.markedQuotient_mk (f : EquivariantAddHom G V A)
    (hf : Function.Surjective f.toAddMonoidHom) (v : V) :
    f.markedQuotient hf (QuotientAddGroup.mk v) = f.toAddMonoidHom v := rfl

/-- Equivariance on representatives for the auxiliary marked-quotient step of
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis.
The stable-kernel theorem ensures the represented quotient action is well-defined;
`quotientAction` constructs the action on all quotient classes. -/
theorem EquivariantAddHom.markedQuotient_action (f : EquivariantAddHom G V A)
    (hf : Function.Surjective f.toAddMonoidHom) (g : G) (v : V) :
    f.markedQuotient hf (QuotientAddGroup.mk (g • v)) =
      g • f.markedQuotient hf (QuotientAddGroup.mk v) := by
  simpa using f.map_action g v

/-- Equivariance on every quotient class for the auxiliary marked-quotient
step of `K2-018#prop:k2018-arithmetic-characters`, on the module source basis.
This strengthens `markedQuotient_action` from representatives to the actual
quotient G-action. -/
theorem EquivariantAddHom.markedQuotient_equivariant
    (f : EquivariantAddHom G V A)
    (hf : Function.Surjective f.toAddMonoidHom) :
    letI := f.quotientAction
    ∀ (g : G) (q : V ⧸ f.toAddMonoidHom.ker),
      f.markedQuotient hf (g • q) = g • f.markedQuotient hf q := by
  let _ := f.quotientAction
  intro g q
  exact QuotientAddGroup.induction_on q (f.markedQuotient_action hf g)

/-- The actual marked quotient as an equivariant additive equivalence, for
the auxiliary marked-cover step of `K2-018#prop:k2018-arithmetic-characters`,
on the module source basis. This constructs a group-module quotient only;
the corresponding elliptic curve and isogeny remain external geometry. -/
noncomputable def EquivariantAddHom.markedQuotientEquiv
    (f : EquivariantAddHom G V A)
    (hf : Function.Surjective f.toAddMonoidHom) :
    letI := f.quotientAction
    EquivariantAddEquiv G (V ⧸ f.toAddMonoidHom.ker) A := by
  letI := f.quotientAction
  exact { toAddEquiv := f.markedQuotient hf
          map_action := f.markedQuotient_equivariant hf }

/-- Auxiliary marking change for `K2-018#prop:k2018-arithmetic-characters`,
on the module source basis; not literally stated in the TeX span. -/
def EquivariantAddHom.changeMarking (f : EquivariantAddHom G V A)
    (e : A ≃+ A) (he : ∀ g : G, ∀ a : A, e (g • a) = g • e a) :
    EquivariantAddHom G V A where
  toAddMonoidHom := e.toAddMonoidHom.comp f.toAddMonoidHom
  map_action g v := by
    change e (f.toAddMonoidHom (g • v)) = g • e (f.toAddMonoidHom v)
    rw [f.map_action, he]

/-- Auxiliary marking-forgetting consequence for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis;
not literally stated in the TeX span. -/
theorem EquivariantAddHom.changeMarking_kernel (f : EquivariantAddHom G V A)
    (e : A ≃+ A) (he : ∀ g : G, ∀ a : A, e (g • a) = g • e a) :
    (f.changeMarking e he).toAddMonoidHom.ker = f.toAddMonoidHom.ker := by
  ext v
  simp only [AddMonoidHom.mem_ker]
  change e (f.toAddMonoidHom v) = 0 ↔ f.toAddMonoidHom v = 0
  constructor
  · intro h
    apply e.injective
    simpa using h
  · intro h
    simp [h]

/-- Auxiliary preservation of surjectivity under marking change for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis;
not literally stated in the TeX span. -/
theorem EquivariantAddHom.changeMarking_surjective (f : EquivariantAddHom G V A)
    (hf : Function.Surjective f.toAddMonoidHom)
    (e : A ≃+ A) (he : ∀ g : G, ∀ a : A, e (g • a) = g • e a) :
    Function.Surjective (f.changeMarking e he).toAddMonoidHom := by
  intro a
  obtain ⟨v, hv⟩ := hf (e.symm a)
  refine ⟨v, ?_⟩
  change e (f.toAddMonoidHom v) = a
  rw [hv, e.apply_symm_apply]

/-- Auxiliary marking reconstruction for `K2-018#prop:k2018-arithmetic-characters`,
on the module source basis; not literally stated in the TeX span. Full-image
characters with the same kernel differ by this coefficient automorphism. -/
noncomputable def EquivariantAddHom.markingChange
    (f k : EquivariantAddHom G V A)
    (hf : Function.Surjective f.toAddMonoidHom)
    (hk : Function.Surjective k.toAddMonoidHom)
    (hker : f.toAddMonoidHom.ker = k.toAddMonoidHom.ker) : A ≃+ A :=
  (f.markedQuotient hf).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq hker).trans (k.markedQuotient hk))

/-- Auxiliary marking-reconstruction formula for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis;
not literally stated in the TeX span. -/
@[simp]
theorem EquivariantAddHom.markingChange_apply
    (f k : EquivariantAddHom G V A)
    (hf : Function.Surjective f.toAddMonoidHom)
    (hk : Function.Surjective k.toAddMonoidHom)
    (hker : f.toAddMonoidHom.ker = k.toAddMonoidHom.ker) (v : V) :
    f.markingChange k hf hk hker (f.toAddMonoidHom v) = k.toAddMonoidHom v := by
  have h : (f.markedQuotient hf).symm (f.toAddMonoidHom v) =
      QuotientAddGroup.mk v := by
    simpa using (f.markedQuotient hf).symm_apply_apply (QuotientAddGroup.mk v)
  simp only [markingChange, AddEquiv.trans_apply, h]
  simp

/-- Auxiliary equivariance of the reconstructed marking for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis;
not literally stated in the TeX span. -/
theorem EquivariantAddHom.markingChange_equivariant
    (f k : EquivariantAddHom G V A)
    (hf : Function.Surjective f.toAddMonoidHom)
    (hk : Function.Surjective k.toAddMonoidHom)
    (hker : f.toAddMonoidHom.ker = k.toAddMonoidHom.ker) (g : G) (a : A) :
    f.markingChange k hf hk hker (g • a) = g • f.markingChange k hf hk hker a := by
  obtain ⟨v, rfl⟩ := hf a
  rw [← f.map_action, f.markingChange_apply, f.markingChange_apply, k.map_action]

/-- Auxiliary uniqueness of marking reconstruction for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis;
not literally stated in the TeX span. -/
theorem EquivariantAddHom.markingChange_unique
    (f k : EquivariantAddHom G V A)
    (hf : Function.Surjective f.toAddMonoidHom)
    (hk : Function.Surjective k.toAddMonoidHom)
    (hker : f.toAddMonoidHom.ker = k.toAddMonoidHom.ker)
    (e : A ≃+ A) (he : ∀ v : V, e (f.toAddMonoidHom v) = k.toAddMonoidHom v) :
    e = f.markingChange k hf hk hker := by
  apply AddEquiv.ext
  intro a
  obtain ⟨v, rfl⟩ := hf a
  rw [he, f.markingChange_apply]

/-- Same-kernel surjections are exactly the orbits under equivariant
coefficient automorphisms, the auxiliary marking-forgetting statement for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis.
Both characters must be surjective; no finiteness of the domain is assumed. -/
theorem EquivariantAddHom.same_kernel_iff_equivariant_aut
    (f k : EquivariantAddHom G V A)
    (hf : Function.Surjective f.toAddMonoidHom)
    (hk : Function.Surjective k.toAddMonoidHom) :
    f.toAddMonoidHom.ker = k.toAddMonoidHom.ker ↔
      ∃ e : A ≃+ A,
        (∀ (g : G) (a : A), e (g • a) = g • e a) ∧
        k.toAddMonoidHom = e.toAddMonoidHom.comp f.toAddMonoidHom := by
  constructor
  · intro hker
    refine ⟨f.markingChange k hf hk hker, f.markingChange_equivariant k hf hk hker, ?_⟩
    exact AddMonoidHom.ext fun v => (f.markingChange_apply k hf hk hker v).symm
  · rintro ⟨e, he, h⟩
    rw [h]
    exact (f.changeMarking_kernel e he).symm

/-- The equivariant coefficient automorphism relating two same-kernel
surjections is unique, in the auxiliary marked-cover algebra for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
theorem EquivariantAddHom.existsUnique_equivariant_aut
    (f k : EquivariantAddHom G V A)
    (hf : Function.Surjective f.toAddMonoidHom)
    (hk : Function.Surjective k.toAddMonoidHom)
    (hker : f.toAddMonoidHom.ker = k.toAddMonoidHom.ker) :
    ∃! e : A ≃+ A,
      (∀ (g : G) (a : A), e (g • a) = g • e a) ∧
      k.toAddMonoidHom = e.toAddMonoidHom.comp f.toAddMonoidHom := by
  refine ⟨f.markingChange k hf hk hker,
    ⟨f.markingChange_equivariant k hf hk hker,
      AddMonoidHom.ext fun v => (f.markingChange_apply k hf hk hker v).symm⟩, ?_⟩
  intro e he
  apply f.markingChange_unique k hf hk hker e
  intro v
  exact (DFunLike.congr_fun he.2 v).symm

end RepresentationTheory.EquivariantQuotients

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 471306b049a5ffa0acf855a2fa7556da8803fabd40561d9a98c14d3afe935636.
Definitions, hypotheses and universes are retained modulo native names. -/
