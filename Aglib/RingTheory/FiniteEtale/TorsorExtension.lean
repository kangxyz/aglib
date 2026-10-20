/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.FiniteEtale.GenericMaps
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Original generic coaction laws and faithfully flat torsor models

Supporting local constructions for
`K2-018#prop:k2018-arithmetic-characters`
(`research/exposes/K2/018/expose.tex`), source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
The intended source model is `X_ell = \mathcal E[1/\ell]`.

Encoded subset C1: over a normal Noetherian domain R with fraction field K,
a supplied generic-fibre equivalence and nontrivial original-A torsor datum
over the actual H_K extend to a supplied finite etale model B and coefficient
algebra H. Ordinary coaction laws, faithful flatness and the integral
transporter are derived, preserving the original generic square. The literal
normalization specialization still assumes A integral over K and the finite
etale normalization instances. Supporting tensor identities use their own
stated, weaker hypotheses.

The coefficient epsilon/Delta are the supplied genuine-group maps; this file
does not reconstruct their Hopf axioms or a categorical group object. A and H
may be product algebras. No K-rational point or E-owned model is constructed.
H1 construction, the H1-to-fixed-point implication, coefficient inertia,
vertical arguments and global gluing are outside this local conditional slice.
-/

/-!
Extraction source: `R5Lab.Aglib.RingTheory.IntegralClosure.FiniteEtale.TorsorExtension`,
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`d9db138f37ffb065cef7bc72321dd8f05e12a3715dd0c21b60e7e7b7e59ee3ea`.
Historical source locators retain their original basis. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped TensorProduct
open Algebra.TensorProduct

namespace Algebra.FiniteEtale.TorsorExtension

open Algebra.FiniteEtale.GenericMaps

universe u

/-- Finite and flat algebras with nontrivial generic fibre are faithfully
flat over a domain. The proof uses torsion freeness, injectivity, and GENERAL
integral lying-over; it makes no domain/field assumption on B.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded subset C1: the finite-flat faithful-flatness prerequisite over a domain, from
nontrivial K tensor B. -/
theorem faithfullyFlat_of_nontrivial_tensor
    (R K B : Type u) [CommRing R] [IsDomain R] [CommRing K] [Algebra R K]
    [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Flat R B]
    [Nontrivial (K ⊗[R] B)] : Module.FaithfullyFlat R B := by
  letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := K) (B := B)
  haveI : Nontrivial B := (algebraMap B (K ⊗[R] B)).domain_nontrivial
  haveI : Module.IsTorsionFree R B := inferInstance
  haveI : FaithfulSMul R B := inferInstance
  exact Module.FaithfullyFlat.of_comap_surjective (Algebra.IsIntegral.comap_surjective R B)

section Comparison

variable (R K : Type u) [CommRing R] [Field K] [Algebra R K]
variable {B A H : Type u} [CommRing B] [Algebra R B]
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [CommRing H] [Algebra R H]

/-- Original generic coaction data, with ordinary laws on A itself.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded subset C1: ordinary original-A coaction laws over the actual H_K, using the
supplied coefficient maps. -/
abbrev OriginalCoaction (ε : H →ₐ[R] R) (Δ : H →ₐ[R] H ⊗[R] H) :=
  AlgebraCoaction K A (K ⊗[R] H) (BaseChange.counit R K ε) (BaseChange.comul R K Δ)

/-- The given generic-fibre equivalence and the actual coefficient tensor.

Supporting helper for the module's explicit C1 source mapping. -/
def fibreTensorEquiv (e : (K ⊗[R] B) ≃ₐ[K] A) :
    K ⊗[R] (B ⊗[R] H) ≃ₐ[K] A ⊗[K] (K ⊗[R] H) :=
  (BaseChange.tensorEquiv R K).symm.trans
    (Algebra.TensorProduct.congr e (AlgEquiv.refl : (K ⊗[R] H) ≃ₐ[K] (K ⊗[R] H)))

/-- The triple comparison retains the coefficient tensor's actual carrier.

Supporting helper for the module's explicit C1 source mapping. -/
def fibreTripleEquiv (e : (K ⊗[R] B) ≃ₐ[K] A) :
    K ⊗[R] (B ⊗[R] (H ⊗[R] H)) ≃ₐ[K]
      A ⊗[K] ((K ⊗[R] H) ⊗[K] (K ⊗[R] H)) :=
  (BaseChange.tensorEquiv R K).symm.trans
    (Algebra.TensorProduct.congr e (BaseChange.tensorEquiv R K).symm)

omit [Algebra R A] [IsScalarTower R K A] in
@[simp] theorem fibreTensorEquiv_tmul (e : (K ⊗[R] B) ≃ₐ[K] A)
    (k : K) (b : B) (h : H) :
    fibreTensorEquiv R K e (k ⊗ₜ[R] (b ⊗ₜ[R] h)) =
      e (k ⊗ₜ[R] b) ⊗ₜ[K] ((1 : K) ⊗ₜ[R] h) := by
  simp [fibreTensorEquiv]

omit [Algebra R A] [IsScalarTower R K A] in
@[simp] theorem fibreTripleEquiv_tmul (e : (K ⊗[R] B) ≃ₐ[K] A)
    (k : K) (b : B) (h j : H) :
    fibreTripleEquiv R K e (k ⊗ₜ[R] (b ⊗ₜ[R] (h ⊗ₜ[R] j))) =
      e (k ⊗ₜ[R] b) ⊗ₜ[K]
        (((1 : K) ⊗ₜ[R] h) ⊗ₜ[K] ((1 : K) ⊗ₜ[R] j)) := by
  simp [fibreTripleEquiv]

/-- Counit compatibility for the original generic algebra and actual models.

Supporting helper for the module's explicit C1 source mapping. -/
theorem fibre_counit (e : (K ⊗[R] B) ≃ₐ[K] A) (ε : H →ₐ[R] R) :
    e.toAlgHom.comp (BaseChange.map R K (coactionCounit R B H ε)) =
      (coactionCounit K A (K ⊗[R] H) (BaseChange.counit R K ε)).comp
        (fibreTensorEquiv R K e).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro k x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul b h =>
    simp only [BaseChange.map, coactionCounit, genericMap_comp, AlgHom.coe_comp,
      AlgEquiv.coe_toAlgHom, Function.comp_apply, map_tmul, AlgHom.coe_id, id_eq,
      rid_tmul, TensorProduct.tmul_smul, BaseChange.counit, fibreTensorEquiv_tmul]
    calc
      e ((ε h • k) ⊗ₜ[R] b) = ε h • e (k ⊗ₜ[R] b) := by
        rw [← TensorProduct.smul_tmul']
        exact (e.restrictScalars R).toLinearEquiv.map_smul (ε h) (k ⊗ₜ[R] b)
      _ = (Algebra.TensorProduct.rid K K A)
          ((ε h • e (k ⊗ₜ[R] b)) ⊗ₜ[K] (1 : K)) := by
        simp only [Algebra.TensorProduct.rid_tmul, one_smul]


omit [Algebra R A] [IsScalarTower R K A] in
/-- Comultiplication compatibility with the original generic algebra.

Supporting helper for the module's explicit C1 source mapping. -/
theorem fibre_comul (e : (K ⊗[R] B) ≃ₐ[K] A) (Δ : H →ₐ[R] H ⊗[R] H) :
    (fibreTripleEquiv R K e).toAlgHom.comp
        (BaseChange.map R K (Algebra.TensorProduct.map (AlgHom.id R B) Δ)) =
      (Algebra.TensorProduct.map (AlgHom.id K A) (BaseChange.comul R K Δ)).comp
        (fibreTensorEquiv R K e).toAlgHom := by
  have hm :
      (Algebra.TensorProduct.map e.toAlgHom
        (BaseChange.tensorEquiv R K (B := H) (H := H)).symm.toAlgHom).comp
          (Algebra.TensorProduct.map (BaseChange.map R K (AlgHom.id R B)) (BaseChange.map R K Δ)) =
        (Algebra.TensorProduct.map (AlgHom.id K A) (BaseChange.comul R K Δ)).comp
          (Algebra.TensorProduct.map e.toAlgHom (AlgHom.id K (K ⊗[R] H))) := by
    rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp]
    simp [BaseChange.comul]
  apply AlgHom.ext
  intro z
  obtain ⟨t, rfl⟩ := (BaseChange.tensorEquiv R K (B := B) (H := H)).surjective z
  have hn := DFunLike.congr_fun
    (genericTensorEquiv_naturality R K (AlgHom.id R B) Δ) t
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] at hn
  change fibreTripleEquiv R K e
      (BaseChange.map R K (Algebra.TensorProduct.map (AlgHom.id R B) Δ)
        (BaseChange.tensorEquiv R K t)) = _
  rw [← hn]
  simpa [fibreTensorEquiv, fibreTripleEquiv] using DFunLike.congr_fun hm t

/-- Coherent associativity of actual generic tensor products.

Supporting helper for the module's explicit C1 source mapping. -/
theorem fibre_assoc (e : (K ⊗[R] B) ≃ₐ[K] A) :
    ((fibreTripleEquiv R K e).toAlgHom.comp
      (BaseChange.map R K (Algebra.TensorProduct.assoc R R R B H H).toAlgHom)).comp
        (BaseChange.tensorEquiv R K (B := B ⊗[R] H) (H := H)).toAlgHom =
      (Algebra.TensorProduct.assoc K K K A (K ⊗[R] H) (K ⊗[R] H)).toAlgHom.comp
        (Algebra.TensorProduct.map (fibreTensorEquiv R K e).toAlgHom
          (AlgHom.id K (K ⊗[R] H))) := by
  ext b <;> simp [BaseChange.map, fibreTensorEquiv, fibreTripleEquiv,
    Algebra.TensorProduct.one_def]

/-- Conjugate an actual map on A to the canonical generic fibre of B.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded subset C1: conjugation by the supplied generic-fibre equivalence, without a
generic-square premise. -/
def fibreCoact (e : (K ⊗[R] B) ≃ₐ[K] A)
    (δ : A →ₐ[K] A ⊗[K] (K ⊗[R] H)) :
    (K ⊗[R] B) →ₐ[K] K ⊗[R] (B ⊗[R] H) :=
  (fibreTensorEquiv R K (H := H) e).symm.toAlgHom.comp (δ.comp e.toAlgHom)

/-- The generic square is proved by the construction, never assumed.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded subset C1: the square for the original-A map and the supplied generic-fibre
equivalence. -/
theorem fibreCoact_square (e : (K ⊗[R] B) ≃ₐ[K] A)
    (δ : A →ₐ[K] A ⊗[K] (K ⊗[R] H)) :
    (fibreTensorEquiv R K e).toAlgHom.comp (fibreCoact R K e δ) = δ.comp e.toAlgHom := by
  ext x
  simp [fibreCoact]

/-- Triple compatibility for any intertwining generic algebra map. The
intertwining relation used below is the conclusion of `fibreCoact_square`.

Supporting helper for the module's explicit C1 source mapping. -/
theorem fibre_coassoc_right (e : (K ⊗[R] B) ≃ₐ[K] A)
    (f : (K ⊗[R] B) →ₐ[K] K ⊗[R] (B ⊗[R] H))
    (δ : A →ₐ[K] A ⊗[K] (K ⊗[R] H))
    (hf : (fibreTensorEquiv R K e).toAlgHom.comp f = δ.comp e.toAlgHom) :
    ((fibreTripleEquiv R K e).toAlgHom.comp
      (BaseChange.map R K (Algebra.TensorProduct.assoc R R R B H H).toAlgHom)).comp
        (genericTensorMap R K f (AlgHom.id K (K ⊗[R] H))) =
      (Algebra.TensorProduct.assoc K K K A (K ⊗[R] H) (K ⊗[R] H)).toAlgHom.comp
        ((Algebra.TensorProduct.map δ (AlgHom.id K (K ⊗[R] H))).comp
          (fibreTensorEquiv R K e).toAlgHom) := by
  have hm :
      (Algebra.TensorProduct.map (fibreTensorEquiv R K e).toAlgHom
        (AlgHom.id K (K ⊗[R] H))).comp
          (Algebra.TensorProduct.map f (AlgHom.id K (K ⊗[R] H))) =
        (Algebra.TensorProduct.map δ (AlgHom.id K (K ⊗[R] H))).comp
          (Algebra.TensorProduct.map e.toAlgHom (AlgHom.id K (K ⊗[R] H))) := by
    rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp]
    simp only [AlgHom.id_comp, hf]
  apply AlgHom.ext
  intro z
  let t := Algebra.TensorProduct.map f (AlgHom.id K (K ⊗[R] H))
    ((BaseChange.tensorEquiv R K (B := B) (H := H)).symm z)
  have ha := DFunLike.congr_fun (fibre_assoc R K (H := H) e) t
  have hmt := DFunLike.congr_fun hm ((BaseChange.tensorEquiv R K (B := B) (H := H)).symm z)
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] at ha hmt
  change fibreTripleEquiv R K e
      (BaseChange.map R K (Algebra.TensorProduct.assoc R R R B H H).toAlgHom
        (BaseChange.tensorEquiv R K t)) = _
  rw [ha, hmt]
  simp [fibreTensorEquiv]

/-- Compare the actual product generic fibre with A tensor A.

Supporting helper for the module's explicit C1 source mapping. -/
def fibreProductEquiv (e : (K ⊗[R] B) ≃ₐ[K] A) :
    K ⊗[R] (B ⊗[R] B) ≃ₐ[K] A ⊗[K] A :=
  (BaseChange.tensorEquiv R K (B := B) (H := B)).symm.trans
    (Algebra.TensorProduct.congr e e)

/-- Exact transporter compatibility with the original generic map on A.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded subset C1: compatibility of the actual canonical-fibre and original-A
transporters. -/
theorem fibre_transporter (e : (K ⊗[R] B) ≃ₐ[K] A)
    (δ : A →ₐ[K] A ⊗[K] (K ⊗[R] H)) :
    (fibreTensorEquiv R K e).toAlgHom.comp
        (genericTransporter R K B H (fibreCoact R K e δ)) =
      (transporter K A (K ⊗[R] H) δ).comp (fibreProductEquiv R K e).toAlgHom := by
  have hm (x : A ⊗[K] (K ⊗[R] H)) :
      Algebra.TensorProduct.map e.toAlgHom (AlgHom.id K (K ⊗[R] H))
        (Algebra.TensorProduct.map e.symm.toAlgHom (AlgHom.id K (K ⊗[R] H)) x) = x := by
    change ((Algebra.TensorProduct.map e.toAlgHom (AlgHom.id K (K ⊗[R] H))).comp
      (Algebra.TensorProduct.map e.symm.toAlgHom (AlgHom.id K (K ⊗[R] H)))) x = x
    rw [← Algebra.TensorProduct.map_comp]
    simp
  have ht :
      ((fibreTensorEquiv R K e).toAlgHom.comp
        (genericTransporter R K B H (fibreCoact R K e δ))).comp
          (BaseChange.tensorEquiv R K (B := B) (H := B)).toAlgHom =
        ((transporter K A (K ⊗[R] H) δ).comp (fibreProductEquiv R K e).toAlgHom).comp
          (BaseChange.tensorEquiv R K (B := B) (H := B)).toAlgHom := by
    ext b <;> simp [genericTransporter, transporter, fibreProductEquiv,
      fibreTensorEquiv, fibreCoact, BaseChange.map, Algebra.TensorProduct.one_def] <;>
      simp only [hm]
  apply AlgHom.ext
  intro z
  obtain ⟨t, rfl⟩ := (BaseChange.tensorEquiv R K (B := B) (H := B)).surjective z
  exact DFunLike.congr_fun ht t

/-- A generic transporter isomorphism on the ORIGINAL A yields the actual
canonical-fibre transporter isomorphism, without a rational point.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded subset C1: bijectivity transported from the original-A transporter through the
supplied equivalence. -/
theorem genericTransporter_bijective_original (e : (K ⊗[R] B) ≃ₐ[K] A)
    (δ : A →ₐ[K] A ⊗[K] (K ⊗[R] H))
    (hδ : Function.Bijective (transporter K A (K ⊗[R] H) δ)) :
    Function.Bijective (genericTransporter R K B H (fibreCoact R K e δ)) := by
  have hc : Function.Bijective ((fibreTensorEquiv R K e).toAlgHom.comp
      (genericTransporter R K B H (fibreCoact R K e δ))) := by
    rw [fibre_transporter]
    exact hδ.comp (fibreProductEquiv R K e).bijective
  constructor
  · intro x y hxy
    apply hc.injective
    exact congrArg (fibreTensorEquiv R K e) hxy
  · intro z
    obtain ⟨x, hx⟩ := hc.surjective (fibreTensorEquiv R K e z)
    exact ⟨x, (fibreTensorEquiv R K e).injective hx⟩

end Comparison

section OriginalLaws

variable (R K : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]
variable {B A H : Type u} [CommRing B] [Algebra R B]
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [CommRing H] [Algebra R H]
variable {ε : H →ₐ[R] R} {Δ : H →ₐ[R] H ⊗[R] H}

/-- Transport ORDINARY laws on the original A into canonical generic-fibre
coaction data. This closes the law-data boundary left by the frozen Coactions
module; no model action or generic square is an input.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded subset C1: ordinary original-A laws transported to the canonical generic fibre. -/
def transportOriginalCoaction (e : (K ⊗[R] B) ≃ₐ[K] A)
    (α : OriginalCoaction R K (A := A) ε Δ) : GenericCoaction R K B H ε Δ where
  coact := fibreCoact R K e α.coact
  counit := by
    apply AlgHom.ext
    intro x
    apply e.injective
    have hc := DFunLike.congr_fun (fibre_counit R K e ε) (fibreCoact R K e α.coact x)
    have hs := DFunLike.congr_fun (fibreCoact_square R K e α.coact) x
    have ht := DFunLike.congr_fun α.counit (e x)
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.id_apply] at hc hs ht ⊢
    rw [hc, hs]
    exact ht
  coassoc := by
    apply AlgHom.ext
    intro x
    apply (fibreTripleEquiv R K e).injective
    have hl := DFunLike.congr_fun (fibre_comul R K e Δ) (fibreCoact R K e α.coact x)
    have hr := DFunLike.congr_fun
      (fibre_coassoc_right R K e (fibreCoact R K e α.coact) α.coact
        (fibreCoact_square R K e α.coact)) (fibreCoact R K e α.coact x)
    have hs := DFunLike.congr_fun (fibreCoact_square R K e α.coact) x
    have ht := DFunLike.congr_fun α.coassoc (e x)
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] at hl hr hs ht ⊢
    rw [hl, hr, hs]
    exact ht

end OriginalLaws

/-- Genuine generic torsor DATA on A itself. Nontriviality is nonemptiness
of the affine generic torsor; no A -> K point or section occurs in this input.
The coefficient maps come from the supplied actual coefficient group/Hopf
algebra. Its independent group axioms are not reconstructed in this record.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded subset C1: supplied coaction laws, Nontrivial A and bijective original-A
transporter; this record does not construct H1. -/
structure OriginalTorsorData
    (R K A H : Type u) [CommRing R] [Field K] [Algebra R K]
    [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    [CommRing H] [Algebra R H] (ε : H →ₐ[R] R) (Δ : H →ₐ[R] H ⊗[R] H) where
  /-- The supplied coaction on the original generic algebra, including its counit and
  coassociativity laws. -/
  coaction : OriginalCoaction R K (A := A) ε Δ
  nontrivial : Nontrivial A
  transporter_bijective : Function.Bijective
    (transporter K A (K ⊗[R] H) coaction.coact)

/-- Standard affine algebraic torsor criterion over the supplied coefficient
group: coaction laws, faithful flatness and transporter isomorphism.
All three are OUTPUTS of `extendOriginalTorsor`; no final torsor property or
faithful-flatness condition on the model is supplied to that construction.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded subset C1: the conditional algebraic torsor criterion over the supplied
coefficient group, without group reconstruction. -/
structure AlgebraicTorsorData
    (R B H : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [CommRing H] [Algebra R H] (ε : H →ₐ[R] R) (Δ : H →ₐ[R] H ⊗[R] H) where
  /-- The coaction on the model algebra, including its counit and coassociativity laws. -/
  coaction : AlgebraCoaction R B H ε Δ
  faithfullyFlat : Module.FaithfullyFlat R B
  transporter_bijective : Function.Bijective (transporter R B H coaction.coact)

section Torsors

variable (R K : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]
variable {B A H : Type u} [CommRing B] [Algebra R B]
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [CommRing H] [Algebra R H]
  [Module.Finite R B] [Algebra.Etale R B]
  [Module.Finite R H] [Algebra.Etale R H]
variable {ε : H →ₐ[R] R} {Δ : H →ₐ[R] H ⊗[R] H}

local instance tensorEtale {C D : Type u} [CommRing C] [CommRing D]
    [Algebra R C] [Algebra R D] [Algebra.Etale R C] [Algebra.Etale R D] :
    Algebra.Etale R (C ⊗[R] D) := Algebra.Etale.comp R C _

/-- The original, nontrivial generic torsor extends to an algebraic torsor
on the SAME actual finite etale model and coefficient algebra. Faithful
flatness and the actual transporter isomorphism are derived conclusions.
No rational point or E-model
construction is used, and B/H may be product algebras.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded subset C1: extension on supplied finite etale B/H over a normal Noetherian domain
R with fraction field K. -/
def extendOriginalTorsor (e : (K ⊗[R] B) ≃ₐ[K] A)
    (τ : OriginalTorsorData R K A H ε Δ) : AlgebraicTorsorData R B H ε Δ where
  coaction := extendCoaction R K B H (transportOriginalCoaction R K e τ.coaction)
  faithfullyFlat := by
    letI := τ.nontrivial
    letI : Nontrivial (K ⊗[R] B) := e.toEquiv.nontrivial
    haveI : Module.Flat R B := inferInstance
    exact faithfullyFlat_of_nontrivial_tensor R K B
  transporter_bijective := by
    apply transporter_bijective_of_generic R K B H
      (transportOriginalCoaction R K e τ.coaction)
    exact genericTransporter_bijective_original R K e τ.coaction.coact τ.transporter_bijective

/-- The extended actual torsor preserves the original generic arrow.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded subset C1: preservation of the original generic arrow under the extension
hypotheses. -/
theorem extendOriginalTorsor_square (e : (K ⊗[R] B) ≃ₐ[K] A)
    (τ : OriginalTorsorData R K A H ε Δ) :
    (fibreTensorEquiv R K e).toAlgHom.comp
        (BaseChange.map R K (extendOriginalTorsor R K e τ).coaction.coact) =
      τ.coaction.coact.comp e.toAlgHom := by
  rw [show BaseChange.map R K (extendOriginalTorsor R K e τ).coaction.coact =
      fibreCoact R K e τ.coaction.coact from extendCoaction_generic R K B H _]
  exact fibreCoact_square R K e τ.coaction.coact

end Torsors

section LiteralNormalization

open integralClosure

variable (R K A H : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [Algebra.IsIntegral K A] [CommRing H] [Algebra R H]
  [Module.Finite R (integralClosure R A)] [Algebra.Etale R (integralClosure R A)]
  [Module.Finite R H] [Algebra.Etale R H]
variable {ε : H →ₐ[R] R} {Δ : H →ₐ[R] H ⊗[R] H}

/-- Literal-normalization specialization with the FIXED canonical generic
fibre of the ORIGINAL A; no other generic algebra or model is substituted.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded subset C1: literal normalization with A integral over K and finite etale
normalization/H instances still supplied. -/
def normalizationTorsor (τ : OriginalTorsorData R K A H ε Δ) :
    AlgebraicTorsorData R (integralClosure R A) H ε Δ :=
  extendOriginalTorsor R K (genericFiberEquiv R K A) τ

@[simp] theorem normalizationTorsor_coact (τ : OriginalTorsorData R K A H ε Δ) :
    (normalizationTorsor R K A H τ).coaction.coact =
      liftActualCoactionHom R K A H τ.coaction.coact := rfl

/-- Exact canonical original-A square for the fully derived torsor data.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded subset C1: the canonical original-A square under the same literal-normalization
hypotheses. -/
theorem normalizationTorsor_square (τ : OriginalTorsorData R K A H ε Δ) :
    (actualTensorEquiv R K A H).toAlgHom.comp
        (BaseChange.map R K (normalizationTorsor R K A H τ).coaction.coact) =
      τ.coaction.coact.comp (genericFiberEquiv R K A).toAlgHom := by
  rw [normalizationTorsor_coact]
  exact liftActualCoactionHom_square R K A H τ.coaction.coact

end LiteralNormalization

end Algebra.FiniteEtale.TorsorExtension
