/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.IntegralClosure.FiniteEtale

/-!
# Maps and actions on the literal normalization

Foundational slice toward `K2-018#prop:k2018-arithmetic-characters`, mathematical
snapshot `e73d98b1b5c1e5abcdebf7d058e436d792b87982`: restriction of generic
algebra maps and actions to the same normalization, with its canonical generic
fibre. The generic algebra is a commutative ring; it need not be a field.
The fraction-field and integrality hypotheses enter only the inverse and the
generic-fibre compatibility. No scheme torsor, nonsplit coefficient group scheme,
finite-etale torsor condition, or global gluing assertion is encoded here.
-/

/-!
Extraction source: `R5Lab.Aglib.RingTheory.IntegralClosure.FiniteEtale.Actions`,
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`015cc116bc69c3d354170faa84ab0d3e017c35c933bd51507d55fb9771b73fe7`.
Historical source locators retain their original basis. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped TensorProduct

namespace integralClosure

section Restriction

variable (R K : Type*) [CommRing R] [CommRing K] [Algebra R K]
variable {A B C : Type*}
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [CommRing B] [Algebra K B] [Algebra R B] [IsScalarTower R K B]
  [CommRing C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]

/-- `K2-018#prop:k2018-arithmetic-characters`, snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, foundational algebra slice:
restrict an actual generic algebra map to its literal integral closures.
This requires compatible scalar towers, but no field or finiteness hypothesis. -/
def restrictHom (f : A →ₐ[K] B) : integralClosure R A →ₐ[R] integralClosure R B :=
  (f.restrictScalars R).mapIntegralClosure

@[simp] theorem coe_restrictHom (f : A →ₐ[K] B) (b : integralClosure R A) :
    (restrictHom R K f b : B) = f (b : A) := rfl

@[simp] theorem restrictHom_id :
    restrictHom R K (AlgHom.id K A) = AlgHom.id R (integralClosure R A) := by
  ext b
  rfl

@[simp] theorem restrictHom_comp (g : B →ₐ[K] C) (f : A →ₐ[K] B) :
    restrictHom R K (g.comp f) = (restrictHom R K g).comp (restrictHom R K f) := by
  ext b
  rfl

/-- The isomorphism version of `restrictHom` on the same literal model;
source correspondence is the foundational slice described in `restrictHom`. -/
def restrictEquiv (e : A ≃ₐ[K] B) : integralClosure R A ≃ₐ[R] integralClosure R B :=
  (e.restrictScalars R).mapIntegralClosure

@[simp] theorem coe_restrictEquiv (e : A ≃ₐ[K] B) (b : integralClosure R A) :
    (restrictEquiv R K e b : B) = e (b : A) := rfl

@[simp] theorem restrictEquiv_toAlgHom (e : A ≃ₐ[K] B) :
    (restrictEquiv R K e).toAlgHom = restrictHom R K e.toAlgHom := rfl

@[simp] theorem restrictEquiv_refl :
    restrictEquiv R K (AlgEquiv.refl : A ≃ₐ[K] A) = AlgEquiv.refl := by
  ext b
  rfl

@[simp] theorem restrictEquiv_trans (e : A ≃ₐ[K] B) (f : B ≃ₐ[K] C) :
    restrictEquiv R K (e.trans f) = (restrictEquiv R K e).trans (restrictEquiv R K f) := by
  ext b
  rfl

@[simp] theorem restrictEquiv_symm (e : A ≃ₐ[K] B) :
    restrictEquiv R K e.symm = (restrictEquiv R K e).symm := by
  ext b
  rfl

/-- Restriction is a homomorphism of automorphism groups. The multiplication
convention is composition, with `(e * f) b = e (f b)`. This is the action
extension input for the foundational slice of `K2-018#prop:k2018-arithmetic-characters`
at snapshot `e73d98b1b5c1e5abcdebf7d058e436d792b87982`. -/
def restrictAut : (A ≃ₐ[K] A) →* (integralClosure R A ≃ₐ[R] integralClosure R A) where
  toFun := restrictEquiv R K
  map_one' := restrictEquiv_refl R K
  map_mul' e f := by
    ext b
    rfl

@[simp] theorem restrictAut_apply (e : A ≃ₐ[K] A) :
    restrictAut R K e = restrictEquiv R K e := rfl

end Restriction

section GenericFiber

variable (R K : Type*) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
variable {A B C : Type*}
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [CommRing B] [Algebra K B] [Algebra R B] [IsScalarTower R K B]
  [CommRing C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]

/-- On the actual canonical generic fibres, restriction recovers the given map.
This is the commuting square in the foundational algebra slice of
`K2-018#prop:k2018-arithmetic-characters`, snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`. Only integrality of the two generic
algebras over the fraction field is required in addition to the scalar towers. -/
theorem genericFiberEquiv_naturality [Algebra.IsIntegral K A] [Algebra.IsIntegral K B]
    (f : A →ₐ[K] B) :
    (genericFiberEquiv R K B).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id K K) (restrictHom R K f)) =
      f.comp (genericFiberEquiv R K A).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro k b
  simp [genericFiberEquiv_tmul]

/-- Two generic algebra maps agreeing on the actual normalization agree
everywhere. Only the source generic algebra must be integral over `K`.
This supplies uniqueness for the same-model slice of
`K2-018#prop:k2018-arithmetic-characters`, snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`. -/
theorem hom_ext_of_model [Algebra.IsIntegral K A] {f g : A →ₐ[K] B}
    (h : ∀ b : integralClosure R A, f (b : A) = g (b : A)) : f = g := by
  have ht : f.comp (genericFiberEquiv R K A).toAlgHom =
      g.comp (genericFiberEquiv R K A).toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro k b
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, genericFiberEquiv_tmul,
      map_mul, AlgHom.commutes, h b]
  apply AlgHom.ext
  intro a
  obtain ⟨t, rfl⟩ := (genericFiberEquiv R K A).surjective a
  exact DFunLike.congr_fun ht t

/-- Extend an `R`-algebra map between the literal normalizations by tensoring
with the fraction field and using the fixed canonical generic-fibre maps.
This is the inverse construction for the foundational algebra slice of
`K2-018#prop:k2018-arithmetic-characters`, snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`; both generic algebras are assumed
integral over `K`, and no target-specific torsor premise is assumed. -/
def liftHom [Algebra.IsIntegral K A] [Algebra.IsIntegral K B]
    (f : integralClosure R A →ₐ[R] integralClosure R B) : A →ₐ[K] B :=
  (genericFiberEquiv R K B).toAlgHom.comp
    ((Algebra.TensorProduct.map (AlgHom.id K K) f).comp
      (genericFiberEquiv R K A).symm.toAlgHom)

@[simp] theorem liftHom_coe [Algebra.IsIntegral K A] [Algebra.IsIntegral K B]
    (f : integralClosure R A →ₐ[R] integralClosure R B) (b : integralClosure R A) :
    liftHom R K f (b : A) = (f b : B) := by
  have hb : (genericFiberEquiv R K A).symm (b : A) = (1 : K) ⊗ₜ[R] b := by
    apply (genericFiberEquiv R K A).injective
    simp [genericFiberEquiv_tmul]
  simp [liftHom, hb, genericFiberEquiv_tmul]

@[simp] theorem restrictHom_liftHom [Algebra.IsIntegral K A] [Algebra.IsIntegral K B]
    (f : integralClosure R A →ₐ[R] integralClosure R B) : restrictHom R K (liftHom R K f) = f := by
  ext b
  exact liftHom_coe R K f b

@[simp] theorem liftHom_restrictHom [Algebra.IsIntegral K A] [Algebra.IsIntegral K B]
    (f : A →ₐ[K] B) : liftHom R K (restrictHom R K f) = f := by
  apply hom_ext_of_model R K
  intro b
  simp

/-- Generic algebra maps and normalization maps are in bijection, on the same
algebras and canonical fibres. This is a Hom-set strengthening of the assigned
same-model action prerequisite for `K2-018#prop:k2018-arithmetic-characters`,
snapshot `e73d98b1b5c1e5abcdebf7d058e436d792b87982`, under the explicit
fraction-field and integrality hypotheses of `liftHom`. -/
def homEquiv [Algebra.IsIntegral K A] [Algebra.IsIntegral K B] :
    (A →ₐ[K] B) ≃ (integralClosure R A →ₐ[R] integralClosure R B) where
  toFun := restrictHom R K
  invFun := liftHom R K
  left_inv := liftHom_restrictHom R K
  right_inv := restrictHom_liftHom R K

@[simp] theorem liftHom_id [Algebra.IsIntegral K A] :
    liftHom R K (AlgHom.id R (integralClosure R A)) = AlgHom.id K A := by
  apply hom_ext_of_model R K
  intro b
  simp

@[simp] theorem liftHom_comp [Algebra.IsIntegral K A] [Algebra.IsIntegral K B]
    [Algebra.IsIntegral K C] (g : integralClosure R B →ₐ[R] integralClosure R C)
    (f : integralClosure R A →ₐ[R] integralClosure R B) :
    liftHom R K (g.comp f) = (liftHom R K g).comp (liftHom R K f) := by
  apply hom_ext_of_model R K
  intro b
  simp

/-- Lift a normalization isomorphism on the same generic algebras.
Source correspondence and hypotheses are those of `homEquiv`. -/
def liftEquiv [Algebra.IsIntegral K A] [Algebra.IsIntegral K B]
    (e : integralClosure R A ≃ₐ[R] integralClosure R B) : A ≃ₐ[K] B :=
  AlgEquiv.ofAlgHom (liftHom R K e.toAlgHom) (liftHom R K e.symm.toAlgHom)
    (by rw [← liftHom_comp]; simp)
    (by rw [← liftHom_comp]; simp)

@[simp] theorem liftEquiv_coe [Algebra.IsIntegral K A] [Algebra.IsIntegral K B]
    (e : integralClosure R A ≃ₐ[R] integralClosure R B) (b : integralClosure R A) :
    liftEquiv R K e (b : A) = (e b : B) :=
  liftHom_coe R K e.toAlgHom b

@[simp] theorem restrictEquiv_liftEquiv [Algebra.IsIntegral K A] [Algebra.IsIntegral K B]
    (e : integralClosure R A ≃ₐ[R] integralClosure R B) :
    restrictEquiv R K (liftEquiv R K e) = e := by
  ext b
  exact liftEquiv_coe R K e b

@[simp] theorem liftEquiv_restrictEquiv [Algebra.IsIntegral K A] [Algebra.IsIntegral K B]
    (e : A ≃ₐ[K] B) : liftEquiv R K (restrictEquiv R K e) = e := by
  apply AlgEquiv.coe_toAlgHom_injective
  exact liftHom_restrictHom R K e.toAlgHom

/-- The automorphism groups of the actual generic algebra and its literal
normalization are canonically isomorphic. This closes the bounded algebraic
action-extension prerequisite toward `K2-018#prop:k2018-arithmetic-characters`,
snapshot `e73d98b1b5c1e5abcdebf7d058e436d792b87982`, under fraction-field,
compatible-tower and generic-integrality hypotheses. It makes no full torsor
or arithmetic-image assertion. -/
def autEquiv [Algebra.IsIntegral K A] :
    (A ≃ₐ[K] A) ≃* (integralClosure R A ≃ₐ[R] integralClosure R A) where
  toFun := restrictEquiv R K
  invFun := liftEquiv R K
  left_inv := liftEquiv_restrictEquiv R K
  right_inv := restrictEquiv_liftEquiv R K
  map_mul' e f := (restrictAut R K).map_mul e f

end GenericFiber

section Actions

variable (R K A G : Type*) [CommRing R] [CommRing K] [Algebra R K]
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A] [Monoid G]

/-- Extend a given action by generic algebra automorphisms to the same
normalization. This is the constant-group algebra action slice of
`K2-018#prop:k2018-arithmetic-characters`, snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`. The input is an actual monoid
homomorphism to `Aut_K(A)`; no normalization action is assumed. -/
def extendAction (ρ : G →* (A ≃ₐ[K] A)) :
    G →* (integralClosure R A ≃ₐ[R] integralClosure R A) :=
  (restrictAut R K).comp ρ

@[simp] theorem extendAction_coe (ρ : G →* (A ≃ₐ[K] A)) (g : G) (b : integralClosure R A) :
    (extendAction R K A G ρ g b : A) = ρ g (b : A) := rfl

/-- The extension on the literal subring is unique once its inclusion into the
actual generic algebra is equivariant. No fraction-field hypothesis is needed
for this uniqueness assertion. Source correspondence is the bounded algebra
action slice of `K2-018#prop:k2018-arithmetic-characters`, snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`. -/
theorem extendAction_unique (ρ : G →* (A ≃ₐ[K] A))
    (α : G →* (integralClosure R A ≃ₐ[R] integralClosure R A))
    (h : ∀ g (b : integralClosure R A), (α g b : A) = ρ g (b : A)) :
    α = extendAction R K A G ρ := by
  ext g b
  exact h g b

/-- The `MulSemiringAction` attached to `extendAction`, with no global instance
choice imposed. Source correspondence is the algebra action slice above. -/
abbrev modelAction (ρ : G →* (A ≃ₐ[K] A)) : MulSemiringAction G (integralClosure R A) :=
  MulSemiringAction.compHom (integralClosure R A) (extendAction R K A G ρ)

@[simp] theorem modelAction_smul_coe (ρ : G →* (A ≃ₐ[K] A)) (g : G) (b : integralClosure R A) :
    letI := modelAction R K A G ρ
    (g • b : integralClosure R A).val = ρ g (b : A) := rfl

/-- The extended action fixes the base scalars. This produces the algebra-action
compatibility needed to use `MulSemiringAction.toAlgAut` on the model. -/
abbrev modelActionSMulCommClass (ρ : G →* (A ≃ₐ[K] A)) :
    letI := modelAction R K A G ρ
    SMulCommClass G R (integralClosure R A) := by
  letI := modelAction R K A G ρ
  exact ⟨fun g r b => (extendAction R K A G ρ g).toLinearEquiv.map_smul r b⟩

end Actions

section ActionEquivalence

variable (R K A G : Type*) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [Algebra.IsIntegral K A] [Monoid G]

/-- All actions by algebra automorphisms on the generic algebra and on its
literal model correspond uniquely. This strengthens the assigned algebra
prerequisite for `K2-018#prop:k2018-arithmetic-characters`, snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, under the explicit fraction-field
and integrality hypotheses. This equivalence does not assert a scheme torsor
condition or cover a nonsplit group-scheme coaction. -/
def actionEquiv :
    (G →* (A ≃ₐ[K] A)) ≃ (G →* (integralClosure R A ≃ₐ[R] integralClosure R A)) where
  toFun := extendAction R K A G
  invFun α := (autEquiv R K).symm.toMonoidHom.comp α
  left_inv ρ := by
    apply MonoidHom.ext
    intro g
    exact (autEquiv R K).left_inv (ρ g)
  right_inv α := by
    apply MonoidHom.ext
    intro g
    exact (autEquiv R K).right_inv (α g)

/-- The fixed canonical generic-fibre square is equivariant for the extended
action; this conclusion is derived from restriction, rather than assumed. -/
theorem genericFiberEquiv_extendAction (ρ : G →* (A ≃ₐ[K] A)) (g : G) :
    (genericFiberEquiv R K A).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id K K)
          (extendAction R K A G ρ g).toAlgHom) =
      (ρ g).toAlgHom.comp (genericFiberEquiv R K A).toAlgHom :=
  genericFiberEquiv_naturality R K (ρ g).toAlgHom

end ActionEquivalence

end integralClosure
