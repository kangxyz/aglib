/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.Basic
public import Aglib.RingTheory.RootsOfUnity.FiniteCharacter
public import Aglib.AlgebraicGeometry.SchemeOverField

/-!
# Point automorphisms and cyclotomic characters of a field fibre functor

The point-automorphism maps, inverse-variance descent formula, finite cyclotomic
character, and its continuity are the original general field constructions.
Source: K2-018#prop:k2018-arithmetic-characters, revision
e73d98b1b5c1e5abcdebf7d058e436d792b87982, source SHA-256
e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299.
The characteristic-zero premise of the field/Galois equivalence is retained.
Actual squared-Tate actions and coefficient schemes remain with their consumer.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.OverField (Base FScheme)

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.PreGaloisCategory CategoryTheory.MonObj
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber fiberToFinite)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open AlgebraicGeometry.Scheme.FiniteEtale

namespace AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.Coefficients

universe u
attribute [local instance] Over.cartesianMonoidalCategory

variable (F : Type u) [Field F]

/-- The actual chosen algebraic-closure point in the field coefficient
realization for `K2-018#prop:k2018-arithmetic-characters`. -/
abbrev geometricPoint := FieldGalois.geometricPoint F

/-- The actual finite-etale fibre automorphism group, for the field
coefficient realization in `K2-018#prop:k2018-arithmetic-characters`. -/
abbrev ArithmeticGroup := FieldGalois.FieldFundamentalGroup F

/-- Actual point automorphism induced by the inverse field automorphism,
for `K2-018#prop:k2018-arithmetic-characters`. The inverse gives a homomorphism
into categorical automorphisms, whose multiplication reverses arrow composition. -/
def galoisPointAutomorphism (σ : Field.absoluteGaloisGroup F) :
    Aut (Over.mk (geometricPoint F)) where
  hom := FieldGalois.pointEnd F σ⁻¹
  inv := FieldGalois.pointEnd F σ
  hom_inv_id := by
    rw [← FieldGalois.pointEnd_mul, inv_mul_cancel, FieldGalois.pointEnd_one]
  inv_hom_id := by
    rw [← FieldGalois.pointEnd_mul, mul_inv_cancel, FieldGalois.pointEnd_one]

/-- The actual absolute-Galois-to-point-automorphism homomorphism, with
the Spec variance for `K2-018#prop:k2018-arithmetic-characters`. -/
def galoisPointHom : Field.absoluteGaloisGroup F →* Aut (Over.mk (geometricPoint F)) where
  toFun := galoisPointAutomorphism F
  map_one' := by
    apply Aut.ext
    change FieldGalois.pointEnd F (1 : Field.absoluteGaloisGroup F)⁻¹ = 𝟙 _
    rw [inv_one, FieldGalois.pointEnd_one]
  map_mul' σ τ := by
    apply Aut.ext
    change FieldGalois.pointEnd F (σ * τ)⁻¹ =
      FieldGalois.pointEnd F τ⁻¹ ≫ FieldGalois.pointEnd F σ⁻¹
    rw [mul_inv_rev, FieldGalois.pointEnd_mul]

variable [CharZero F]

/-- Actual point descent homomorphism on the field fibre automorphism
group, for `K2-018#prop:k2018-arithmetic-characters`. The field/Galois
identification is the proved `fundamentalGroupContinuousEquiv`. -/
def sigma : ArithmeticGroup F →* Aut (Over.mk (geometricPoint F)) :=
  (galoisPointHom F).comp (FieldGalois.fundamentalGroupContinuousEquiv F).symm.toMonoidHom

/-- The precise inverse-variance formula required by
`CoefficientRealization.descent`, for
`K2-018#prop:k2018-arithmetic-characters`. -/
-- Keep this original canonical-map simp formula alongside its lower evaluation expansion.
@[simp, nolint simpNF] theorem sigma_inv_hom (g : ArithmeticGroup F) :
    (sigma F g⁻¹).hom = FieldGalois.pointEnd F
      ((FieldGalois.fundamentalGroupContinuousEquiv F).symm g) := by
  change FieldGalois.pointEnd F
    (((FieldGalois.fundamentalGroupContinuousEquiv F).symm g⁻¹)⁻¹) = _
  rw [map_inv, inv_inv]

/-- Natural evaluation of the actual fibre automorphism has exactly the
scheme descent formula used in `K2-018#prop:k2018-arithmetic-characters`.
It follows from the proved field fundamental-group action, not a descent premise. -/
theorem fiber_evaluation_descent (g : ArithmeticGroup F)
    (Y : Scheme.FiniteEtale (Base F)) (p : Fiber (geometricPoint F) Y) :
    g.hom.app Y p = (sigma F g⁻¹).hom ≫ p := by
  rw [sigma_inv_hom]
  have h := FieldGalois.fundamentalGroupContinuousEquiv_apply F
    ((FieldGalois.fundamentalGroupContinuousEquiv F).symm g) Y p
  simpa only [ContinuousMulEquiv.apply_symm_apply, FieldGalois.act] using h

variable (n : ℕ) [NeZero n]

/-- The actual finite cyclotomic character on the actual field fibre group,
for `K2-018#prop:k2018-arithmetic-characters`, transferred from the constructed
absolute Galois character without a supplied character or identification premise. -/
def arithmeticCharacter : ArithmeticGroup F →* (ZMod n)ˣ :=
  (Field.absoluteGaloisGroup.CyclotomicCharacter.character F n).comp
    (FieldGalois.fundamentalGroupContinuousEquiv F).symm.toMonoidHom

/-- Continuity of the transferred actual cyclotomic value, for
`K2-018#prop:k2018-arithmetic-characters`, using the proved topological
field fundamental-group equivalence. -/
theorem arithmeticCharacter_continuous_value :
    Continuous (fun g : ArithmeticGroup F => (arithmeticCharacter F n g : ZMod n)) :=
  (Field.absoluteGaloisGroup.CyclotomicCharacter.character_continuous_value F n).comp
    (FieldGalois.fundamentalGroupContinuousEquiv F).continuous_invFun

end AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.Coefficients

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 81b6401bb7b0272ec33e81cd587123276e6453afaed38577220d30d658ab32a1.
Definitions, hypotheses and universes are retained modulo native names. -/
