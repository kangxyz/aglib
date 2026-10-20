/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.SimplexFieldPullback
public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.FlatDictionary
public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.CoefficientComposition
public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.SimplexFaces

/-!
# SimplexFieldFaces for finite correspondences on the two-dimensional torus

Native migration from `lean/R5Lab/Aglib/AlgebraicGeometry/Torus/FiniteCorrespondence/`
leaf `SimplexFieldFaces.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`c74c9f20bd72cf873387a1084c3a5fe74551b43e949cc0d480ad37a6847b406b`.

The Laurent object is `MonoidAlgebra R (Multiplicative (ℤ × ℤ))` in its original
coordinate order. Statements retain their displayed finiteness, normality,
Noetherianity, flatness, regularity and scalar-map hypotheses.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped AlgebraMonoidAlgebra TensorProduct
namespace AlgebraicGeometry.Torus.FiniteCorrespondence.BaseChange
open _root_.Module.CommutingAutomorphisms
open _root_.Module.CommutingAutomorphisms.LaurentSupport
open MonoidAlgebra (FiniteDominantPrime)
open LaurentSupport
universe u

variable {K L : Type u} [Field K] [Field L]

theorem simplexFieldPullback_eq_quotientFor (f : K →+* L) (d : ℕ) :
    simplexFieldPullback f d = quotientFibreCycleMapFor (AlgebraicSimplex.coefficientMap f d) := by
  let := (AlgebraicSimplex.coefficientMap f d).toAlgebra
  let : Module.Flat (AlgebraicSimplex.CoordinateRing K d)
    (AlgebraicSimplex.CoordinateRing L d) := AlgebraicSimplex.coefficientMap_flat f d
  exact quotientCycle_eq_flatPullback.symm

/-- All five native field/face squares on every actual point cycle. -/
theorem simplexFieldPullback_face (f : K →+* L) (j : Fin 2) (i : Fin (j.val + 2)) :
    (simplexFieldPullback f j.val).comp (simplexFaceCycle K j.val i) =
      (simplexFaceCycle L j.val i).comp (simplexFieldPullback f (j.val + 1)) := by
  apply FreeAbelianGroup.lift_ext
  intro p
  apply (FreeAbelianGroup.equivFinsupp _).injective
  ext q
  simp only [AddMonoidHom.comp_apply, simplexFieldPullback_eq_quotientFor]
  change FreeAbelianGroup.coeff q (quotientFibreCycleMapFor (AlgebraicSimplex.coefficientMap f
    j.val)
      (quotientFibreCycleMapFor (AlgebraicSimplex.face K i).toRingHom (FreeAbelianGroup.of p))) =
    FreeAbelianGroup.coeff q (quotientFibreCycleMapFor (AlgebraicSimplex.face L i).toRingHom
      (quotientFibreCycleMapFor (AlgebraicSimplex.coefficientMap f (j.val + 1))
        (FreeAbelianGroup.of p)))
  let : IsIntegrallyClosed (AlgebraicSimplex.CoordinateRing K (j.val + 1)) :=
    IsIntegrallyClosed.of_equiv (AlgebraicSimplex.polynomialEquiv K (j.val + 1)).symm.toRingEquiv
  have hdom : ∀ Q ∈ (p.val.map (coefficientMap (AlgebraicSimplex.face K
    i).toRingHom)).minimalPrimes,
      Q.under (AlgebraicSimplex.CoordinateRing K j.val) = ⊥ := by
    let := (AlgebraicSimplex.face K i).toAlgebra
    exact fun Q hQ => principalPoint_minimal_contract_zero p _
      (AlgebraicSimplex.face_surjective K i) (AlgebraicSimplex.ker_face K i) Q hQ
  rw [flat_second_coeffFor _ _ (AlgebraicSimplex.coefficientMap_flat f j.val) p hdom q,
    flat_principal_coeffFor _ (AlgebraicSimplex.coefficientMap_flat f (j.val + 1)) _
      (AlgebraicSimplex.coordinate L (j.val + 1) i)
      (AlgebraicSimplex.coordinate_ne_zero L (j.val + 1) i)
      (AlgebraicSimplex.face_surjective L i) (AlgebraicSimplex.ker_face L i) p q]
  let F : Ideal (Laurent (AlgebraicSimplex.CoordinateRing L j.val)) → ℤ := fun I =>
    ((Module.length (Localization.AtPrime q.val)
      (Localization.AtPrime q.val ⊗[Laurent (AlgebraicSimplex.CoordinateRing L j.val)]
        (Laurent (AlgebraicSimplex.CoordinateRing L j.val) ⧸ I))).toNat : ℤ)
  have h₁ := mappedIdeal_comp (AlgebraicSimplex.face K i).toRingHom
    (AlgebraicSimplex.coefficientMap f j.val) p.val
  have h₂ := mappedIdeal_comp (AlgebraicSimplex.coefficientMap f (j.val + 1))
    (AlgebraicSimplex.face L i).toRingHom p.val
  have he := congrArg (fun h : AlgebraicSimplex.CoordinateRing K (j.val + 1) →+*
      AlgebraicSimplex.CoordinateRing L j.val => p.val.map (coefficientMap h))
    (AlgebraicSimplex.coefficientMap_face f i)
  exact congrArg F (h₁.trans (he.trans h₂.symm))

end AlgebraicGeometry.Torus.FiniteCorrespondence.BaseChange
