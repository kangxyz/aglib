/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.PrincipalInterchange
public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.SimplexFaces

/-!
# SimplexFaceIdentities for finite correspondences on the two-dimensional torus

Native migration from `lean/R5Lab/Aglib/AlgebraicGeometry/Torus/FiniteCorrespondence/`
leaf `SimplexFaceIdentities.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`6986bae1739724b1f573d056b5ca8badddd2e65974c32dc5458d3e16e510ee3b`.

The Laurent object is `MonoidAlgebra R (Multiplicative (ℤ × ℤ))` in its original
coordinate order. Statements retain their displayed finiteness, normality,
Noetherianity, flatness, regularity and scalar-map hypotheses.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry.Torus.FiniteCorrespondence
open _root_.Module.CommutingAutomorphisms
open _root_.Module.CommutingAutomorphisms.LaurentSupport
open MonoidAlgebra (FiniteDominantPrime)
universe u

/-- The two literal quotient-fibre cycle operators for a codimension-two
simplex face agree, on every cycle over every field in every degree. -/
theorem simplexFaceCycle_comp (K : Type u) [Field K] (n : ℕ)
    (i : Fin (n + 3)) (j : Fin (n + 2)) :
    (simplexFaceCycle K n j).comp (simplexFaceCycle K (n + 1) i) =
      (simplexFaceCycle K n (j.predAbove i)).comp
        (simplexFaceCycle K (n + 1) (i.succAbove j)) := by
  let : IsIntegrallyClosed (AlgebraicSimplex.CoordinateRing K (n + 2)) :=
    IsIntegrallyClosed.of_equiv (AlgebraicSimplex.polynomialEquiv K (n + 2)).symm.toRingEquiv
  let a := AlgebraicSimplex.coordinate K (n + 2) i
  let b := AlgebraicSimplex.coordinate K (n + 2) (i.succAbove j)
  have hfb : (AlgebraicSimplex.face K i).toRingHom b = AlgebraicSimplex.coordinate K (n + 1) j :=
    AlgebraicSimplex.face_coordinate_succAbove K i j
  have hf'a : (AlgebraicSimplex.face K (i.succAbove j)).toRingHom a =
      AlgebraicSimplex.coordinate K (n + 1) (j.predAbove i) := by
    change AlgebraicSimplex.face K (i.succAbove j)
      (AlgebraicSimplex.coordinate K (n + 2) i) = _
    have h := AlgebraicSimplex.face_coordinate_succAbove K
      (i.succAbove j) (j.predAbove i)
    simpa only [Fin.succAbove_succAbove_predAbove] using h
  change (quotientFibreCycleMapFor (AlgebraicSimplex.face K j).toRingHom).comp
      (quotientFibreCycleMapFor (AlgebraicSimplex.face K i).toRingHom) =
    (quotientFibreCycleMapFor (AlgebraicSimplex.face K (j.predAbove i)).toRingHom).comp
      (quotientFibreCycleMapFor (AlgebraicSimplex.face K (i.succAbove j)).toRingHom)
  apply quotientFibreCycleMapFor_principal_square
    (AlgebraicSimplex.face K i).toRingHom (AlgebraicSimplex.face K j).toRingHom
    (AlgebraicSimplex.face K (i.succAbove j)).toRingHom
    (AlgebraicSimplex.face K (j.predAbove i)).toRingHom a b
    (AlgebraicSimplex.coordinate_ne_zero K (n + 2) i)
    (AlgebraicSimplex.coordinate_ne_zero K (n + 2) (i.succAbove j))
    (AlgebraicSimplex.face_surjective K i) (AlgebraicSimplex.ker_face K i)
    (by rw [hfb]; exact AlgebraicSimplex.coordinate_ne_zero K (n + 1) j)
    (AlgebraicSimplex.face_surjective K j)
    (by rw [hfb]; exact AlgebraicSimplex.ker_face K j)
    (AlgebraicSimplex.face_surjective K (i.succAbove j))
    (AlgebraicSimplex.ker_face K (i.succAbove j))
    (by rw [hf'a]; exact AlgebraicSimplex.coordinate_ne_zero K (n + 1) (j.predAbove i))
    (AlgebraicSimplex.face_surjective K (j.predAbove i))
    (by rw [hf'a]; exact AlgebraicSimplex.ker_face K (j.predAbove i))
  exact congrArg (fun f : AlgebraicSimplex.CoordinateRing K (n + 2) →ₐ[K]
    AlgebraicSimplex.CoordinateRing K n => f.toRingHom) (AlgebraicSimplex.face_comp K i j)

/-- The standard indexed identity for the alternating simplex boundary. -/
theorem simplexFaceCycle_comp_of_le (K : Type u) [Field K] (n : ℕ)
    {i j : Fin (n + 2)} (h : i ≤ j) :
    (simplexFaceCycle K n i).comp (simplexFaceCycle K (n + 1) j.succ) =
      (simplexFaceCycle K n j).comp (simplexFaceCycle K (n + 1) i.castSucc) := by
  have he := simplexFaceCycle_comp K n j.succ i
  rwa [Fin.succAbove_succ_of_le _ _ h, Fin.predAbove_succ_of_le _ _ h] at he

end AlgebraicGeometry.Torus.FiniteCorrespondence
