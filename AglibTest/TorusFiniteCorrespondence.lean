/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.FieldPullback
import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.LowSimplexFaces
import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.ModulePrincipalNaturality
import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.ScalarPoint
import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.ScalarTransport
import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.SimplexFaceIdentities
import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.ScalarGraphCycle

open AlgebraicGeometry
open AlgebraicGeometry.Torus.FiniteCorrespondence
open Module.CommutingAutomorphisms
open Module.CommutingAutomorphisms.LaurentSupport
open MonoidAlgebra (FiniteDominantPrime)
open scoped TensorProduct

noncomputable section

namespace AglibTest.TorusFiniteCorrespondence

universe u

/-- The lower length interface only asks that the quotient be Noetherian. -/
example {A : Type u} [CommRing A] (I : Ideal A) [IsNoetherianRing (A ⧸ I)]
    (q : Ideal A) [q.IsPrime] (hq : q ∈ I.minimalPrimes) :
    Module.length (Localization.AtPrime q)
      (Localization.AtPrime q ⊗[A] (A ⧸ I)) ≠ ⊤ :=
  Module.length_localized_quotient_ne_top I q hq

/-- The geometric dictionary uses exactly the shared lower prime carrier. -/
example (R : Type u) [CommRing R] [_root_.IsReduced R] :
    FiniteDominantPrime R ≃ Subscheme.FiniteDominantSubscheme R :=
  Subscheme.pointEquivSubscheme

/-- Scalar cycles have the actual rank-one length, in the stated coordinate order. -/
example {K : Type u} [Field K] (a b : Kˣ) :
    objectCycle (Object.unitPair a b) = FreeAbelianGroup.of (scalarPoint a b) :=
  objectCycle_unitPair a b

/-- Original module cycles commute with the actual face extension in every degree. -/
example (K : Type u) [Field K] (n : ℕ) (i : Fin (n + 2))
    (X : Object (AlgebraicSimplex.CoordinateRing K (n + 1))) :
    let := (AlgebraicSimplex.face K i).toAlgebra
    objectCycle (X.baseChange (AlgebraicSimplex.CoordinateRing K n)) =
      simplexFaceCycle K n i (objectCycle X) :=
  simplexFace_objectCycle K n i X

/-- The all-degree face identity keeps its original contravariant ordering. -/
example (K : Type u) [Field K] (n : ℕ) {i j : Fin (n + 2)} (h : i ≤ j) :
    (simplexFaceCycle K n i).comp (simplexFaceCycle K (n + 1) j.succ) =
      (simplexFaceCycle K n j).comp (simplexFaceCycle K (n + 1) i.castSucc) :=
  simplexFaceCycle_comp_of_le K n h

/-- Field functoriality uses the literal ring-homomorphism composition. -/
example {K L M : Type u} [Field K] [Field L] [Field M]
    (f : K →+* L) (g : L →+* M) (d : ℕ) :
    (simplexFieldPullback g d).comp (simplexFieldPullback f d) =
      simplexFieldPullback (g.comp f) d :=
  BaseChange.simplexFieldPullback_comp f g d

/-- The field/face square retains its actual five-case scope. -/
example {K L : Type u} [Field K] [Field L]
    (f : K →+* L) (j : Fin 2) (i : Fin (j.val + 2)) :
    (simplexFieldPullback f j.val).comp (simplexFaceCycle K j.val i) =
      (simplexFaceCycle L j.val i).comp (simplexFieldPullback f (j.val + 1)) :=
  BaseChange.simplexFieldPullback_face f j i

/-- Scalar graph transport keeps the separate one-variable Laurent source. -/
example {R : Type u} [CommRing R] [IsNoetherianRing R]
    (X : Module.Automorphism.Object R) (f : Rˣ) :
    objectCycle (X.tensor (Module.Automorphism.Object.unit f)) =
      ScalarGraph.graphCycles f (ScalarGraph.oneObjectCycle X) :=
  ScalarGraph.objectCycle_tensor_graph X f

end AglibTest.TorusFiniteCorrespondence
