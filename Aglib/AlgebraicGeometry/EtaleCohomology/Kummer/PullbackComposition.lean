/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.BoundaryNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.TriangleCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackComposition
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisInstances

/-! # Composition of original roots-coefficient pullback

The existing whole roots coefficient triangle and native cohomological
composition give composition of the original roots maps. For a connected
final target the actual cover/fibre dictionaries are supplied internally.
No composition premise, new coefficient model or independent root coordinate
is introduced. In particular the final target may be a function-field spectrum.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients
open GroupCohomology.Kummer.CoefficientBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

universe u w w' w''

variable {X S T : Scheme.{u}} [ConnectedSpace T]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]
  [HasExt.{w''} (AbelianSheaf.{u, u + 1} T)]

/-- The original roots cohomology pullbacks compose in every degree. -/
theorem rootsCohomologyPullback_comp (f : S ⟶ X) (g : T ⟶ S)
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (q : ℕ)
    (a : Sheaf.H.{w} (mu X n) q) :
    rootsCohomologyPullback (g ≫ f) n hn hinv q a =
      rootsCohomologyPullback g n hn (levelInvertible f n hinv) q
        (rootsCohomologyPullback f n hn hinv q a) := by
  let z := Scheme.FiniteEtale.algebraicClosureResiduePoint T
    (Classical.choice (inferInstance : Nonempty T))
  have ht := TriangleCoherence.rootsPullbackIso_comp f g z n hn hinv
  have hc := cohomologyPullback_comp f g (mu X n) q a
  have hm := cohomologyPullback_coefficientMap g (rootsPullbackIso f n hn hinv).hom q
    (cohomologyPullback f (mu X n) q a)
  change Sheaf.H.map (rootsPullbackIso (g ≫ f) n hn hinv).hom q
      (cohomologyPullback (g ≫ f) (mu X n) q a) = _
  refine (congrArg (fun e => Sheaf.H.map e q
    (cohomologyPullback (g ≫ f) (mu X n) q a)) ht.symm).trans ?_
  rw [Sheaf.H.map_comp_apply, Sheaf.H.map_comp_apply]
  exact (congrArg (fun b =>
    Sheaf.H.map (rootsPullbackIso g n hn (levelInvertible f n hinv)).hom q
      (Sheaf.H.map ((inverseImage g).map (rootsPullbackIso f n hn hinv).hom) q b)) hc).trans
    (congrArg (Sheaf.H.map (rootsPullbackIso g n hn (levelInvertible f n hinv)).hom q)
      hm.symm)

/-- The same original composition law on the existing H1 roots map. -/
theorem h1Map_comp (f : S ⟶ X) (g : T ⟶ S)
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    (a : H1Etale X (mu X n)) :
    h1Map (g ≫ f) n hn hinv a =
      h1Map g n hn (levelInvertible f n hinv) (h1Map f n hn hinv a) :=
  rootsCohomologyPullback_comp f g n hn hinv 1 a

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
