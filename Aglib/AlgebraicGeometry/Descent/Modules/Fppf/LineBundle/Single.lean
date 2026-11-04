/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Descent.Single
public import Aglib.AlgebraicGeometry.Descent.Modules.Fppf.LineBundleStack
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Fppf morphism descent for the original line bundles

The proved line-bundle stack descends morphisms and isomorphisms between given
original bundles along an fppf singleton. No descended object is selected.
Finite flat surjections to a locally Noetherian target supply the cover, also
after arbitrary parameter base change.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor Opposite

namespace AlgebraicGeometry.Scheme.Modules.FppfSingle

universe u

variable {Y Z : Scheme.{u}} (f : Y ⟶ Z)

/-- Flat surjections locally of finite presentation give the actual singleton fppf sieve. -/
theorem singleton_cover [Flat f] [Surjective f] [LocallyOfFinitePresentation f] :
    Sieve.ofArrows (fun _ : PUnit.{1} => Y) (fun _ : PUnit.{1} => f) ∈
      Scheme.fppfTopology Z := by
  simpa only [Sieve.ofArrows, Presieve.ofArrows_pUnit] using
    (Precoverage.generate_mem_toGrothendieck f.singleton_mem_fppfPrecoverage)

/-- Finite flat surjections to locally Noetherian targets give the required cover. -/
theorem singleton_cover_of_finite [IsFinite f] [Flat f] [Surjective f]
    [IsLocallyNoetherian Z] :
    Sieve.ofArrows (fun _ : PUnit.{1} => Y) (fun _ : PUnit.{1} => f) ∈
      Scheme.fppfTopology Z := by
  let : LocallyOfFinitePresentation f := inferInstance
  exact singleton_cover f

/-- An arbitrary parameter base change retains the original finite flat cover. -/
theorem singleton_cover_pullback_of_finite [IsFinite f] [Flat f] [Surjective f]
    [IsLocallyNoetherian Z] {T : Scheme.{u}} (p : T ⟶ Z) :
    Sieve.ofArrows (fun _ : PUnit.{1} => Limits.pullback f p)
      (fun _ : PUnit.{1} => Limits.pullback.snd f p) ∈ Scheme.fppfTopology T := by
  let : LocallyOfFinitePresentation f := inferInstance
  exact singleton_cover (Limits.pullback.snd f p)

variable (hf : Sieve.ofArrows (fun _ : PUnit.{1} => Y) (fun _ : PUnit.{1} => f) ∈
  Scheme.fppfTopology Z)
  {M N : lineBundlePseudofunctor.obj (.mk (op Z))}

/-- Lift the compatible descent morphism between the same original line bundles. -/
def liftMap
    (φ : (lineBundlePseudofunctor.toDescentData (fun _ : PUnit.{1} => f)).obj M ⟶
      (lineBundlePseudofunctor.toDescentData (fun _ : PUnit.{1} => f)).obj N) : M ⟶ N := by
  let := lineBundlePseudofunctor.isEquivalence_toDescentData (fun _ : PUnit.{1} => f) hf
  exact SingleDescent.liftHom lineBundlePseudofunctor f φ

/-- The lifted map has exactly the original upstairs value. -/
theorem liftMap_value
    (φ : (lineBundlePseudofunctor.toDescentData (fun _ : PUnit.{1} => f)).obj M ⟶
      (lineBundlePseudofunctor.toDescentData (fun _ : PUnit.{1} => f)).obj N) :
    (pullback f).map (liftMap f hf φ).hom = (φ.hom PUnit.unit).hom := by
  let := lineBundlePseudofunctor.isEquivalence_toDescentData (fun _ : PUnit.{1} => f) hf
  exact congrArg InducedCategory.Hom.hom
    (SingleDescent.liftHom_value lineBundlePseudofunctor f φ)

/-- Lift an isomorphism between the two original line bundles. -/
def liftIso
    (e : (lineBundlePseudofunctor.toDescentData (fun _ : PUnit.{1} => f)).obj M ≅
      (lineBundlePseudofunctor.toDescentData (fun _ : PUnit.{1} => f)).obj N) : M ≅ N := by
  let := lineBundlePseudofunctor.isEquivalence_toDescentData (fun _ : PUnit.{1} => f) hf
  exact SingleDescent.liftIso lineBundlePseudofunctor f e

/-- The whole descent isomorphism is recovered, including every transition. -/
theorem map_liftIso
    (e : (lineBundlePseudofunctor.toDescentData (fun _ : PUnit.{1} => f)).obj M ≅
      (lineBundlePseudofunctor.toDescentData (fun _ : PUnit.{1} => f)).obj N) :
    (lineBundlePseudofunctor.toDescentData (fun _ : PUnit.{1} => f)).mapIso
      (liftIso f hf e) = e := by
  let := lineBundlePseudofunctor.isEquivalence_toDescentData (fun _ : PUnit.{1} => f) hf
  exact SingleDescent.map_liftIso lineBundlePseudofunctor f e

end AlgebraicGeometry.Scheme.Modules.FppfSingle
