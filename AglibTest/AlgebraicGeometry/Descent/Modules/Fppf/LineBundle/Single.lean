/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.Modules.Fppf.LineBundle.Single

/-! Original line-bundle isomorphisms and arbitrary-parameter fppf covers. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

variable {Y Z : Scheme.{u}} (f : Y ⟶ Z)
  (hf : Sieve.ofArrows (fun _ : PUnit.{1} => Y) (fun _ : PUnit.{1} => f) ∈
    Scheme.fppfTopology Z)

example [IsFinite f] [Flat f] [Surjective f] [IsLocallyNoetherian Z]
    {T : Scheme.{u}} (p : T ⟶ Z) :
    Sieve.ofArrows (fun _ : PUnit.{1} => pullback f p)
      (fun _ : PUnit.{1} => pullback.snd f p) ∈ Scheme.fppfTopology T :=
  Scheme.Modules.FppfSingle.singleton_cover_pullback_of_finite f p

example {M N : Scheme.Modules.lineBundlePseudofunctor.obj (.mk (op Z))}
    (e : (Scheme.Modules.lineBundlePseudofunctor.toDescentData
        (fun _ : PUnit.{1} => f)).obj M ≅
      (Scheme.Modules.lineBundlePseudofunctor.toDescentData
        (fun _ : PUnit.{1} => f)).obj N) :
    (Scheme.Modules.lineBundlePseudofunctor.toDescentData
        (fun _ : PUnit.{1} => f)).mapIso
      (Scheme.Modules.FppfSingle.liftIso f hf e) = e :=
  Scheme.Modules.FppfSingle.map_liftIso f hf e
