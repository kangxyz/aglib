/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.EtaleTrace
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.Cohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.FiniteDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackEquivalence

/-! # Coprime finite-etale descent of original cohomology vanishing

The original trace retraction survives every coefficient functor. For an open
immersion and an actual finite completion of the cover, ordinary finite/open
exchange and finite direct-image cohomology give the compactified endpoint.
The source and target Ext universes are independent. Neither torsion descent
nor unbounded proper base change is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing

universe u e eY

attribute [local instance] hasSheafifyLarge

/-- A coprime finite-etale trace descends vanishing after any displayed
coefficient functor. No exactness of that further functor is required. -/
theorem subsingleton_H_obj_of_finiteEtale_coprime
    {U X : Scheme.{u}} [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    (V : Scheme.FiniteEtale U) (n : ℕ)
    (hn : ∀ x : U, V.obj.hom.finrank x = n)
    (F : AbelianSheaf.{u, u + 1} U) (p : ℕ)
    (hcop : n.Coprime p) (hp : p • 𝟙 F = 0)
    (L : AbelianSheaf.{u, u + 1} U ⥤ AbelianSheaf.{u, u + 1} X)
    (q : ℕ)
    [Subsingleton (Sheaf.H.{e} (L.obj
      ((directImage V.obj.hom).obj ((inverseImage V.obj.hom).obj F))) q)] :
    Subsingleton (Sheaf.H.{e} (L.obj F) q) := by
  let H := L ⋙ (Sheaf.functorH X.smallEtaleTopology q :
    AbelianSheaf.{u, u + 1} X ⥤ AddCommGrpCat.{e})
  let : Subsingleton (H.obj
      ((directImage V.obj.hom).obj ((inverseImage V.obj.hom).obj F))) :=
    inferInstanceAs (Subsingleton (Sheaf.H.{e} (L.obj
      ((directImage V.obj.hom).obj ((inverseImage V.obj.hom).obj F))) q))
  obtain ⟨r, hr⟩ := exists_finiteEtale_sheafRetraction_map V n hn F p hcop hp H
  have hsurj : Function.Surjective r := by
    intro x
    exact ⟨H.map ((inverseImageAdjunction V.obj.hom).unit.app F) x,
      congrArg (fun a => a x) hr⟩
  exact hsurj.subsingleton

/-- Vanishing on an actual finite completion of a prime-to-annihilator cover
descends to extension by zero on the original scheme. The square and the
coefficient are the original ones, not replacement compact-support objects. -/
theorem subsingleton_H_etaleLowerShriek_of_finiteEtale_coprime
    {U X Y : Scheme.{u}}
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    (V : Scheme.FiniteEtale U)
    (j : U ⟶ X) [IsOpenImmersion j]
    (b : Y ⟶ X) [IsFinite b]
    (j' : V.obj.left ⟶ Y) [IsOpenImmersion j']
    (sq : IsPullback j' V.obj.hom b j)
    (n : ℕ) (hn : ∀ x : U, V.obj.hom.finrank x = n)
    (F : AbelianSheaf.{u, u + 1} U) (p : ℕ)
    (hcop : n.Coprime p) (hp : p • 𝟙 F = 0) (q : ℕ)
    [Subsingleton (Sheaf.H.{eY} ((etaleLowerShriek j').obj
      ((inverseImage V.obj.hom).obj F)) q)] :
    Subsingleton (Sheaf.H.{e} ((etaleLowerShriek j).obj F) q) := by
  let G := (inverseImage V.obj.hom).obj F
  let : Subsingleton (Sheaf.H.{e}
      ((etaleLowerShriek j' ⋙ directImage b).obj G) q) :=
    (Finite.finiteCohomologyDirectImageAddEquiv.{u, eY, e}
      b ((etaleLowerShriek j').obj G) q).injective.subsingleton
  let : Subsingleton (Sheaf.H.{e}
      ((etaleLowerShriek j).obj ((directImage V.obj.hom).obj G)) q) :=
    (cohomologyMapIso_bijective
      ((etaleLowerShriekFiniteDirectImageIso b V.obj.hom j j' sq).app G) q).injective.subsingleton
  exact subsingleton_H_obj_of_finiteEtale_coprime V n hn F p hcop hp
    (etaleLowerShriek j) q

end AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing
