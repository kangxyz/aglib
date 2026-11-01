/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SerreLerayEdge
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.FiniteSurjectiveDescent
public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.Composition

/-! # Constructibility descent from a surjective composition

If the original inner map and its composite preserve constructibility in all
higher degrees, then the outer map does too. The inverse-image unit is actually
monic, its cokernel is constructible, and strong degree induction uses the
positive-truncation reverse Leray edge. No finiteness, flatness, base-change,
acyclicity, or supplied filtration of the inner map is assumed. Properness is
needed by geometric suppliers, not by this descent argument.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u dY dX dS

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {Y X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
  [HasDerivedCategory.{dY} (AbelianSheaf.{u, u + 1} Y)]
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]

omit [IsNoetherian X] in
/-- The positive original Leray diagonal recovers the next image of the
ordinary direct image, without assuming the inner map is acyclic. -/
theorem higherDirectImage_directImage_isConstructible_of_positive_diagonal
    (f : X ⟶ S) (p : Y ⟶ X) (G : AbelianSheaf.{u, u + 1} Y) (n : ℕ)
    (hdiag : ∀ j : ℕ, 0 < j → j ≤ n → Constructible.IsConstructible
      ((higherDirectImage f (n - j)).obj ((higherDirectImage p j).obj G)))
    (hcomp : Constructible.IsConstructible
      ((higherDirectImage (p ≫ f) (n + 1)).obj G)) :
    Constructible.IsConstructible
      ((higherDirectImage f (n + 1)).obj ((directImage p).obj G)) := by
  let K := (derivedDirectImage p).obj
    ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj G)
  let : K.IsGE 0 := (directImage p).rightDerivedFunctorPlus_isGE _ 0
  let H := DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S)
    (n + 1 : ℕ)
  let e := (higherDirectImageIso (p ≫ f) (n + 1)).app G ≪≫
    H.mapIso ((derivedDirectImageCompIso f p).app
      ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj G))
  have hK := (directImage f).rightDerived_property_of_positive_diagonal
    (Constructible.IsConstructible (X := S)) K n
    (fun j hj hn => (Constructible.isConstructible_iff_of_iso
      ((higherDirectImage f (n - j)).mapIso ((higherDirectImageIso p j).app G))).mp
        (hdiag j hj hn))
    ((Constructible.isConstructible_iff_of_iso e).mp hcomp)
  let e0 := ((higherDirectImageIso p 0).app G).symm ≪≫
    (directImage p).rightDerivedZeroIsoSelf.app G
  exact (Constructible.isConstructible_iff_of_iso
    ((higherDirectImage f (n + 1)).mapIso e0)).mp hK

/-- The same surjective unit and its actual cokernel descend constructibility
by strong induction in the degree. Only the inner map and the composite are
supplied by geometry; the outer conclusion is constructed. -/
theorem higherDirectImage_isConstructible_of_surjective_composition
    (f : X ⟶ S) (p : Y ⟶ X) [Surjective p]
    (hp : ∀ (j : ℕ) (G : AbelianSheaf.{u, u + 1} Y),
      Constructible.IsConstructible G →
      Constructible.IsConstructible ((higherDirectImage p j).obj G))
    (hcomp : ∀ (j : ℕ) (G : AbelianSheaf.{u, u + 1} Y),
      Constructible.IsConstructible G →
      Constructible.IsConstructible ((higherDirectImage (p ≫ f) j).obj G)) :
    ∀ (q : ℕ) (F : AbelianSheaf.{u, u + 1} X), Constructible.IsConstructible F →
      Constructible.IsConstructible ((higherDirectImage f q).obj F) := by
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro F hF
    let G := (inverseImage p).obj F
    have hG : Constructible.IsConstructible G :=
      Constructible.isConstructible_pullback_of_qcqs p hF
    let a := (inverseImageAdjunction p).unit.app F
    let : Mono a := mono_inverseImage_unit_of_surjective p F
    cases q with
    | zero =>
      have hcomp0 := (Constructible.isConstructible_iff_of_iso
        ((directImage (p ≫ f)).rightDerivedZeroIsoSelf.app G)).mp (hcomp 0 G hG)
      have hE := (Constructible.isConstructible_iff_of_iso
        ((directImageCompIso f p).app G)).mpr hcomp0
      have hF0 := Constructible.isConstructible_of_mono_of_noetherian
        ((directImage f).map a) hE
      exact (Constructible.isConstructible_iff_of_iso
        ((directImage f).rightDerivedZeroIsoSelf.app F)).mpr hF0
    | succ n =>
      have hE := (Constructible.isConstructible_iff_of_iso
        ((directImage p).rightDerivedZeroIsoSelf.app G)).mp (hp 0 G hG)
      have hQ : Constructible.IsConstructible (cokernel a) :=
        Constructible.isConstructible_cokernel a hF hE
      have hQn := ih n (by omega) (cokernel a) hQ
      have hEn : Constructible.IsConstructible
          ((higherDirectImage f (n + 1)).obj ((directImage p).obj G)) := by
        apply higherDirectImage_directImage_isConstructible_of_positive_diagonal
          f p G n ?_ (hcomp (n + 1) G hG)
        intro j hj hn
        exact ih (n - j) (by omega) _ (hp j G hG)
      let T := ShortComplex.mk a (cokernel.π a) (cokernel.condition a)
      have hT : T.ShortExact := { exact := ShortComplex.exact_cokernel a }
      exact Functor.rightDerived_property_succ_of_shortExact (directImage f)
        (Constructible.IsConstructible (X := S)) T hT n hQn hEn

end AlgebraicGeometry.Scheme.EtaleCohomology
