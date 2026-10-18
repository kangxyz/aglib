/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Model.Naturality
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.RightAdjoint.Restriction.Counit
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.CartesianSections

/-!
# Composition of the actual ordinary closed-adjoint open maps

The native open base-change maps compose because their section maps are
the same original presheaf transports. Their original counit equations
then identify the direct and iterated closed-adjoint comparison. These are
the ordinary maps used termwise on the common ambient resolution.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme.Modules

variable {W' W U V' V P : Scheme.{u}}
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ P) (j : V ⟶ P)
  (c : W' ⟶ W) (d : W' ⟶ V') (k : V' ⟶ V)
  [IsOpenImmersion a] [IsOpenImmersion j] [IsOpenImmersion c] [IsOpenImmersion k]
  (h : IsPullback a b f j) (h' : IsPullback c d b k)

/-- The actual open base-change maps compose through the original restriction comparisons. -/
theorem canonicalOpenBaseChange_comp (M : U.Modules) :
    (restrictFunctor k).map ((cartesianOpenBaseChange a b f j h).hom.app M) ≫
        (cartesianOpenBaseChange c d b k h').hom.app (M.restrict a) =
      (restrictFunctorComp k j).inv.app ((pushforward f).obj M) ≫
        (cartesianOpenBaseChange (c ≫ a) d f (k ≫ j) (h'.paste_horiz h)).hom.app M ≫
          (pushforward d).map ((restrictFunctorComp c a).hom.app M) := by
  apply Scheme.Modules.hom_ext
  intro T
  simp only [Scheme.Modules.Hom.comp_app, restrictFunctor_map_app,
    cartesianOpenBaseChange_hom_app, restrictFunctorComp_inv_app_app,
    pushforward_map_app, restrictFunctorComp_hom_app_app]
  change M.presheaf.map _ ≫ M.presheaf.map _ =
    M.presheaf.map _ ≫ M.presheaf.map _ ≫ M.presheaf.map _
  simp only [← Functor.map_comp]
  congr 1

/-- The inverse comparison retains the same three original restriction arrows. -/
theorem canonicalOpenBaseChange_comp_inv (M : U.Modules) :
    (pushforward d).map ((restrictFunctorComp c a).hom.app M) ≫
        (cartesianOpenBaseChange c d b k h').inv.app (M.restrict a) ≫
          (restrictFunctor k).map ((cartesianOpenBaseChange a b f j h).inv.app M) =
      (cartesianOpenBaseChange (c ≫ a) d f (k ≫ j) (h'.paste_horiz h)).inv.app M ≫
        (restrictFunctorComp k j).hom.app ((pushforward f).obj M) := by
  let e₀ := (cartesianOpenBaseChange (c ≫ a) d f (k ≫ j) (h'.paste_horiz h)).app M
  let e₁ := (restrictFunctor k).mapIso ((cartesianOpenBaseChange a b f j h).app M)
  let e₂ := (cartesianOpenBaseChange c d b k h').app (M.restrict a)
  let rA := (restrictFunctorComp k j).app ((pushforward f).obj M)
  let rC := (pushforward d).mapIso ((restrictFunctorComp c a).app M)
  have hc : e₁.hom ≫ e₂.hom = rA.inv ≫ e₀.hom ≫ rC.hom :=
    canonicalOpenBaseChange_comp a b f j c d k h h' M
  have hi := congrArg (fun z => e₀.inv ≫ rA.hom ≫ z ≫ e₂.inv ≫ e₁.inv) hc
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Category.comp_id] at hi
  exact hi.symm

variable [IsClosedImmersion f] [IsClosedImmersion b] [IsClosedImmersion d]

/-- Direct and iterated ordinary closed-adjoint restriction are the same actual arrow. -/
theorem canonicalClosedRightAdjointOpenIso_comp (N : P.Modules) :
    (restrictFunctorComp c a).hom.app ((closedImmersionRightAdjoint f).obj N) ≫
        (restrictFunctor c).map
          ((closedImmersionRightAdjointOpenIso a b f j h).hom.app N) ≫
        (closedImmersionRightAdjointOpenIso c d b k h').hom.app (N.restrict j) =
      (closedImmersionRightAdjointOpenIso (c ≫ a) d f (k ≫ j)
        (h'.paste_horiz h)).hom.app N ≫
        (closedImmersionRightAdjoint d).map ((restrictFunctorComp k j).hom.app N) := by
  let K := (closedImmersionRightAdjoint f).obj N
  let O₁ := (closedImmersionRightAdjointOpenIso a b f j h).hom.app N
  let O₂ := (closedImmersionRightAdjointOpenIso c d b k h').hom.app (N.restrict j)
  let O₀ := (closedImmersionRightAdjointOpenIso (c ≫ a) d f (k ≫ j)
    (h'.paste_horiz h)).hom.app N
  let E := (closedImmersionRightAdjunction f).counit.app N
  let rC := (restrictFunctorComp c a).hom.app K
  let rA := (restrictFunctorComp k j).hom.app N
  apply ((closedImmersionRightAdjunction d).homEquiv
    (K.restrict (c ≫ a)) ((N.restrict j).restrict k)).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have h₂ := closedImmersionRightAdjointOpenIso_pushforward_counit c d b k h'
    (N.restrict j)
  have hn := (cartesianOpenBaseChange c d b k h').inv.naturality O₁
  have h₁ := closedImmersionRightAdjointOpenIso_pushforward_counit a b f j h N
  have h₀ := closedImmersionRightAdjointOpenIso_pushforward_counit
    (c ≫ a) d f (k ≫ j) (h'.paste_horiz h) N
  have hε := (closedImmersionRightAdjunction d).counit.naturality rA
  have hr := (restrictFunctorComp k j).hom.naturality E
  change (pushforward d).map ((restrictFunctor c).map O₁) ≫
      (cartesianOpenBaseChange c d b k h').inv.app
        ((closedImmersionRightAdjoint b).obj (N.restrict j)) =
    (cartesianOpenBaseChange c d b k h').inv.app (K.restrict a) ≫
      (restrictFunctor k).map ((pushforward b).map O₁) at hn
  change (pushforward d).map ((closedImmersionRightAdjoint d).map rA) ≫
      (closedImmersionRightAdjunction d).counit.app ((N.restrict j).restrict k) =
    (closedImmersionRightAdjunction d).counit.app (N.restrict (k ≫ j)) ≫ rA at hε
  change (restrictFunctor (k ≫ j)).map E ≫ rA =
    (restrictFunctorComp k j).hom.app ((pushforward f).obj K) ≫
      (restrictFunctor k).map ((restrictFunctor j).map E) at hr
  change (pushforward d).map rC ≫ (pushforward d).map ((restrictFunctor c).map O₁) ≫
      (pushforward d).map O₂ ≫
        (closedImmersionRightAdjunction d).counit.app ((N.restrict j).restrict k) =
    (pushforward d).map O₀ ≫
      (pushforward d).map ((closedImmersionRightAdjoint d).map rA) ≫
        (closedImmersionRightAdjunction d).counit.app ((N.restrict j).restrict k)
  rw [h₂]
  rw [← Category.assoc ((pushforward d).map ((restrictFunctor c).map O₁)), hn]
  rw [Category.assoc, ← Functor.map_comp, h₁, Functor.map_comp]
  rw [hε, ← Category.assoc ((pushforward d).map O₀), h₀]
  rw [Category.assoc, hr]
  have hc := congrArg (fun z => z ≫
      (restrictFunctor k).map ((restrictFunctor j).map E))
    (canonicalOpenBaseChange_comp_inv a b f j c d k h h' K)
  simpa only [Category.assoc] using hc

end AlgebraicGeometry.Scheme.Modules
