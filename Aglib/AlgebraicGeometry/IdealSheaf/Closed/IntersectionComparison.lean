/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Closed intersections from equal inverse-image ideals

Source: `R5Lab.Aglib.AlgebraicGeometry.IdealSheaf.IntersectionComparison`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `a5813595c03239bad1f3fee37b483569b909af24fa969f0d38661a0c8fe78331`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

section IdealIntersectionComparison23

/-!
# Scheme-theoretic intersection comparison from equality modulo a kernel

For actual ideal sheaves `I` and `J` on `X` and an arbitrary scheme morphism
`j : C ⟶ X`, equality `j.ker ⊔ I = j.ker ⊔ J` identifies their actual pullbacks
to `C`. In particular this applies to every closed immersion, without a
reducedness, support, or length hypothesis. The comparison preserves the
projection to `C` and both resulting maps to `X`, and is an isomorphism over
any base of `C`.
-/

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X C S : Scheme.{u}}

/-- A morphism pulls its own kernel ideal back to zero. -/
@[simp]
theorem comap_ker_eq_bot (j : C ⟶ X) : j.ker.comap j = ⊥ := by
  apply le_bot_iff.mp
  simpa only [map_bot] using (comap_map_le (⊥ : C.IdealSheafData) j)

/-- Equality modulo the kernel implies equality of actual pullback ideal sheaves. -/
theorem comap_eq_of_ker_sup_eq (I J : X.IdealSheafData) (j : C ⟶ X)
    (h : j.ker ⊔ I = j.ker ⊔ J) : I.comap j = J.comap j := by
  have h' := congrArg (fun K : X.IdealSheafData => K.comap j) h
  simpa only [comap_sup, comap_ker_eq_bot, bot_sup_eq] using h'

/-- Equality of ideal sheaves identifies their actual associated closed subschemes. -/
def subschemeIsoOfEq {I J : X.IdealSheafData} (h : I = J) :
    I.subscheme ≅ J.subscheme :=
  eqToIso (congrArg (fun K : X.IdealSheafData => K.subscheme) h)

@[reassoc (attr := simp)]
theorem subschemeIsoOfEq_hom_subschemeι {I J : X.IdealSheafData} (h : I = J) :
    (subschemeIsoOfEq h).hom ≫ J.subschemeι = I.subschemeι := by
  subst J
  simp [subschemeIsoOfEq]

@[reassoc (attr := simp)]
theorem subschemeIsoOfEq_inv_subschemeι {I J : X.IdealSheafData} (h : I = J) :
    (subschemeIsoOfEq h).inv ≫ I.subschemeι = J.subschemeι := by
  subst J
  simp [subschemeIsoOfEq]

/-- An actual scheme comparison of intersections with equal pullback ideals. -/
def intersectionIsoOfComapEq (I J : X.IdealSheafData) (j : C ⟶ X)
    (h : I.comap j = J.comap j) :
    pullback I.subschemeι j ≅ pullback J.subschemeι j :=
  pullbackSymmetry I.subschemeι j ≪≫ (I.comapIso j).symm ≪≫
    subschemeIsoOfEq h ≪≫ J.comapIso j ≪≫ pullbackSymmetry j J.subschemeι

@[reassoc (attr := simp)]
theorem intersectionIsoOfComapEq_hom_snd (I J : X.IdealSheafData) (j : C ⟶ X)
    (h : I.comap j = J.comap j) :
    (intersectionIsoOfComapEq I J j h).hom ≫ pullback.snd J.subschemeι j =
      pullback.snd I.subschemeι j := by
  simp [intersectionIsoOfComapEq]

@[reassoc (attr := simp)]
theorem intersectionIsoOfComapEq_inv_snd (I J : X.IdealSheafData) (j : C ⟶ X)
    (h : I.comap j = J.comap j) :
    (intersectionIsoOfComapEq I J j h).inv ≫ pullback.snd I.subschemeι j =
      pullback.snd J.subschemeι j := by
  rw [← cancel_epi (intersectionIsoOfComapEq I J j h).hom]
  simp

/-- Equality of sums with the kernel produces the actual intersection isomorphism. -/
def intersectionIsoOfKerSupEq (I J : X.IdealSheafData) (j : C ⟶ X)
    (h : j.ker ⊔ I = j.ker ⊔ J) :
    pullback I.subschemeι j ≅ pullback J.subschemeι j :=
  intersectionIsoOfComapEq I J j (comap_eq_of_ker_sup_eq I J j h)

@[reassoc (attr := simp)]
theorem intersectionIsoOfKerSupEq_hom_snd (I J : X.IdealSheafData) (j : C ⟶ X)
    (h : j.ker ⊔ I = j.ker ⊔ J) :
    (intersectionIsoOfKerSupEq I J j h).hom ≫ pullback.snd J.subschemeι j =
      pullback.snd I.subschemeι j :=
  intersectionIsoOfComapEq_hom_snd I J j _

@[reassoc (attr := simp)]
theorem intersectionIsoOfKerSupEq_inv_snd (I J : X.IdealSheafData) (j : C ⟶ X)
    (h : j.ker ⊔ I = j.ker ⊔ J) :
    (intersectionIsoOfKerSupEq I J j h).inv ≫ pullback.snd I.subschemeι j =
      pullback.snd J.subschemeι j :=
  intersectionIsoOfComapEq_inv_snd I J j _

/-- The comparison also respects the first projections after their actual
closed-subscheme inclusions into the common ambient scheme. -/
@[reassoc]
theorem intersectionIsoOfKerSupEq_hom_fst_subschemeι
    (I J : X.IdealSheafData) (j : C ⟶ X) (h : j.ker ⊔ I = j.ker ⊔ J) :
    (intersectionIsoOfKerSupEq I J j h).hom ≫
        pullback.fst J.subschemeι j ≫ J.subschemeι =
      pullback.fst I.subschemeι j ≫ I.subschemeι := by
  rw [pullback.condition, intersectionIsoOfKerSupEq_hom_snd_assoc, pullback.condition]

@[reassoc]
theorem intersectionIsoOfKerSupEq_inv_fst_subschemeι
    (I J : X.IdealSheafData) (j : C ⟶ X) (h : j.ker ⊔ I = j.ker ⊔ J) :
    (intersectionIsoOfKerSupEq I J j h).inv ≫
        pullback.fst I.subschemeι j ≫ I.subschemeι =
      pullback.fst J.subschemeι j ≫ J.subschemeι := by
  rw [pullback.condition, intersectionIsoOfKerSupEq_inv_snd_assoc, pullback.condition]

/-- The same intersection comparison over any actual structure map of `C`. -/
def intersectionOverIsoOfKerSupEq (I J : X.IdealSheafData) (j : C ⟶ X)
    (h : j.ker ⊔ I = j.ker ⊔ J) (structureMap : C ⟶ S) :
    Over.mk (pullback.snd I.subschemeι j ≫ structureMap) ≅
      Over.mk (pullback.snd J.subschemeι j ≫ structureMap) :=
  Over.isoMk (intersectionIsoOfKerSupEq I J j h) (by simp)

@[simp]
theorem intersectionOverIsoOfKerSupEq_hom_left
    (I J : X.IdealSheafData) (j : C ⟶ X) (h : j.ker ⊔ I = j.ker ⊔ J)
    (structureMap : C ⟶ S) :
    (intersectionOverIsoOfKerSupEq I J j h structureMap).hom.left =
      (intersectionIsoOfKerSupEq I J j h).hom := rfl

@[simp]
theorem intersectionOverIsoOfKerSupEq_inv_left
    (I J : X.IdealSheafData) (j : C ⟶ X) (h : j.ker ⊔ I = j.ker ⊔ J)
    (structureMap : C ⟶ S) :
    (intersectionOverIsoOfKerSupEq I J j h structureMap).inv.left =
      (intersectionIsoOfKerSupEq I J j h).inv := rfl

end AlgebraicGeometry.Scheme.IdealSheafData

end
end IdealIntersectionComparison23
