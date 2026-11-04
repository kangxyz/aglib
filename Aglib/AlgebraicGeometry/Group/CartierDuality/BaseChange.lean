/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.UniversalProperty.BaseChange

/-! Canonical comparison of the same selected Cartier duals by the actual character functor. -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.Group.CartierDuality

universe u v w

open AlgebraicGeometry.Scheme.OverField (FScheme Base)

private theorem representer_unique_character
    {C : Type v} [Category.{u} C] {F : Cᵒᵖ ⥤ Type w} {R S U : C}
    (a : F.RepresentableBy R) (b : F.RepresentableBy S) (p : U ⟶ R) :
    b.homEquiv (p ≫ (a.uniqueUpToIso b).hom) = a.homEquiv p := by
  have hU : b.homEquiv (a.uniqueUpToIso b).hom = a.homEquiv (𝟙 R) := by
    rw [Functor.RepresentableBy.uniqueUpToIso_hom, Yoneda.fullyFaithful_preimage]
    exact b.homEquiv.apply_symm_apply _
  have hP := b.homEquiv_comp p (a.uniqueUpToIso b).hom
  have hM := congrArg (fun x => F.map p.op x) hU
  exact hP.trans (hM.trans (a.homEquiv_eq p).symm)

variable {k : Type u} [Field k] (K : Type u) [Field K]
  (G : Grp (FScheme k)) [IsFinite G.X.hom] [IsCommMonObj G.X]

/-- The two existing native duals are compared through their actual character representations. -/
def dualGroupBaseChangeOverIso (i : Base K ⟶ Base k) :
    ((Over.pullback (i)).mapGrp.obj (dualGroup G)).X ≅
      (dualGroup (k := K) ((Over.pullback (i)).mapGrp.obj G)).X :=
  (characterRepresentableByBaseChange K G i).uniqueUpToIso
    (characterRepresentableBy (k := K) ((Over.pullback (i)).mapGrp.obj G))

/-- The comparison identifies the original actual character on every test scheme. -/
theorem dualGroupBaseChangeOverIso_character (i : Base K ⟶ Base k) (U : FScheme K)
    (p : U ⟶ ((Over.pullback (i)).mapGrp.obj (dualGroup G)).X) :
    characterEquiv (k := K) ((Over.pullback (i)).mapGrp.obj G) U
        (p ≫ (dualGroupBaseChangeOverIso K G i).hom) =
      characterEquivBaseChange G (Over.mk (i)) U p := by
  have h := representer_unique_character (characterRepresentableByBaseChange K G i)
    (characterRepresentableBy (k := K) ((Over.pullback (i)).mapGrp.obj G)) p
  exact h

end AlgebraicGeometry.Scheme.Group.CartierDuality
