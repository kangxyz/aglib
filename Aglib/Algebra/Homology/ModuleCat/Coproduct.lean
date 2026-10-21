/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Homology of direct sums of module complexes

The direct sum is the actual termwise categorical coproduct. Exactness of
module coproducts gives the canonical homology comparison, without any
finiteness or flatness hypothesis on the terms or their homology.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory CategoryTheory.Limits HomologicalComplex DirectSum

namespace ModuleCat

variable {R : Type (max u v)} [Ring R] {ι : Type v} {κ : Type w} {c : ComplexShape κ}

local instance : AB4OfSize.{v} (ModuleCat.{max u v} R) :=
  AB4OfSize_shrink (ModuleCat.{max u v} R)

/-- A family of complexes regarded as one complex in a discrete functor category. -/
def familyComplex (K : ι → HomologicalComplex (ModuleCat.{max u v} R) c) :
    HomologicalComplex (Discrete ι ⥤ ModuleCat.{max u v} R) c where
  X j := Discrete.functor (fun i => (K i).X j)
  d j k := Discrete.natTrans (fun i => (K i.as).d j k)
  shape j k h := by
    apply NatTrans.ext
    funext i
    exact (K i.as).shape j k h
  d_comp_d' j k l _ _ := by
    apply NatTrans.ext
    funext i
    exact (K i.as).d_comp_d j k l

/-- The termwise categorical direct sum of module complexes. -/
def coproductComplex (K : ι → HomologicalComplex (ModuleCat.{max u v} R) c) :
    HomologicalComplex (ModuleCat.{max u v} R) c :=
  (colim.mapHomologicalComplex c).obj (familyComplex K)

/-- The literal inclusion of one summand into the termwise coproduct. -/
def coproductComplexι (K : ι → HomologicalComplex (ModuleCat.{max u v} R) c) (i : ι) :
    K i ⟶ coproductComplex K :=
  ((colim.ι (Discrete.mk i)).mapHomologicalComplex c).app (familyComplex K)

/-- The original inclusions form the termwise coproduct cocone. -/
def coproductComplexCofan (K : ι → HomologicalComplex (ModuleCat.{max u v} R) c) : Cofan K :=
  Cofan.mk (coproductComplex K) (coproductComplexι K)

/-- The termwise construction is a coproduct also in the category of complexes. -/
def coproductComplexIsColimit (K : ι → HomologicalComplex (ModuleCat.{max u v} R) c) :
    IsColimit (coproductComplexCofan K) := by
  apply HomologicalComplex.isColimitOfEval
  intro q
  let e : Discrete.functor K ⋙ HomologicalComplex.eval (ModuleCat.{max u v} R) c q ≅
      Discrete.functor (fun i => (K i).X q) :=
    Discrete.natIso (fun _ => Iso.refl _)
  have h := (IsColimit.precomposeHomEquiv e _).symm
    (coproductIsCoproduct (fun i => (K i).X q))
  apply IsColimit.ofIsoColimit h
  refine Cocone.ext (Iso.refl _) ?_
  intro i
  simp [e, coproductComplexCofan, coproductComplexι, coproductComplex, familyComplex]

/-- Evaluation identifies the homology diagram with the actual component homologies. -/
def familyComplexHomologyIso (K : ι → HomologicalComplex (ModuleCat.{max u v} R) c) (q : κ) :
    (familyComplex K).homology q ≅ Discrete.functor (fun i => (K i).homology q) :=
  Discrete.natIso (fun i =>
    (((familyComplex K).sc q).mapHomologyIso ((evaluation _ _).obj i)).symm)

/-- Exactness of direct sums gives the canonical comparison on native homology. -/
def coproductComplexHomologyIso
    (K : ι → HomologicalComplex (ModuleCat.{max u v} R) c) (q : κ) :
    (coproductComplex K).homology q ≅ ∐ (fun i => (K i).homology q) :=
  ((familyComplex K).sc q).mapHomologyIso colim ≪≫
    colim.mapIso (familyComplexHomologyIso K q)

/-- On each summand the homology comparison is the original coproduct inclusion. -/
@[reassoc]
theorem coproductComplexι_homologyIso
    (K : ι → HomologicalComplex (ModuleCat.{max u v} R) c) (q : κ) (i : ι) :
    homologyMap (coproductComplexι K i) q ≫ (coproductComplexHomologyIso K q).hom =
      Sigma.ι (fun i => (K i).homology q) i := by
  change ShortComplex.homologyMap
      (((familyComplex K).sc q).mapNatTrans (colim.ι (Discrete.mk i))) ≫ _ = _
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp only [coproductComplexHomologyIso, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [← (colim.ι (Discrete.mk i)).naturality]
  simp [familyComplexHomologyIso]

/-- The comparison with the usual finitely supported direct sum of homology modules. -/
def coproductComplexHomologyLinearEquiv [DecidableEq ι]
    (K : ι → HomologicalComplex (ModuleCat.{max u v} R) c) (q : κ) :
    (coproductComplex K).homology q ≃ₗ[R] ⨁ i, (K i).homology q :=
  (coproductComplexHomologyIso K q ≪≫ coprodIsoDirectSum _).toLinearEquiv

end ModuleCat
