/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Native good-truncation maps and functor comparisons

The native term isomorphisms of good truncation retain its original inclusion
and projection maps. These equations support the canonical comparison of good
upper truncation with a zero-preserving functor preserving the boundary kernel.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (K : HomologicalComplex C c')

/-- The native lower-bound term comparison retains the original projection. -/
@[reassoc (attr := simp)]
theorem πTruncGE_f_truncGEXIsoOpcycles_hom (e : c.Embedding c') [e.IsTruncGE]
    {i : ι} {i' : ι'} (hi : e.f i = i') (hb : e.BoundaryGE i) :
    (K.πTruncGE e).f i' ≫ (K.truncGEXIsoOpcycles e hi hb).hom = K.pOpcycles i' := by
  dsimp only [πTruncGE]
  rw [e.liftExtend_f _ _ hi, K.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv e hi hb]
  simp [truncGEXIsoOpcycles]

/-- Away from the lower boundary the native term comparison is its projection. -/
@[reassoc (attr := simp)]
theorem πTruncGE_f_truncGEXIso_hom (e : c.Embedding c') [e.IsTruncGE]
    {i : ι} {i' : ι'} (hi : e.f i = i') (hb : ¬ e.BoundaryGE i) :
    (K.πTruncGE e).f i' ≫ (K.truncGEXIso e hi hb).hom = 𝟙 _ := by
  dsimp only [πTruncGE]
  rw [e.liftExtend_f _ _ hi, K.restrictionToTruncGE'_f_eq_iso_hom_iso_inv e hi hb]
  simp [truncGEXIso]

/-- The native upper-bound cycle comparison retains the original inclusion. -/
@[reassoc (attr := simp)]
theorem truncLEXIsoCycles_hom_iCycles (e : c.Embedding c') [e.IsTruncLE]
    {i : ι} {i' : ι'} (hi : e.f i = i') (hb : e.BoundaryLE i) :
    (K.truncLEXIsoCycles e hi hb).hom ≫ K.iCycles i' = (K.ιTruncLE e).f i' := by
  have hπ := K.op.πTruncGE_f_truncGEXIsoOpcycles_hom e.op hi (by simpa using hb)
  have hp : K.op.pOpcycles i' ≫ (K.opcyclesOpIso i').hom = (K.iCycles i').op :=
    (K.sc i').op_pOpcycles_opcyclesOpIso_hom
  apply Quiver.Hom.op_inj
  change (K.iCycles i').op ≫ (K.opcyclesOpIso i').inv ≫
      (K.op.truncGEXIsoOpcycles e.op hi (by simpa using hb)).inv = (K.op.πTruncGE e.op).f i'
  rw [← hp, Category.assoc, Iso.hom_inv_id_assoc, ← hπ, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- Away from the upper boundary the native term comparison is its inclusion. -/
@[reassoc (attr := simp)]
theorem truncLEXIso_hom_eq_ιTruncLE_f (e : c.Embedding c') [e.IsTruncLE]
    {i : ι} {i' : ι'} (hi : e.f i = i') (hb : ¬ e.BoundaryLE i) :
    (K.truncLEXIso e hi hb).hom = (K.ιTruncLE e).f i' := by
  have hπ := K.op.πTruncGE_f_truncGEXIso_hom e.op hi (by simpa using hb)
  apply Quiver.Hom.op_inj
  change (K.op.truncGEXIso e.op hi (by simpa using hb)).inv = (K.op.πTruncGE e.op).f i'
  apply (cancel_mono (K.op.truncGEXIso e.op hi (by simpa using hb)).hom).mp
  rw [Iso.inv_hom_id, hπ]

end HomologicalComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] (K : CochainComplex C ℤ)

/-- The native integer-indexed upper term comparison is its original inclusion. -/
@[reassoc (attr := simp)]
theorem truncLEXIso_hom_eq_ιTruncLE_f (b q : ℤ) (hq : q < b) :
    (K.truncLEXIso b q hq).hom = (K.ιTruncLE b).f q := by
  dsimp only [truncLEXIso]
  apply HomologicalComplex.truncLEXIso_hom_eq_ιTruncLE_f

/-- The native integer-indexed boundary-cycle comparison keeps its original inclusion. -/
@[reassoc (attr := simp)]
theorem truncLEXIsoCycles_hom_iCycles (b : ℤ) :
    (K.truncLEXIsoCycles b).hom ≫ K.iCycles b = (K.ιTruncLE b).f b := by
  dsimp only [truncLEXIsoCycles]
  apply HomologicalComplex.truncLEXIsoCycles_hom_iCycles

section Functor

variable {D : Type*} [Category* D] [Abelian D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms] (b : ℤ)
  [PreservesLimit (parallelPair (K.d b (b + 1)) 0) F]

/-- The native cycle comparison obtained from preservation of the actual
boundary kernel alone, without any homology-preservation assumption. -/
def mapCyclesIsoOfPreservesKernel :
    F.obj (K.cycles b) ≅ ((F.mapHomologicalComplex (.up ℤ)).obj K).cycles b :=
  (KernelFork.mapIsLimit _ (K.cyclesIsKernel b (b + 1) (by simp)) F).conePointUniqueUpToIso
    (((F.mapHomologicalComplex (.up ℤ)).obj K).cyclesIsKernel b (b + 1) (by simp))

/-- The boundary kernel comparison retains the original cycle inclusions. -/
@[reassoc (attr := simp)]
theorem mapCyclesIsoOfPreservesKernel_hom_iCycles :
    (K.mapCyclesIsoOfPreservesKernel F b).hom ≫
        ((F.mapHomologicalComplex (.up ℤ)).obj K).iCycles b = F.map (K.iCycles b) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

/-- The original term isomorphisms comparing mapped upper truncation with
upper truncation after mapping. At the boundary this is the native kernel
comparison; outside the support both objects are the original zero objects. -/
def mapTruncLEXIso (q : ℤ) :
    ((F.mapHomologicalComplex (.up ℤ)).obj (K.truncLE b)).X q ≅
      (CochainComplex.truncLE ((F.mapHomologicalComplex (.up ℤ)).obj K) b).X q := by
  classical
  exact if hq : q < b then
    F.mapIso (K.truncLEXIso b q hq) ≪≫
      (CochainComplex.truncLEXIso ((F.mapHomologicalComplex (.up ℤ)).obj K) b q hq).symm
  else if hq : q = b then by
    subst q
    exact F.mapIso (K.truncLEXIsoCycles b) ≪≫ K.mapCyclesIsoOfPreservesKernel F b ≪≫
      (CochainComplex.truncLEXIsoCycles ((F.mapHomologicalComplex (.up ℤ)).obj K) b).symm
  else
    (F.map_isZero ((K.truncLE b).isZero_of_isStrictlyLE b q (by omega))).iso
      ((CochainComplex.truncLE ((F.mapHomologicalComplex (.up ℤ)).obj K) b).isZero_of_isStrictlyLE
        b q (by omega))

/-- Each original comparison component commutes with the actual truncation inclusion. -/
@[reassoc]
theorem mapTruncLEXIso_hom_ιTruncLE_f (q : ℤ) :
    (K.mapTruncLEXIso F b q).hom ≫
        (CochainComplex.ιTruncLE ((F.mapHomologicalComplex (.up ℤ)).obj K) b).f q =
      F.map ((K.ιTruncLE b).f q) := by
  classical
  by_cases hq : q < b
  · simp only [mapTruncLEXIso, dite_eq_left hq, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom]
    rw [← truncLEXIso_hom_eq_ιTruncLE_f _ b q hq, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, K.truncLEXIso_hom_eq_ιTruncLE_f]
  · by_cases hqb : q = b
    · subst q
      dsimp only [mapTruncLEXIso]
      rw [dite_eq_right (lt_irrefl b), dite_eq_left (rfl : b = b)]
      rw [← truncLEXIsoCycles_hom_iCycles _ b]
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
        Category.assoc, Iso.inv_hom_id_assoc,
        mapCyclesIsoOfPreservesKernel_hom_iCycles]
      rw [← F.map_comp, truncLEXIsoCycles_hom_iCycles]
    · exact (F.map_isZero ((K.truncLE b).isZero_of_isStrictlyLE b q (by omega))).eq_of_src _ _

/-- A zero-preserving functor preserving the original boundary kernel
commutes with the native good upper truncation. -/
def mapTruncLEIso :
    (F.mapHomologicalComplex (.up ℤ)).obj (K.truncLE b) ≅
      CochainComplex.truncLE ((F.mapHomologicalComplex (.up ℤ)).obj K) b := by
  refine HomologicalComplex.Hom.isoOfComponents (K.mapTruncLEXIso F b) ?_
  intro i j hij
  let m := CochainComplex.ιTruncLE ((F.mapHomologicalComplex (.up ℤ)).obj K) b
  let g := (F.mapHomologicalComplex (.up ℤ)).map (K.ιTruncLE b)
  let : Mono (m.f j) := by
    change Mono ((HomologicalComplex.ιTruncLE ((F.mapHomologicalComplex (.up ℤ)).obj K)
      (ComplexShape.embeddingUpIntLE b)).f j)
    infer_instance
  apply (cancel_mono (m.f j)).mp
  rw [Category.assoc, Category.assoc]
  calc
    (K.mapTruncLEXIso F b i).hom ≫
          (CochainComplex.truncLE ((F.mapHomologicalComplex (.up ℤ)).obj K) b).d i j ≫ m.f j =
        (K.mapTruncLEXIso F b i).hom ≫ m.f i ≫
          ((F.mapHomologicalComplex (.up ℤ)).obj K).d i j := by rw [← m.comm]
    _ = g.f i ≫ ((F.mapHomologicalComplex (.up ℤ)).obj K).d i j := by
      rw [← Category.assoc, K.mapTruncLEXIso_hom_ιTruncLE_f]
      rfl
    _ = ((F.mapHomologicalComplex (.up ℤ)).obj (K.truncLE b)).d i j ≫ g.f j := g.comm i j
    _ = ((F.mapHomologicalComplex (.up ℤ)).obj (K.truncLE b)).d i j ≫
        (K.mapTruncLEXIso F b j).hom ≫ m.f j := by
      rw [K.mapTruncLEXIso_hom_ιTruncLE_f]
      rfl

/-- The actual comparison retains the original mapped truncation inclusion. -/
@[reassoc (attr := simp)]
theorem mapTruncLEIso_hom_ιTruncLE :
    (K.mapTruncLEIso F b).hom ≫
        CochainComplex.ιTruncLE ((F.mapHomologicalComplex (.up ℤ)).obj K) b =
      (F.mapHomologicalComplex (.up ℤ)).map (K.ιTruncLE b) := by
  ext q
  exact K.mapTruncLEXIso_hom_ιTruncLE_f F b q

/-- The actual truncation comparison is natural in coefficient chain maps
whenever the two original boundary kernels are preserved. -/
@[reassoc]
theorem mapTruncLEIso_hom_naturality {L : CochainComplex C ℤ} (φ : K ⟶ L)
    [PreservesLimit (parallelPair (L.d b (b + 1)) 0) F] :
    (F.mapHomologicalComplex (.up ℤ)).map (CochainComplex.truncLEMap φ b) ≫
        (L.mapTruncLEIso F b).hom =
      (K.mapTruncLEIso F b).hom ≫
        CochainComplex.truncLEMap ((F.mapHomologicalComplex (.up ℤ)).map φ) b := by
  let m := CochainComplex.ιTruncLE ((F.mapHomologicalComplex (.up ℤ)).obj L) b
  let : Mono m := by
    change Mono (HomologicalComplex.ιTruncLE ((F.mapHomologicalComplex (.up ℤ)).obj L)
      (ComplexShape.embeddingUpIntLE b))
    infer_instance
  apply (cancel_mono m).mp
  calc
    ((F.mapHomologicalComplex (.up ℤ)).map (CochainComplex.truncLEMap φ b) ≫
        (L.mapTruncLEIso F b).hom) ≫ m =
      (F.mapHomologicalComplex (.up ℤ)).map (CochainComplex.truncLEMap φ b ≫ L.ιTruncLE b) := by
        rw [Category.assoc, L.mapTruncLEIso_hom_ιTruncLE, ← Functor.map_comp]
    _ = (F.mapHomologicalComplex (.up ℤ)).map (K.ιTruncLE b ≫ φ) := by
      rw [CochainComplex.ιTruncLE_naturality]
    _ = (F.mapHomologicalComplex (.up ℤ)).map (K.ιTruncLE b) ≫
        (F.mapHomologicalComplex (.up ℤ)).map φ := Functor.map_comp _ _ _
    _ = ((K.mapTruncLEIso F b).hom ≫
        CochainComplex.truncLEMap ((F.mapHomologicalComplex (.up ℤ)).map φ) b) ≫ m := by
      rw [Category.assoc, CochainComplex.ιTruncLE_naturality, ← Category.assoc,
        K.mapTruncLEIso_hom_ιTruncLE]

/-- The original mapped inclusion is a quasi-isomorphism when the actual
mapped complex has the displayed upper cohomological bound. -/
theorem quasiIso_map_ιTruncLE_of_isLE
    [CochainComplex.IsLE ((F.mapHomologicalComplex (.up ℤ)).obj K) b] :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map (K.ιTruncLE b)) := by
  rw [← K.mapTruncLEIso_hom_ιTruncLE F b]
  infer_instance

end Functor

end CochainComplex
