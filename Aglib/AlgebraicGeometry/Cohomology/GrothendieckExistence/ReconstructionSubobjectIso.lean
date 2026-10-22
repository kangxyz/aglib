/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.OpenCoverExt
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness

/-! # Gluing original isomorphisms of reconstruction subobjects

Original local inclusions in one arbitrary ambient module force overlap
compatibility by monicity. No quasicoherence of the ambient is required.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u v
variable {X : Scheme.{u}} {ι : Type v} (Y : ι → Scheme.{u})
  (p : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (p i)]
  (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), p i y = x)
  {M N P : X.Modules} (s : M ⟶ P) (t : N ⟶ P) [Mono t]
  (e : ∀ i, M.restrict (p i) ≅ N.restrict (p i))
  (he : ∀ i, (restrictFunctor (p i)).map s =
    (e i).hom ≫ (restrictFunctor (p i)).map t)

include he in
/-- Original inclusions force the genuine native overlap equation. -/
theorem reconstructionSubobjectIso_compatible :
    InternalHom.RestrictionHomCompatible p M N (fun i => (e i).hom) := by
  intro i j
  let R := restrictFunctor (pullback.fst (p i) (p j))
  let S := restrictFunctor (pullback.snd (p i) (p j))
  let E := overlapRestrictIso (p i) (p j)
  apply (cancel_mono (S.map ((restrictFunctor (p j)).map t))).mp
  change (R.map (e i).hom ≫ E.hom.app N) ≫ S.map ((restrictFunctor (p j)).map t) =
    (E.hom.app M ≫ S.map (e j).hom) ≫ S.map ((restrictFunctor (p j)).map t)
  have hn : R.map ((restrictFunctor (p i)).map t) ≫ E.hom.app P =
      E.hom.app N ≫ S.map ((restrictFunctor (p j)).map t) := E.hom.naturality t
  calc
    _ = R.map ((e i).hom ≫ (restrictFunctor (p i)).map t) ≫ E.hom.app P := by
      rw [Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp]
    _ = R.map ((restrictFunctor (p i)).map s) ≫ E.hom.app P := by rw [← he i]
    _ = E.hom.app M ≫ S.map ((restrictFunctor (p j)).map s) := E.hom.naturality s
    _ = _ := by rw [he j, Functor.map_comp, Category.assoc]

/-- Actual original local subobject isomorphisms glue to an actual global
isomorphism preserving the same ambient inclusion. -/
def reconstructionSubobjectIsoOfOpenCover :
    {c : M ≅ N // s = c.hom ≫ t} := by
  let f := InternalHom.glueRestrictionHom Y p hcover M N (fun i => (e i).hom)
    (reconstructionSubobjectIso_compatible Y p s t e he)
  have hf (i : ι) : (restrictFunctor (p i)).map f = (e i).hom :=
    InternalHom.glueRestrictionHom_restrict Y p hcover M N (fun i => (e i).hom)
      (reconstructionSubobjectIso_compatible Y p s t e he) i
  have hi : IsIso f := isIso_of_restrict_openCover Y p hcover f (fun i => by
    rw [hf i]
    infer_instance)
  letI := hi
  refine ⟨asIso f, ?_⟩
  apply InternalHom.hom_ext_of_openCover Y p hcover
  intro i
  rw [Functor.map_comp, asIso_hom, hf i]
  exact he i

end AlgebraicGeometry.Scheme.Modules.Coherent
