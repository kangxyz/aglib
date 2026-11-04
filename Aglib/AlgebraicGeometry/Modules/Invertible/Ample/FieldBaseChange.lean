/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve.Generation.VeryAmple
public import Aglib.AlgebraicGeometry.Modules.Invertible.Affine
public import Aglib.AlgebraicGeometry.Modules.Invertible.Ample.FiniteMorphism
public import Aglib.AlgebraicGeometry.Modules.Invertible.Ample.Generation
public import Aglib.AlgebraicGeometry.Modules.Invertible.Ample.Power
public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonvanishing.Generation
public import Aglib.AlgebraicGeometry.Morphisms.Finite.SurjectiveBaseChange
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.Nonvanishing
public import Aglib.CategoryTheory.Comma.Over.PullbackMap

/-! Ampleness of the original bundle descends along extensions of fields. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Scheme.Modules Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- On a proper field scheme, ampleness of the original pullback implies
ampleness of the original line bundle. The proof descends generation of
one positive power and finiteness of the projective map of those sections. -/
theorem LineBundle.IsAmple.of_fieldBaseChange {k : Type u} [Field k]
    (X : FScheme k) [IsProper X.hom] (L : LineBundle X.left)
    (K : Type u) [Field K] [Algebra k K]
    (hL : (pullbackLineBundle (pullback.fst X.hom (Spec.algebraMap k K)) L).IsAmple) :
    L.IsAmple := by
  let b := Spec.algebraMap k K
  let p := pullback.fst X.hom b
  let q := pullback.snd X.hom b
  let Y := Limits.pullback X.hom b
  let LK := pullbackLineBundle p L
  let : IsProper q := inferInstanceAs (IsProper (pullback.snd X.hom b))
  let : Y.IsSeparated := ⟨by
    rw [← terminal.comp_from q]
    infer_instance⟩
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : Surjective b := ⟨Function.surjective_to_subsingleton b⟩
  let hsurj : Surjective p := inferInstanceAs (Surjective (pullback.fst X.hom b))
  let : Flat p := inferInstanceAs (Flat (pullback.fst X.hom b))
  obtain ⟨n, hn, hcover⟩ := hL.exists_tensorPower_nonvanishing_cover
  let M := tensorPowerLineBundle X.left L n
  let MK := pullbackLineBundle p M
  let N := tensorPowerLineBundle Y LK n
  have hc : classOf Y MK = classOf Y N := classOf_pullback_tensorPower p L n
  obtain ⟨e⟩ := (class_eq_iff Y MK N).mp hc
  have hM : MK.IsAmple := (hL.tensorPower n hn).of_classOf_eq hc.symm
  let : Epi (globalSectionsEval MK.val) :=
    epi_globalSectionsEval_of_nonvanishing_cover MK (fun x => by
      obtain ⟨s, _, hx⟩ := hcover x
      refine ⟨e.inv.val.app (op ⊤) s, ?_⟩
      have h := nonvanishingOpen_iso N MK e.symm s
      exact h.symm ▸ hx)
  let : Epi (globalSectionsEval ((Scheme.Modules.pullback p).obj M.val)) :=
    inferInstanceAs (Epi (globalSectionsEval MK.val))
  let : M.val.IsQuasicoherent := lineBundle_isQuasicoherent M
  let : Epi (globalSectionsEval M.val) := globalSectionsEval_epi_of_flat_baseChange
    p hsurj.surj q X.hom (algebraMap k K)
    (IsPullback.of_hasPullback X.hom b) (RingHom.Flat.of_isField (Field.toIsField k) _) M.val
  obtain ⟨I, hI, f, hf, ⟨eO⟩⟩ :=
    ProjectiveSpace.FromSections.exists_projectiveMap_of_nonvanishing_cover
      X.hom M (fun s => s) (nonvanishing_cover_of_epi_globalSectionsEval M)
  let := hI
  let P : FScheme k := Over.mk (ProjectiveSpace.toSpec k I)
  let f' : X ⟶ P := Over.homMk f hf
  let O := ProjectiveSpace.twistingLineBundle k I 1
  let g := ((Over.pullback b).map f').left
  let r := pullback.fst P.hom b
  let H : IsPullback p g f r := Over.isPullback_map_left b f'
  let : IsProper (f ≫ P.hom) := hf.symm ▸ inferInstanceAs (IsProper X.hom)
  let : IsSeparated P.hom := inferInstanceAs (IsSeparated (ProjectiveSpace.toSpec k I))
  let : IsProper f := IsProper.of_comp f P.hom
  let : IsProper g := MorphismProperty.of_isPullback H (show IsProper f by infer_instance)
  let : Surjective r := inferInstanceAs (Surjective (pullback.fst P.hom b))
  have hO : pullbackClass f (classOf P.left O) = classOf X.left M :=
    (class_eq_iff X.left _ _).mpr ⟨eO⟩
  have hclass : classOf Y (pullbackLineBundle g (pullbackLineBundle r O)) =
      classOf Y MK := by
    change pullbackClass g (pullbackClass r (classOf P.left O)) =
      pullbackClass p (classOf X.left M)
    rw [← pullbackClass_comp, ← H.w, pullbackClass_comp, hO]
  let : IsFinite g := LineBundle.isFinite_of_isProper_of_isAmple_pullback g
    (pullbackLineBundle r O) (hM.of_classOf_eq hclass.symm)
  let : IsFinite f := Scheme.isFinite_of_isProper_of_isPullback H
  exact LineBundle.IsAmple.of_tensorPower L n hn
    (ProjectiveSpace.FromSections.isAmple_of_isFinite_projectiveMap M f eO)

end AlgebraicGeometry.Scheme.Modules.Invertible
