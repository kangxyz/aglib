/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.GeneralRelative
public import Aglib.AlgebraicGeometry.Morphisms.IsIso.OpenLift

/-!
# Closed graphs of proper open models

Quasi-domination normalizes a compactified proper model without changing its
specified dense open. Properness of the original map forces the extended
partial domain to be precisely the original open model.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
universe u

namespace AlgebraicGeometry.Scheme.Compactification

/-- Normalize a dense open proper model by an actual admissible sequence.
The retained graph uses the original map `q`, not a replacement target map. -/
theorem exists_closedGraph_of_proper_dense_open
    {Y X S : Scheme.{u}} [IsNoetherian Y]
    (pY : Y ⟶ S) [IsSeparated pY]
    (pX : X ⟶ S) [IsSeparated pX] [QuasiCompact pX] [LocallyOfFiniteType pX]
    (V : Y.Opens) (hV : Dense (V : Set Y))
    (q : V.toScheme ⟶ X) [IsProper q]
    (hq : q ≫ pX = V.ι ≫ pY) :
    ∃ (Y' : Scheme.{u}) (β : Y' ⟶ Y) (e : V.toScheme ⟶ Y')
      (hw : e ≫ β ≫ pY = q ≫ pX),
      Blowup.AdmissibleSequence V β ∧ IsProper β ∧ IsIso (β ∣_ V) ∧
      IsOpenImmersion e ∧ DenseRange e ∧ e ≫ β = V.ι ∧
      IsClosedImmersion (pullback.lift e q hw) := by
  obtain ⟨Y', β, D, d, h, j, hw, hseq, hβ, hβV, hd, hddense, hj,
      hjd, hjh, hgraph⟩ :=
    QuasiDomination.exists_relative_quasiDomination_oneOpen pY pX V hV q hq
  let : IsProper β := hβ
  let : IsIso (β ∣_ V) := hβV
  let : IsOpenImmersion d := hd
  let : IsDominant d := ⟨hddense⟩
  let : IsSchemeTheoreticallyDominant j := hj
  let : IsClosedImmersion (pullback.lift d h hw) := hgraph
  have hjs : (j ≫ d) ≫ β = V.ι := by simpa only [Category.assoc] using hjd
  let : IsOpenImmersion (j ≫ d) := β.isOpenImmersion_of_isIso_restriction V _ hjs
  let : IsOpenImmersion j := IsOpenImmersion.of_comp j d
  let : IsSeparated (h ≫ pX) := by rw [← hw]; infer_instance
  let : IsSeparated h := IsSeparated.of_comp h pX
  let : IsProper (j ≫ h) := by rw [hjh]; infer_instance
  let : IsProper j := IsProper.of_comp j h
  let : IsIso j :=
    (isIso_iff_isOpenImmersion_and_surjective j).mpr ⟨inferInstance, inferInstance⟩
  let e := j ≫ d
  have heβ : e ≫ β = V.ι := hjs
  have hew : e ≫ β ≫ pY = q ≫ pX := by
    rw [← Category.assoc, heβ, hq]
  have hegraph : pullback.lift e q hew = j ≫ pullback.lift d h hw := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      rfl
    · simp only [Category.assoc, pullback.lift_snd]
      exact hjh.symm
  refine ⟨Y', β, e, hew, hseq, hβ, hβV, inferInstance,
    (inferInstance : IsDominant e).denseRange, heβ, ?_⟩
  rw [hegraph]
  infer_instance

end AlgebraicGeometry.Scheme.Compactification
