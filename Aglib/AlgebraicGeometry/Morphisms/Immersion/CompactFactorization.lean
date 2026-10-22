/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Compact-open trimming of an immersion factorization

An immersion with quasi-compact source becomes a closed immersion into a
compact open contained in its canonical coborder. Trimming a supplied
finite-presentation factorization this way preserves its structure morphism
and its original source. No finite generation of a closure ideal is asserted.
-/

@[expose] public noncomputable section

universe u
open CategoryTheory Topology

namespace AlgebraicGeometry.Scheme.Hom

/-- Trim an immersion with compact source to a compact open in its coborder,
retaining the literal original morphism after the open inclusion. -/
theorem exists_compactOpen_closed_lift {X Y : Scheme.{u}}
    (e : X ⟶ Y) [IsImmersion e] [CompactSpace X] :
    ∃ W : Y.Opens, IsCompact (W : Set Y) ∧ Set.range e ⊆ W ∧
      W ≤ e.coborderRange ∧ ∃ eW : X ⟶ W,
        eW ≫ W.ι = e ∧ IsClosedImmersion eW := by
  have hEc : IsCompact (Set.range e) := isCompact_range e.continuous
  have hEU : Set.range e ⊆ e.coborderRange := by
    change Set.range e ⊆ coborder (Set.range e)
    exact subset_coborder
  obtain ⟨V, hVc, hVo, hEV, hVU⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between hEc e.coborderRange.isOpen hEU
  let W : Y.Opens := ⟨V, hVo⟩
  have hW : Set.range e ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    exact hEV
  let eW : X ⟶ W := IsOpenImmersion.lift W.ι e hW
  have heW : eW ≫ W.ι = e := IsOpenImmersion.lift_fac _ _ _
  have hWU : W ≤ e.coborderRange := hVU
  have hcomp : eW ≫ Y.homOfLE hWU = e.liftCoborder := by
    apply (cancel_mono e.coborderRange.ι).1
    rw [Category.assoc, Scheme.homOfLE_ι, heW, e.liftCoborder_ι]
  have : IsClosedImmersion (eW ≫ Y.homOfLE hWU) := by
    rw [hcomp]
    infer_instance
  have : IsClosedImmersion eW := IsClosedImmersion.of_comp eW (Y.homOfLE hWU)
  exact ⟨W, hVc, hEV, hWU, eW, heW, inferInstance⟩

/-- Trim an actual immersion factorization through a finitely presented
morphism to a closed immersion into a qcqs compact open. -/
theorem exists_compactOpen_closed_factorization {X Y S : Scheme.{u}}
    (e : X ⟶ Y) (g : Y ⟶ S) (f : X ⟶ S) (hef : e ≫ g = f)
    [IsImmersion e] [CompactSpace X] [QuasiSeparatedSpace S]
    [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g] :
    ∃ W : Y.Opens, IsCompact (W : Set Y) ∧ Set.range e ⊆ W ∧
      W ≤ e.coborderRange ∧ QuasiSeparatedSpace W ∧ QuasiCompact W.ι ∧
      LocallyOfFinitePresentation (W.ι ≫ g) ∧ QuasiCompact (W.ι ≫ g) ∧
      QuasiSeparated (W.ι ≫ g) ∧ ∃ eW : X ⟶ W,
        IsClosedImmersion eW ∧ eW ≫ W.ι = e ∧ eW ≫ W.ι ≫ g = f := by
  obtain ⟨W, hWc, hEW, hWU, eW, heW, hclosed⟩ := e.exists_compactOpen_closed_lift
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated g
  have : CompactSpace W := isCompact_iff_compactSpace.mp hWc
  have : QuasiSeparatedSpace W := quasiSeparatedSpace_of_quasiSeparated W.ι
  have : QuasiCompact W.ι := inferInstance
  refine ⟨W, hWc, hEW, hWU, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, eW, hclosed, heW, ?_⟩
  rw [← Category.assoc, heW, hef]

end AlgebraicGeometry.Scheme.Hom
