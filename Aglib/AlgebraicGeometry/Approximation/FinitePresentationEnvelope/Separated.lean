/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Approximation.ClosedSubscheme.FiniteType
public import Aglib.AlgebraicGeometry.Limits.Separated

/-!
# Separated finite-presentation envelopes from actual closed envelopes

For a separated original morphism, an actual finitely presented closed envelope can be made
separated. The construction applies finite-type ideal approximation to its original kernel,
then eventual separatedness to the resulting actual closed-transition inverse limit.
The original source and its structural triangle are retained.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry.Approximation.ClosedSubscheme

universe u

namespace AlgebraicGeometry.Scheme

/-- An actual closed finite-presentation envelope over an affine base can be made separated
when the original structural morphism is separated. -/
theorem exists_separated_finitePresentation_envelope_of_closed
    {X Y S : Scheme.{u}} [IsAffine S]
    (f : X ⟶ S) [IsSeparated f] (g : Y ⟶ S)
    [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g]
    (i : X ⟶ Y) [IsClosedImmersion i] (hcomm : i ≫ g = f) :
    ∃ (Z : Scheme.{u}) (h : Z ⟶ S) (j : X ⟶ Z),
      IsClosedImmersion j ∧ LocallyOfFinitePresentation h ∧
      QuasiCompact h ∧ IsSeparated h ∧ j ≫ h = f := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated g
  let D := finitePresentationDiagram i
  let c := finitePresentationCone i
  let E := D ⋙ Over.map g
  let d : Cone E := (Over.map g).mapCone c
  have hd : IsLimit ((Over.forget S).mapCone d) :=
    isLimitFinitePresentationSchemeCone i
  have {j k : FinitePresentationIndex i} (q : j ⟶ k) :
      IsClosedImmersion (E.map q).left :=
    inferInstanceAs (IsClosedImmersion (D.map q).left)
  have {j k : FinitePresentationIndex i} (q : j ⟶ k) :
      IsAffineHom (E.map q).left := inferInstance
  have {j k : FinitePresentationIndex i} (q : j ⟶ k) :
      Mono (E.map q).left := inferInstance
  have (j : FinitePresentationIndex i) : CompactSpace (E.obj j).left :=
    QuasiCompact.compactSpace_of_compactSpace (D.obj j).hom
  have (j : FinitePresentationIndex i) : QuasiSeparatedSpace (E.obj j).left :=
    quasiSeparatedSpace_of_quasiSeparated (D.obj j).hom
  have : IsSeparated d.pt.hom := by
    change IsSeparated (i ≫ g)
    rw [hcomm]
    infer_instance
  obtain ⟨j, hj⟩ := exists_isSeparated_over_of_isLimit_of_mono E d hd
  let a : X ⟶ (D.obj j).left := ((finitePresentationCone i).π.app j).left
  have ha : IsClosedImmersion a := finitePresentationCone_projection_closed i j
  have hw : a ≫ (D.obj j).hom = i := (c.π.app j).w
  refine ⟨(D.obj j).left, (D.obj j).hom ≫ g, a,
    ha, inferInstance, inferInstance, hj, ?_⟩
  exact (Category.assoc a (D.obj j).hom g).symm.trans
    ((congrArg (fun t => t ≫ g) hw).trans hcomm)

end AlgebraicGeometry.Scheme
