/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteType.SubalgebraColimit
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Separated
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Schemes

/-!
# Separated models over finitely generated subalgebras

An actual separated finitely presented scheme descends to a separated model
at a finite coefficient stage. Both the original structural morphism and its
native cartesian comparison are retained. Neither ring need be Noetherian.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.FiniteTypeSubalgebraLimit

universe u v

open Algebra.FiniteTypeSubalgebraLimit Scheme.FinitePresentationDescent

variable (D : Type v) [CommRing D] (R : Type u) [CommRing R] [Algebra D R]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
  [IsSeparated f] [LocallyOfFinitePresentation f] [QuasiCompact f]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A separated finitely presented scheme has an actual separated model over
one finitely generated coefficient subalgebra, with its native square. -/
theorem exists_separatedModel_over_finiteTypeSubalgebra :
    ∃ s : Finset R,
      ∃ M : Model (Spec.map (CommRingCat.ofHom (stage D R s).val.toRingHom)) f,
        IsSeparated M.f := by
  let F := ringDiagram D R
  let E : (Finset R)ᵒᵖ ⥤ Scheme.{u} := F.op ⋙ Scheme.Spec
  let c : Cone E := Scheme.Spec.mapCone (ringCocone D R).op
  have hc : IsLimit c := isLimitOfPreserves Scheme.Spec (ringCoconeIsColimit D R).op
  have (s : (Finset R)ᵒᵖ) : IsAffine (E.obj s) :=
    inferInstanceAs (IsAffine (Spec (.of (stage D R s.unop))))
  let f' : X ⟶ Spec (ringCocone D R).pt := f
  have : LocallyOfFinitePresentation f' := inferInstanceAs (LocallyOfFinitePresentation f)
  have : QuasiCompact f' := inferInstanceAs (QuasiCompact f)
  have : QuasiSeparated f' := inferInstanceAs (QuasiSeparated f)
  obtain ⟨s, Xs, fs, hfp, hqc, hqs, ⟨e⟩⟩ :=
    Scheme.exists_model_of_isColimit F (ringCocone D R) (ringCoconeIsColimit D R) f'
  let := hfp
  let := hqc
  let := hqs
  let M : Model (c.π.app (op s)) f := Model.ofOverIso fs e
  have hi : M.rawIso.inv ≫ f = pullback.fst (c.π.app (op s)) M.f :=
    (Iso.inv_comp_eq M.rawIso).mpr M.rawIso_hom_fst.symm
  let : IsSeparated (pullback.fst (c.π.app (op s)) M.f) := by
    rw [← hi]
    infer_instance
  obtain ⟨j, hj⟩ := Scheme.exists_isSeparated_baseChange_of_isLimit E c hc (op s) M.f
  let := hj
  let N := M.rebase E c (op s) j
  have hN : IsSeparated N.f := by
    change IsSeparated (pullback.snd M.f (E.map j.hom))
    rw [← pullbackSymmetry_hom_comp_fst M.f (E.map j.hom)]
    infer_instance
  exact ⟨j.left.unop, N, hN⟩

end AlgebraicGeometry.Scheme.FiniteTypeSubalgebraLimit
