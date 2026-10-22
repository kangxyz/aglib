/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteType.SubalgebraColimit
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Proper
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Schemes
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Actual proper models over finite-generated coefficient subalgebras

Finite-presentation descent supplies the original model and its original
cartesian comparison. Eventual properness makes that same model proper after
one native rebase. Only the coefficient ring is required to be Noetherian in
the proper-finitely-presented statement; the target ring may be arbitrary.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.FiniteTypeSubalgebraLimit

universe u v

open Algebra.FiniteTypeSubalgebraLimit Scheme.FinitePresentationDescent

variable (D : Type v) [CommRing D] [IsNoetherianRing D]
  (R : Type u) [CommRing R] [Algebra D R]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A proper finitely presented scheme has an actual proper model over one
finite-generated coefficient subalgebra, retaining its native cartesian square. -/
theorem exists_properModel_over_finiteTypeSubalgebra [LocallyOfFinitePresentation f] :
    ∃ s : Finset R,
      ∃ M : Model (Spec.map (CommRingCat.ofHom (stage D R s).val.toRingHom)) f,
        IsProper M.f := by
  let (s : Finset R) : IsNoetherianRing (stage D R s) :=
    Algebra.FiniteType.isNoetherianRing D _
  let F := ringDiagram D R
  let E : (Finset R)ᵒᵖ ⥤ Scheme.{u} := F.op ⋙ Scheme.Spec
  let c : Cone E := Scheme.Spec.mapCone (ringCocone D R).op
  have hc : IsLimit c := isLimitOfPreserves Scheme.Spec (ringCoconeIsColimit D R).op
  have (s : (Finset R)ᵒᵖ) : IsAffine (E.obj s) :=
    inferInstanceAs (IsAffine (Spec (.of (stage D R s.unop))))
  have (s : (Finset R)ᵒᵖ) : IsLocallyNoetherian (E.obj s) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (.of (stage D R s.unop))))
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
  let : IsProper (pullback.fst (c.π.app (op s)) M.f) := by
    rw [← hi]
    infer_instance
  obtain ⟨j, hj⟩ := Scheme.exists_isProper_baseChange_of_isLimit E c hc (op s) M.f
  let := hj
  let N := M.rebase E c (op s) j
  have hN : IsProper N.f := by
    change IsProper (pullback.snd M.f (E.map j.hom))
    rw [← pullbackSymmetry_hom_comp_fst M.f (E.map j.hom)]
    infer_instance
  exact ⟨j.left.unop, N, hN⟩

/-- Over a Noetherian target, properness supplies local finite presentation,
so the same original proper-model conclusion needs no additional premise. -/
theorem exists_properModel_over_finiteTypeSubalgebra_of_noetherian [IsNoetherianRing R] :
    ∃ s : Finset R,
      ∃ M : Model (Spec.map (CommRingCat.ofHom (stage D R s).val.toRingHom)) f,
        IsProper M.f :=
  exists_properModel_over_finiteTypeSubalgebra D R f

end AlgebraicGeometry.Scheme.FiniteTypeSubalgebraLimit
