/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteType.SubalgebraColimit
public import Aglib.RingTheory.Localization.FiniteSubalgebra
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Gluing

/-! # Spreading actual generic over-isomorphisms to principal localizations

Only finite-presentation scheme geometry is spread here. There is no assertion
about spreading an arbitrary etale sheaf isomorphism. The resulting over-isomorphism
need not have the prescribed generic comparison; its original structural triangles
are retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Algebra.FiniteTypeSubalgebraLimit

namespace AlgebraicGeometry.Scheme.FinitePresentationDescent

universe u

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An actual generic over-isomorphism of finitely presented, quasi-compact and
quasi-separated covers spreads to an actual nonzero principal localization.
No Noetherian hypothesis on the domain is needed. -/
theorem exists_iso_over_principalLocalization_of_generic_iso
    (R K : Type u) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of R)) (g : Y ⟶ Spec (.of R))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj (Over.mk f) ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj (Over.mk g)) :
    ∃ r : R, r ≠ 0 ∧ Nonempty
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))).obj
          (Over.mk f) ≅
       (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))).obj
          (Over.mk g)) := by
  let F := ringDiagram R K
  let D : (Finset K)ᵒᵖ ⥤ Scheme.{u} := F.op ⋙ Scheme.Spec
  let c : Cone D := Scheme.Spec.mapCone (ringCocone R K).op
  have hc : IsLimit c := isLimitOfPreserves Scheme.Spec (ringCoconeIsColimit R K).op
  have (s : (Finset K)ᵒᵖ) : IsAffine (D.obj s) :=
    inferInstanceAs (IsAffine (Spec (.of (stage R K s.unop))))
  have {s t : (Finset K)ᵒᵖ} (q : s ⟶ t) : IsAffineHom (D.map q) := inferInstance
  let i₀ : (Finset K)ᵒᵖ := op ∅
  let b₀ : D.obj i₀ ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R (stage R K ∅)))
  let η := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have h₀ : c.π.app i₀ ≫ b₀ = η := by
    change Spec.map (CommRingCat.ofHom (stage R K ∅).val.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (stage R K ∅))) = η
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (stage R K ∅).val.comp_algebraMap)
  let P := (Over.pullback b₀).obj (Over.mk f)
  let Q := (Over.pullback b₀).obj (Over.mk g)
  have : LocallyOfFinitePresentation P.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd f b₀))
  have : QuasiCompact P.hom := inferInstanceAs (QuasiCompact (pullback.snd f b₀))
  have : QuasiSeparated P.hom := inferInstanceAs (QuasiSeparated (pullback.snd f b₀))
  have : LocallyOfFinitePresentation Q.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd g b₀))
  have : QuasiCompact Q.hom := inferInstanceAs (QuasiCompact (pullback.snd g b₀))
  have : QuasiSeparated Q.hom := inferInstanceAs (QuasiSeparated (pullback.snd g b₀))
  let e₀ (Z : Over (Spec (.of R))) :
      (Over.pullback (c.π.app i₀)).obj ((Over.pullback b₀).obj Z) ≅
        (Over.pullback η).obj Z :=
    ((Over.pullbackComp (c.π.app i₀) b₀).app Z).symm ≪≫
      eqToIso (congrArg (fun h => (Over.pullback h).obj Z) h₀)
  have ep : (Over.pullback (c.π.app i₀)).obj (Over.mk P.hom) ≅
      (Over.pullback (c.π.app i₀)).obj (Over.mk Q.hom) :=
    e₀ (Over.mk f) ≪≫ e ≪≫ (e₀ (Over.mk g)).symm
  obtain ⟨j, ⟨ej⟩⟩ := exists_iso_between_baseChanges_of_isLimit D c hc i₀ P.hom Q.hom ep
  obtain ⟨r, hr, v, i, hv, hi⟩ :=
    IsFractionRing.exists_principal_localization_of_fg_subalgebra R K
      (stage R K j.left.unop) ⟨j.left.unop, rfl⟩
  let a := Spec.map (CommRingCat.ofHom i.toRingHom)
  let τ := D.map j.hom
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
  have hρ : a ≫ τ ≫ b₀ = ρ := by
    change Spec.map (CommRingCat.ofHom i.toRingHom) ≫
      Spec.map (F.map j.hom.unop) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (stage R K ∅))) = ρ
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext x
    exact i.commutes x
  let ecomp (Z : Over (Spec (.of R))) : (Over.pullback ρ).obj Z ≅
      (Over.pullback a).obj ((Over.pullback τ).obj ((Over.pullback b₀).obj Z)) :=
    eqToIso (congrArg (fun h => (Over.pullback h).obj Z) hρ.symm) ≪≫
      (Over.pullbackComp a (τ ≫ b₀)).app Z ≪≫
      (Over.pullback a).mapIso ((Over.pullbackComp τ b₀).app Z)
  exact ⟨r, hr, ⟨ecomp (Over.mk f) ≪≫ (Over.pullback a).mapIso ej ≪≫
    (ecomp (Over.mk g)).symm⟩⟩

end AlgebraicGeometry.Scheme.FinitePresentationDescent
