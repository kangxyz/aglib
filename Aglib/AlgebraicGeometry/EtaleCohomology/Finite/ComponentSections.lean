/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.StrictlyLocal.Standard

/-! # Exact sections at strictly local objects of an ambient small etale site -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u

variable {X : Scheme.{u}} (B : Type u) [CommRing B] [HenselianLocalRing B]
  [IsSepClosed (IsLocalRing.ResidueField B)] (p : Spec (.of B) ⟶ X) [Etale p]

/-- A strictly local etale object in an arbitrary ambient small etale site has
no proper covering sieve. The object need not be terminal in that site. -/
theorem component_covering_sieve_eq_top
    (W : Sieve (Scheme.Etale.mk p))
    (hW : W ∈ X.smallEtaleTopology (Scheme.Etale.mk p)) : W = ⊤ := by
  let : Scheme.IsJointlySurjectivePreserving
      (fun {U V : Scheme.{u}} (f : U ⟶ V) => Etale f) :=
    Scheme.isJointlySurjectivePreserving _
  obtain ⟨𝒰, hOver, hEtale, hle⟩ :=
    (Scheme.mem_smallGrothendieckTopology (Scheme.Etale.mk p) W).mp hW
  let : 𝒰.Over X := hOver
  let (i : 𝒰.I₀) : (𝒰.X i).Over X := Scheme.Cover.Over.over (𝒰 := 𝒰) i
  let (i : 𝒰.I₀) : (𝒰.f i).IsOver X := Scheme.Cover.Over.isOver_map (𝒰 := 𝒰) i
  let : Scheme.JointlySurjective
      (Scheme.precoverage (fun {U V : Scheme.{u}} (f : U ⟶ V) => Etale f)) :=
    Scheme.instJointlySurjectivePrecoverage
  obtain ⟨i, σ, hσ⟩ := @StrictlyLocal.exists_section_of_etale_family
    B _ _ _ 𝒰.I₀ 𝒰.X 𝒰.f (fun i => 𝒰.map_prop i) (fun x => 𝒰.exists_eq x)
  have hstruct : 𝒰.f i ≫ p = (𝒰.X i ↘ X) :=
    HomIsOver.comp_over (f := 𝒰.f i) (S := X)
  let V : X.Etale := (𝒰.X i).asOverProp X (hEtale i)
  let f : V ⟶ Scheme.Etale.mk p := (𝒰.f i).asOverProp X
  let s : Scheme.Etale.mk p ⟶ V := MorphismProperty.Over.homMk σ (by
    change σ ≫ (𝒰.X i ↘ X) = p
    exact (congrArg (fun k : 𝒰.X i ⟶ X => σ ≫ k) hstruct.symm).trans
      ((Category.assoc σ (𝒰.f i) p).symm.trans
        ((congrArg (fun k : Spec (.of B) ⟶ Spec (.of B) => k ≫ p) hσ).trans
          (Category.id_comp p))))
  have hf : W f := hle V f (Presieve.ofArrows.mk (C := X.Etale) i)
  have hsf : s ≫ f = 𝟙 (Scheme.Etale.mk p) := by
    apply MorphismProperty.Over.Hom.ext
    exact hσ
  apply Sieve.id_mem_iff_eq_top.mp
  exact hsf ▸ W.downward_closed hf s

/-- Evaluation at the actual strictly local component preserves epimorphisms
of arbitrary abelian sheaves in the original ambient small etale site. -/
theorem componentSections_preservesEpimorphisms
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}] :
    ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op (Scheme.Etale.mk p))).PreservesEpimorphisms :=
  CategoryTheory.SheafCohomology.SplitTerminal.sections_preservesEpimorphisms _ _
    (component_covering_sieve_eq_top B p)

/-- Sections at the actual strictly local component are exact. This statement
uses the original ambient-site evaluation, not a replacement coefficient. -/
theorem componentSections_preservesFiniteColimits
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}] :
    PreservesFiniteColimits
      ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op (Scheme.Etale.mk p))) := by
  let Γ := (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (op (Scheme.Etale.mk p))
  have : PreservesFiniteLimits Γ := preservesFiniteLimits_of_natIso
    (sheafSectionsNatIsoEvaluation X.smallEtaleTopology AddCommGrpCat.{u + 1}).symm
  let : Γ.PreservesEpimorphisms := componentSections_preservesEpimorphisms B p
  let : Γ.Additive := { map_add := by intros; rfl }
  let : Γ.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels Γ
  exact Functor.preservesFiniteColimits_of_preservesHomology Γ

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
