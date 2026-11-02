/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.AffineRepresentable
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.FiniteEtalePartitions
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionColimit.Bounded
public import Aglib.CategoryTheory.Limits.Types.FiniteSubset
public import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Constructible stages capturing an original finite geometric stalk

A subsheaf of a constructible abelian sheaf inherits its actual positive
annihilator. Its original bounded filtered presentation has constructible
stages on an affine base. Finiteness of the original geometric stalk selects
one stage mapping onto that stalk. Constructibility of the subsheaf is not
assumed, and no local-constancy certificate is an input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u

attribute [local instance] hasSheafifyLarge Cardinal.fact_isRegular_aleph0

/-- An original subsheaf of a constructible coefficient on an affine scheme
receives a map from an actual constructible coefficient which is epimorphic
at the specified geometric stalk. -/
theorem exists_constructible_geometricStalk_epi_of_mono
    {X : Scheme.{u}} [IsAffine X]
    {F G : AbelianSheaf.{u, u + 1} X} (f : F ⟶ G) [Mono f]
    (hG : IsConstructible G) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (η : Spec (.of Ω) ⟶ X) :
    ∃ (P : AbelianSheaf.{u, u + 1} X) (q : P ⟶ F),
      IsConstructible P ∧ Epi ((pointSmallEtale η).sheafFiber.map q) := by
  obtain ⟨n, hn, hkill⟩ := exists_positive_annihilator_of_isConstructible G hG
  have hFkill : n • 𝟙 F = 0 := by
    apply (cancel_mono f).mp
    calc
      (n • 𝟙 F) ≫ f = f ≫ (n • 𝟙 G) := by simp
      _ = 0 ≫ f := by rw [hkill, comp_zero, zero_comp]
  have hparts : ∀ U : Scheme.AffineEtale X, ∀ V : X.affineOpens,
      ∃ p : FiniteLocallyClosedPartition V.1.toScheme,
        ∀ i, IsFinite ((siteBaseChange (p.inclusion i ≫ V.1.ι)).obj
          ((Scheme.AffineEtale.Spec X).obj U)).hom := by
    intro U
    have : IsAffine ((Scheme.AffineEtale.Spec X).obj U).left :=
      inferInstanceAs (IsAffine (Spec U.left.unop))
    exact PositivePresentation.finiteEtalePartitions_of_isAffine_of_isSeparated _
  obtain ⟨I, hI, hfilt, D, ι, hc, hstage⟩ :=
    PositivePresentation.exists_filtered_presentation_constructible_of_finiteEtalePartitions
      X n (Nat.ne_of_gt hn) hparts F hFkill
  let := hI
  have : IsFiltered I := hfilt
  let T := (pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})
  let : LocallySmall.{u} X.Etale := inferInstance
  let : HasFilteredColimitsOfSize.{u, u} AddCommGrpCat.{u + 1} :=
    hasFilteredColimitsOfSize_of_univLE.{u, u, u + 1, u + 1}
  let : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
  let : PreservesFiniteLimits T := inferInstanceAs
    (PreservesFiniteLimits ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})))
  let : T.PreservesMonomorphisms := inferInstance
  have : Finite (T.obj G) := finite_geometricStalk_of_isConstructible G hG η
  have : Finite (T.obj F) := Finite.of_injective (T.map f)
    ((AddCommGrpCat.mono_iff_injective (T.map f)).mp inferInstance)
  let c : Cocone (D ⋙ BoundedPresentation.inclusion X n) := Cocone.mk F ι
  let V := T ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}
  have hcV : IsColimit (V.mapCocone c) := isColimitOfPreserves V hc.some
  classical
  have : Finite ((V.mapCocone c).pt) := inferInstanceAs (Finite (T.obj F))
  let : Fintype ((V.mapCocone c).pt) := Fintype.ofFinite _
  obtain ⟨i, hi⟩ := Types.exists_finset_subset_range_of_isColimit
    _ (V.mapCocone c) hcV Finset.univ
  refine ⟨(D.obj i).obj, ι.app i, (hstage i).2.2, ?_⟩
  apply (AddCommGrpCat.epi_iff_surjective _).mpr
  intro x
  exact hi (@Finset.mem_univ ((V.mapCocone c).pt) inferInstance x)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
