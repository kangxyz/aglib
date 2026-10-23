/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FinitePresentation
public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Sheaf
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.Restriction
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Presentable.StrongGenerator

/-! # Actual filtered presentations of bounded coefficients

The full subcategory of actual abelian sheaves killed by a fixed integer is
closed under original coefficient colimits. The original free mod-n
representables on affine etale objects form compact strong generators: their
maps are the original sections, and the native affine restriction equivalence
detects equality and isomorphisms.

The proved categorical finite-colimit-closure construction then supplies an
actual filtered colimit presentation of every bounded coefficient. The stages
are finite colimits of the original free mod-n representables. Their geometric
constructibility is a separate obligation, not part of this definition or a
consequence asserted from bounded annihilation alone.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sheaf.TorsionFinitePresentation

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.BoundedPresentation

universe u

attribute [local instance] hasSheafifyLarge Cardinal.fact_isRegular_aleph0

private theorem scalar_identity_commutes {C : Type*} [Category* C] [Preadditive C]
    (n : ℕ) {A B : C} (f : A ⟶ B) : f ≫ (n • 𝟙 B) = (n • 𝟙 A) ≫ f := by
  simp

variable (X : Scheme.{u}) (n : ℕ)

/-- The actual full subcategory defined by the original scalar identity equation. -/
abbrev Coefficient :=
  (TorsionZMod.killedSheaves X.smallEtaleTopology n :
    ObjectProperty (AbelianSheaf.{u, u + 1} X)).FullSubcategory

/-- The inclusion retains the original abelian sheaf and every original map. -/
abbrev inclusion : Coefficient X n ⥤ AbelianSheaf.{u, u + 1} X :=
  (TorsionZMod.killedSheaves X.smallEtaleTopology n).ι

/-- Original coefficient colimits preserve the literal common annihilator. -/
instance killedSheaves_closedColimits (I : Type (u + 1)) [SmallCategory I] :
    (TorsionZMod.killedSheaves X.smallEtaleTopology n :
      ObjectProperty (AbelianSheaf.{u, u + 1} X)).IsClosedUnderColimitsOfShape I where
  colimitsOfShape_le F hF := by
    obtain ⟨p⟩ := hF
    change n • 𝟙 F = 0
    apply p.isColimit.hom_ext
    intro i
    calc
      p.ι.app i ≫ (n • 𝟙 F) = (n • 𝟙 (p.diag.obj i)) ≫ p.ι.app i :=
        scalar_identity_commutes n (p.ι.app i)
      _ = 0 := by rw [p.prop_diag_obj i, zero_comp]
      _ = p.ι.app i ≫ 0 := by simp

/-- Bounded coefficients have all colimits of the standard coefficient/index size. -/
instance coefficient_hasColimits : HasColimitsOfSize.{u + 1, u + 1} (Coefficient X n) where
  has_colimits_of_shape _I _ := inferInstance

/-- The actual inclusion preserves these colimits; no replacement cocone is used. -/
instance inclusion_preservesColimits : PreservesColimitsOfSize.{u + 1, u + 1} (inclusion X n) where
  preservesColimitsOfShape {_I} := inferInstance

/-- The native free scalar-quotient generator as an actual bounded coefficient. -/
def free (U : X.Etale) : Coefficient X n :=
  ⟨freeZModRepresentable.{u + 1} X.smallEtaleTopology n U,
    nsmul_id_freeZModRepresentable X.smallEtaleTopology n U⟩

/-- Original sections represent maps out of the free mod-n generator inside the
actual bounded coefficient category. -/
def sectionsEquiv (U : X.Etale) (F : Coefficient X n) :
    (free X n U ⟶ F) ≃ F.obj.obj.obj (op U) where
  toFun a := (freeZModSectionsEquiv X.smallEtaleTopology n U F.obj a.hom).val
  invFun s := ObjectProperty.homMk
    ((freeZModSectionsEquiv X.smallEtaleTopology n U F.obj).symm
      ⟨s, TorsionZMod.sheafSectionsKilled X.smallEtaleTopology n F.obj F.property (op U) s⟩)
  left_inv a := by
    apply ObjectProperty.hom_ext
    exact (freeZModSectionsEquiv X.smallEtaleTopology n U F.obj).symm_apply_apply a.hom
  right_inv s := congrArg Subtype.val
    ((freeZModSectionsEquiv X.smallEtaleTopology n U F.obj).apply_symm_apply
      ⟨s, TorsionZMod.sheafSectionsKilled X.smallEtaleTopology n F.obj F.property (op U) s⟩)

/-- This representing equivalence retains the original coefficient maps. -/
theorem sectionsEquiv_naturality (U : X.Etale) {F G : Coefficient X n}
    (a : free X n U ⟶ F) (q : F ⟶ G) :
    sectionsEquiv X n U G (a ≫ q) = q.hom.hom.app (op U) (sectionsEquiv X n U F a) :=
  freeZModSectionsEquiv_naturality X.smallEtaleTopology n U a.hom q.hom

/-- The inverse section equivalence retains the literal coefficient action on
an unchanged section, without expanding the free sheaf's cokernel carrier. -/
theorem sectionsEquiv_symm_naturality (U : X.Etale) {F G : Coefficient X n}
    (s : F.obj.obj.obj (op U)) (q : F ⟶ G) :
    sectionsEquiv X n U G ((sectionsEquiv X n U F).symm s ≫ q) =
      q.hom.hom.app (op U) s :=
  (sectionsEquiv_naturality X n U _ q).trans
    (congrArg (fun z => q.hom.hom.app (op U) z)
      ((sectionsEquiv X n U F).apply_symm_apply s))

/-- The native full inclusion identifies the original Hom functors. -/
def homInclusionIso (U : X.Etale) :
    coyoneda.obj (op (free X n U)) ≅
      inclusion X n ⋙ coyoneda.obj (op (freeZModRepresentable.{u + 1}
        X.smallEtaleTopology n U)) :=
  NatIso.ofComponents (fun F =>
    ((TorsionZMod.killedSheaves X.smallEtaleTopology n).fullyFaithfulι.homEquiv).toIso)
    (fun q => by ext a; rfl)

/-- The original free mod-n generator is compact in the actual bounded category
whenever its original test scheme is qcqs. -/
theorem free_isFinitelyPresentable (U : X.Etale)
    [CompactSpace U.left] [QuasiSeparatedSpace U.left] :
    IsFinitelyPresentable.{u + 1} (free X n U) := by
  have := qcqs_freeZModRepresentable_isFinitelyPresentable n U
  exact Functor.isCardinalAccessible_of_natIso (homInclusionIso X n U).symm
    Cardinal.aleph0.{u + 1}

/-- The actual affine-etale free generators form a small family. -/
def generators : ObjectProperty (Coefficient X n) :=
  .ofObj (fun U : X.AffineEtale => free X n ((Scheme.AffineEtale.Spec X).obj U))

instance generators_small : ObjectProperty.Small.{u + 1} (generators X n) := by
  unfold generators
  infer_instance

/-- The actual affine-etale generators separate every pair of bounded
coefficient maps, via literal restriction sections. -/
theorem generators_isSeparating : (generators X n).IsSeparating := by
  intro F G a b h
  apply ObjectProperty.hom_ext
  apply (Scheme.EtaleAffineBasis.abelianRestriction X).map_injective
  apply ObjectProperty.hom_ext
  ext U s
  let V := (Scheme.AffineEtale.Spec X).obj U.unop
  let z : free X n V ⟶ F := (sectionsEquiv X n V F).symm s
  have hz := h (free X n V) ⟨U.unop⟩ z
  change a.hom.hom.app (op V) s = b.hom.hom.app (op V) s
  exact (sectionsEquiv_symm_naturality X n V s a).symm.trans
    ((congrArg (sectionsEquiv X n V G) hz).trans
      (sectionsEquiv_symm_naturality X n V s b))

/-- Maps from the original affine free generators detect every proper subobject;
thus the generator family is strong, without a supplied presentation premise. -/
theorem generators_isStrongGenerator : (generators X n).IsStrongGenerator := by
  rw [ObjectProperty.isStrongGenerator_iff]
  refine ⟨generators_isSeparating X n, ?_⟩
  intro F G a ha h
  have he : IsIso ((Scheme.EtaleAffineBasis.abelianRestriction X).map a.hom).hom := by
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro U
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    refine ⟨?_, ?_⟩
    · intro s t hst
      let V := (Scheme.AffineEtale.Spec X).obj U.unop
      apply (sectionsEquiv X n V F).symm.injective
      apply (cancel_mono a).mp
      apply (sectionsEquiv X n V G).injective
      exact (sectionsEquiv_symm_naturality X n V s a).trans
        (hst.trans (sectionsEquiv_symm_naturality X n V t a).symm)
    · intro s
      let V := (Scheme.AffineEtale.Spec X).obj U.unop
      obtain ⟨b, hb⟩ := h (free X n V) ⟨U.unop⟩ ((sectionsEquiv X n V G).symm s)
      refine ⟨sectionsEquiv X n V F b, ?_⟩
      exact (sectionsEquiv_naturality X n V b a).symm.trans
        ((congrArg (sectionsEquiv X n V G) hb).trans
          ((sectionsEquiv X n V G).apply_symm_apply s))
  have : IsIso ((sheafToPresheaf (Scheme.AffineEtale.topology X) AddCommGrpCat.{u + 1}).map
      ((Scheme.EtaleAffineBasis.abelianRestriction X).map a.hom)) := he
  have : IsIso ((Scheme.EtaleAffineBasis.abelianRestriction X).map a.hom) :=
    isIso_of_reflects_iso _
      (sheafToPresheaf (Scheme.AffineEtale.topology X) AddCommGrpCat.{u + 1})
  have hi : IsIso a.hom :=
    isIso_of_reflects_iso a.hom (Scheme.EtaleAffineBasis.abelianRestriction X)
  have : IsIso ((inclusion X n).map a) := hi
  exact isIso_of_reflects_iso a (inclusion X n)

/-- Every actual affine free generator is finitely presentable at the displayed size. -/
theorem generators_presentable :
    generators X n ≤ isCardinalPresentable (Coefficient X n) Cardinal.aleph0.{u + 1} := by
  rintro F ⟨U⟩
  have : IsAffine ((Scheme.AffineEtale.Spec X).obj U).left := by
    change IsAffine (Spec U.left.unop)
    infer_instance
  exact free_isFinitelyPresentable X n ((Scheme.AffineEtale.Spec X).obj U)

/-- Finite-colimit stages are the proved categorical closure of the actual affine
free generators. This is not the definition of geometric constructibility. -/
def finiteColimitStages : ObjectProperty (Coefficient X n) :=
  (generators X n).colimitsCardinalClosure Cardinal.aleph0.{u + 1}

/-- The finite-colimit stages form a dense subcategory by the actual strong
generator and compactness proofs. -/
theorem finiteColimitStages_isDense : (finiteColimitStages X n).ι.IsDense :=
  (generators_isStrongGenerator X n).isDense_colimitsCardinalClosure_ι
    (generators_presentable X n)

/-- The actual finite-colimit stages are compact and generate every bounded
coefficient by a filtered colimit, rather than assuming the desired presentation. -/
theorem finiteColimitStages_filteredGenerator :
    (finiteColimitStages X n).IsCardinalFilteredGenerator Cardinal.aleph0.{u + 1} := by
  have := finiteColimitStages_isDense X n
  have (F : Coefficient X n) : IsCardinalFiltered
      (CostructuredArrow (finiteColimitStages X n).ι F) Cardinal.aleph0.{u + 1} := by
    change IsCardinalFiltered (CostructuredArrow
      ((generators X n).colimitsCardinalClosure Cardinal.aleph0.{u + 1}).ι F)
        Cardinal.aleph0.{u + 1}
    infer_instance
  have hp : finiteColimitStages X n ≤
      isCardinalPresentable (Coefficient X n) Cardinal.aleph0.{u + 1} :=
    ObjectProperty.colimitsCardinalClosure_le_isCardinalPresentable.{u + 1, u + 1, u + 2}
      (generators X n) (generators_presentable X n)
  refine ⟨hp, fun F => ?_⟩
  have : LocallySmall.{u + 1} (Coefficient X n) := inferInstance
  have : ObjectProperty.EssentiallySmall.{u + 1} (finiteColimitStages X n) := by
    change ObjectProperty.EssentiallySmall.{u + 1}
      ((generators X n).colimitsCardinalClosure Cardinal.aleph0.{u + 1})
    infer_instance
  have : EssentiallySmall.{u + 1} (finiteColimitStages X n).FullSubcategory := inferInstance
  let J := CostructuredArrow (finiteColimitStages X n).ι F
  have : EssentiallySmall.{u + 1} J := by
    dsimp only [J]
    infer_instance
  let e : J ≌ SmallModel.{u + 1} J := equivSmallModel.{u + 1} J
  refine ⟨SmallModel.{u + 1} J, inferInstance,
    IsCardinalFiltered.of_equivalence Cardinal.aleph0.{u + 1} e, ⟨{
      diag := _
      ι := _
      isColimit := ((finiteColimitStages X n).ι.denseAt F).whiskerEquivalence e.symm
      prop_diag_obj := ?_ }⟩⟩
  intro i
  exact (e.inverse.obj i).left.property

/-- Every originally n-annihilated etale sheaf is an actual filtered colimit of
finite-colimit stages of affine free mod-n representables. All original maps,
coefficients and the index universe are retained. Geometric constructibility of
these stages is not assumed or asserted by this producer. -/
theorem exists_filtered_presentation (F : AbelianSheaf.{u, u + 1} X)
    (hF : n • 𝟙 F = 0) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Coefficient X n)
      (ι : D ⋙ inclusion X n ⟶ (Functor.const I).obj F),
      Nonempty (IsColimit (Cocone.mk F ι)) ∧
        ∀ i, finiteColimitStages X n (D.obj i) := by
  obtain ⟨I, hI, hfiltered, ⟨p⟩⟩ :=
    (finiteColimitStages_filteredGenerator X n).exists_colimitsOfShape ⟨F, hF⟩
  have : IsFiltered I := isFiltered_of_isCardinalFiltered I Cardinal.aleph0.{u + 1}
  let q := p.toColimitPresentation.map (inclusion X n)
  exact ⟨I, hI, inferInstance, p.diag, q.ι, ⟨q.isColimit⟩, p.prop_diag_obj⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.BoundedPresentation
