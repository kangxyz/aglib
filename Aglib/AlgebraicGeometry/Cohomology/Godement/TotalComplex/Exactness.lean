/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/GodementTotalExact.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 193]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Exactness of the actual Godement totalization

The original coproduct diagonals are exact in the actual Grothendieck abelian
category of all module sheaves. This uses exact coproducts, without assuming
exactness of arbitrary sheaf products.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Godement

/-- Zero extension of the actual Godement resolution remains an exact functor. -/
theorem godementResolutionInt_shortExact {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) : (S.map (godementResolutionInt X)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro q
  by_cases hq : 0 ≤ q
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    let e := CategoryTheory.Functor.isoWhiskerLeft (godementResolution X)
      (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso X.Modules (i := k)
        (i' := (k : ℤ)) (by rfl))
    exact (ShortComplex.shortExact_iff_of_iso (S.mapNatIso e)).mpr
      (godementResolutionTerm_shortExact hS k)
  · let T := (S.map (godementResolutionInt X)).map (HomologicalComplex.eval _ _ q)
    have h₁ : IsZero T.X₁ :=
      CochainComplex.isZero_of_isStrictlyGE ((godementResolutionInt X).obj S.X₁) 0 q (by omega)
    have h₂ : IsZero T.X₂ :=
      CochainComplex.isZero_of_isStrictlyGE ((godementResolutionInt X).obj S.X₂) 0 q (by omega)
    have h₃ : IsZero T.X₃ :=
      CochainComplex.isZero_of_isStrictlyGE ((godementResolutionInt X).obj S.X₃) 0 q (by omega)
    have hm : Mono T.f := ⟨fun _ _ _ => h₁.eq_of_tgt _ _⟩
    have he : Epi T.g := ⟨fun _ _ _ => h₃.eq_of_src _ _⟩
    exact { exact := ShortComplex.exact_of_isZero_X₂ _ h₂ }

instance godementResolutionInt_preservesHomology (X : Scheme.{u}) :
    (godementResolutionInt X).PreservesHomology :=
  ((CategoryTheory.Functor.exact_tfae (godementResolutionInt X)).out 1 3).mp
    (fun _ hS => godementResolutionInt_shortExact hS)

/-- Exactness of a discrete diagram is detected on every actual object. -/
theorem godement_discrete_shortExact {X : Scheme.{u}} {I : Type}
    (S : ShortComplex (Discrete I ⥤ X.Modules))
    (hS : ∀ i, (S.map ((evaluation _ _).obj (Discrete.mk i))).ShortExact) : S.ShortExact where
  mono_f := by
    have : ∀ i, Mono (S.f.app i) := fun i => (hS i.as).mono_f
    exact NatTrans.mono_of_mono_app S.f
  epi_g := by
    have : ∀ i, Epi (S.g.app i) := fun i => (hS i.as).epi_g
    exact NatTrans.epi_of_epi_app S.g
  exact := by
    rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
    apply NatTrans.ext
    funext i
    have hz := ((ShortComplex.exact_iff_isZero_homology _).mp (hS i.as).exact).of_iso
      (S.mapHomologyIso ((evaluation _ _).obj i)).symm
    exact hz.eq_of_src _ _

/-- The original entire antidiagonal, before discarding its zero summands. -/
abbrev GodementTotalDegree (n : ℤ) :=
  ((ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ)) ⁻¹' ({n} : Set ℤ))

/-- The actual diagram whose coproduct is a degree of the original totalization. -/
def godementDiagonalFunctor (X : Scheme.{u}) (n : ℤ) :
    CochainComplex X.Modules ℤ ⥤ (Discrete (GodementTotalDegree n) ⥤ X.Modules) where
  obj K := Discrete.functor (fun p : GodementTotalDegree n =>
    ((godementResolutionInt X).obj (K.X p.val.1)).X p.val.2)
  map {K L} f := Discrete.natTrans (fun p =>
    ((godementResolutionInt X).map (f.f p.as.val.1)).f p.as.val.2)
  map_id K := by
    apply NatTrans.ext
    funext p
    change ((godementResolutionInt X).map (𝟙 (K.X p.as.val.1))).f p.as.val.2 = 𝟙 _
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext p
    change ((godementResolutionInt X).map (f.f p.as.val.1 ≫ g.f p.as.val.1)).f p.as.val.2 = _
    rw [Functor.map_comp]
    rfl

instance godementDiagonalFunctor_additive (X : Scheme.{u}) (n : ℤ) :
    (godementDiagonalFunctor X n).Additive where
  map_add {K L} f g := by
    apply NatTrans.ext
    funext p
    change ((godementResolutionInt X).map (f.f p.as.val.1 + g.f p.as.val.1)).f p.as.val.2 = _
    rw [Functor.map_add]
    rfl

/-- The actual entire diagonal diagram preserves every original short exact sequence. -/
theorem godementDiagonalFunctor_shortExact {X : Scheme.{u}}
    {S : ShortComplex (CochainComplex X.Modules ℤ)} (hS : S.ShortExact) (n : ℤ) :
    (S.map (godementDiagonalFunctor X n)).ShortExact := by
  apply godement_discrete_shortExact
  intro p
  change (((S.map (HomologicalComplex.eval _ _ p.val.1)).map (godementResolutionInt X)).map
    (HomologicalComplex.eval _ _ p.val.2)).ShortExact
  exact (godementResolutionInt_shortExact (hS.map_of_exact _)).map_of_exact _

instance godementDiagonalFunctor_preservesHomology (X : Scheme.{u}) (n : ℤ) :
    (godementDiagonalFunctor X n).PreservesHomology :=
  ((CategoryTheory.Functor.exact_tfae (godementDiagonalFunctor X n)).out 1 3).mp
    (fun _ hS => godementDiagonalFunctor_shortExact hS n)

/-- The diagonal coproduct functor and actual totalization evaluation agree naturally. -/
def godementTotalDegreeIso (X : Scheme.{u}) (n : ℤ) :
    godementTotal X ⋙ HomologicalComplex.eval _ _ n ≅
      godementDiagonalFunctor X n ⋙ colim :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro K L f
    dsimp only [Functor.comp_map, Functor.comp_obj, Iso.refl_hom, godementTotal,
      godementDiagonalFunctor, HomologicalComplex₂.totalFunctor, godementBicomplex,
      CategoryTheory.Functor.mapHomologicalComplex]
    rw [Category.comp_id, Category.id_comp]
    apply Sigma.hom_ext
    intro p
    change ((godementBicomplex X).obj K).ιTotal (.up ℤ) p.val.1 p.val.2 n p.property ≫
        ((godementTotal X).map f).f n = _
    dsimp only [godementTotal, Functor.comp_map, HomologicalComplex₂.totalFunctor]
    rw [HomologicalComplex₂.ιTotal_map]
    rcases p with ⟨⟨i, j⟩, hp⟩
    change ((godementResolutionInt X).map (f.f i)).f j ≫
        colimit.ι ((godementDiagonalFunctor X n).obj L) (Discrete.mk ⟨(i, j), hp⟩) =
      colimit.ι ((godementDiagonalFunctor X n).obj K) (Discrete.mk ⟨(i, j), hp⟩) ≫
        colim.map ((godementDiagonalFunctor X n).map f)
    exact (ι_colimMap ((godementDiagonalFunctor X n).map f) (Discrete.mk ⟨(i, j), hp⟩)).symm)


instance godementTotal_additive (X : Scheme.{u}) : (godementTotal X).Additive where
  map_add {K L} f g := by
    ext1 n
    let F := godementTotal X ⋙ HomologicalComplex.eval X.Modules (.up ℤ) n
    let : F.Additive := CategoryTheory.Functor.additive_of_iso (godementTotalDegreeIso X n).symm
    exact F.map_add

/-- Every actual diagonal coproduct preserves short exactness. The installed
Grothendieck abelian structure realizes exact coproducts for these module sheaves. -/
theorem godementTotal_shortExact {X : Scheme.{u}}
    {S : ShortComplex (CochainComplex X.Modules ℤ)} (hS : S.ShortExact) :
    (S.map (godementTotal X)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let F := godementDiagonalFunctor X n
  let G : (Discrete (GodementTotalDegree n) ⥤ X.Modules) ⥤ X.Modules := colim
  have hF : (S.map F).ShortExact := godementDiagonalFunctor_shortExact hS n
  have hFG : ((S.map F).map G).ShortExact := hF.map_of_exact G
  exact (ShortComplex.shortExact_iff_of_iso (S.mapNatIso (godementTotalDegreeIso X n))).mpr hFG

/-- Homology preservation for short complexes in the abelian category of cochain complexes. -/
instance godementTotal_preservesHomology (X : Scheme.{u}) :
    (godementTotal X).PreservesHomology :=
  ((CategoryTheory.Functor.exact_tfae (godementTotal X)).out 1 3).mp
    (fun _ hS => godementTotal_shortExact hS)


instance godementTotal_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (godementTotal X) :=
  CategoryTheory.Functor.preservesFiniteLimits_of_preservesHomology _

instance godementTotal_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (godementTotal X) :=
  CategoryTheory.Functor.preservesFiniteColimits_of_preservesHomology _

/-- Degreewise monomorphisms, the original standard cofibrations, are preserved by
this actual totalization functor. -/
theorem godementTotal_map_degreewiseMono {X : Scheme.{u}}
    {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L) (h : ∀ n, Mono (f.f n)) (n : ℤ) :
    Mono (((godementTotal X).map f).f n) := by
  have : Mono f := HomologicalComplex.mono_of_mono_f f h
  have : Mono ((godementTotal X).map f) := inferInstance
  exact inferInstanceAs
    (Mono ((HomologicalComplex.eval X.Modules (.up ℤ) n).map ((godementTotal X).map f)))

end AlgebraicGeometry.Scheme.Modules.Godement
