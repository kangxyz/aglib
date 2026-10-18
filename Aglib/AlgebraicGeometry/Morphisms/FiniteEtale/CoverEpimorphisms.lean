/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverDirectSummands
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverCoproductPreservation

/-! Categorical epimorphisms of actual finite étale covers are surjective
scheme maps, and the actual fibre functor preserves them at every separably
closed field-valued point. No connectedness, quotient, or Galois premises
supply either conclusion. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.FiniteEtale.Connectedness

namespace AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber fiberToFinite forgetToScheme)

universe u
variable {X : Scheme.{u}}

attribute [local instance] hom_isFinite hom_etale

/-- An actual Boolean-labelled map from a cover to the trivial cover. -/
def coverBoolLabel (Y : Scheme.FiniteEtale X) (b : Bool) : Y ⟶ trivialCover X (ULift.{u} Bool) :=
  ObjectProperty.homMk (Over.homMk
    (Y.obj.hom ≫ (Sigma.ι (fun _ : ULift.{u} Bool => terminalCover X) ⟨b⟩).hom.left) (by
      have hb : (Sigma.ι (fun _ : ULift.{u} Bool => terminalCover X) ⟨b⟩).hom.left ≫
          (trivialCover X (ULift.{u} Bool)).obj.hom = 𝟙 X :=
        Over.w (Sigma.ι (fun _ : ULift.{u} Bool => terminalCover X) ⟨b⟩).hom
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun f : X ⟶ X => Y.obj.hom ≫ f) hb).trans
          (Category.comp_id Y.obj.hom))))

theorem coverBoolLabel_sigma (Y : Scheme.FiniteEtale X) (b : Bool) :
    (coverBoolLabel Y b).hom.left ≫ (trivialCoverSigmaIso X (ULift.{u} Bool)).hom =
      Y.obj.hom ≫ Sigma.ι (fun _ : ULift.{u} Bool => X) ⟨b⟩ :=
  (Category.assoc _ _ _).trans
    (congrArg (fun f : X ⟶ ∐ fun _ : ULift.{u} Bool => X => Y.obj.hom ≫ f)
      (trivialCoverSigmaIso_ι X (ULift.{u} Bool) ⟨b⟩))

/-- The complement of an epi mono is empty: two actual Boolean indicator
maps agree on its image and differ on every point of the complement. -/
theorem cover_isIso_of_mono_epi {Y Z : Scheme.FiniteEtale X} (i : Y ⟶ Z) [Mono i] [Epi i] :
    IsIso i := by
  obtain ⟨W, j, ⟨hc⟩⟩ := coverMonoInducesIsoOnDirectSummand i
  let a := BinaryCofan.IsColimit.desc hc (coverBoolLabel Y false) (coverBoolLabel W false)
  let b := BinaryCofan.IsColimit.desc hc (coverBoolLabel Y false) (coverBoolLabel W true)
  have hab : a = b := (cancel_epi i).mp
    ((BinaryCofan.IsColimit.inl_desc hc _ _).trans
      (BinaryCofan.IsColimit.inl_desc hc _ _).symm)
  have hl : coverBoolLabel W false = coverBoolLabel W true :=
    (BinaryCofan.IsColimit.inr_desc hc _ _).symm.trans
      ((congrArg (fun f : Z ⟶ trivialCover X (ULift.{u} Bool) => j ≫ f) hab).trans
        (BinaryCofan.IsColimit.inr_desc hc _ _))
  have hW : IsEmpty W.obj.left := by
    constructor
    intro w
    have he := (coverBoolLabel_sigma W false).symm.trans
      ((congrArg (fun f : W ⟶ trivialCover X (ULift.{u} Bool) =>
          f.hom.left ≫ (trivialCoverSigmaIso X (ULift.{u} Bool)).hom) hl).trans
        (coverBoolLabel_sigma W true))
    have hp := congrArg (fun f : W.obj.left ⟶ ∐ fun _ : ULift.{u} Bool => X => f w) he
    have hs := (sigmaι_eq_iff (g := fun _ : ULift.{u} Bool => X) ⟨false⟩ ⟨true⟩
      (W.obj.hom w) (W.obj.hom w)).mp hp
    have hBool : false = true := congrArg (fun p : Σ _ : ULift.{u} Bool, X => p.1.down) hs
    cases hBool
  let := hW
  exact (BinaryCofan.isColimit_iff_isIso_inl (isInitialCoverOfIsEmpty W)
    (BinaryCofan.mk i j)).mp ⟨hc⟩

/-- The open subset of `Z.obj.left` given by the range of the cover morphism `f`. -/
def coverImageOpen {Y Z : Scheme.FiniteEtale X} (f : Y ⟶ Z) : Z.obj.left.Opens :=
  ⟨Set.range f.hom.left, (hom_range_isClopen f).2⟩

/-- The finite étale cover obtained by restricting `Z` to the clopen range of `f`. -/
def coverImage {Y Z : Scheme.FiniteEtale X} (f : Y ⟶ Z) : Scheme.FiniteEtale X :=
  clopenCover Z (coverImageOpen f) (hom_range_isClopen f).1

/-- The inclusion of the clopen image cover of `f` into `Z`. -/
def coverImageι {Y Z : Scheme.FiniteEtale X} (f : Y ⟶ Z) : coverImage f ⟶ Z :=
  clopenCoverι Z (coverImageOpen f) (hom_range_isClopen f).1

instance coverImageι_mono {Y Z : Scheme.FiniteEtale X} (f : Y ⟶ Z) : Mono (coverImageι f) := by
  apply (forgetToScheme X).mono_of_mono_map
  change Mono (coverImageOpen f).ι
  infer_instance

/-- The factorization morphism from `Y` to the clopen image cover of `f`, obtained
by lifting the underlying scheme map through the image open immersion. -/
def coverImageFactor {Y Z : Scheme.FiniteEtale X} (f : Y ⟶ Z) : Y ⟶ coverImage f := by
  let : IsOpenImmersion (coverImageOpen f).ι :=
    Scheme.Opens.instIsOpenImmersionι (coverImageOpen f)
  let hrange : Set.range f.hom.left ⊆ Set.range (coverImageOpen f).ι := by
    rintro _ ⟨y, rfl⟩
    exact ⟨⟨f.hom.left y, ⟨y, rfl⟩⟩, rfl⟩
  refine ObjectProperty.homMk ?_
  change Y.obj ⟶ Over.mk ((coverImageOpen f).ι ≫ Z.obj.hom)
  refine Over.homMk (IsOpenImmersion.lift (coverImageOpen f).ι f.hom.left hrange) ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g : Y.obj.left ⟶ Z.obj.left => g ≫ Z.obj.hom)
      (IsOpenImmersion.lift_fac (coverImageOpen f).ι f.hom.left hrange)).trans (Over.w f.hom))

theorem coverImageFactor_ι {Y Z : Scheme.FiniteEtale X} (f : Y ⟶ Z) :
    coverImageFactor f ≫ coverImageι f = f := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac (coverImageOpen f).ι f.hom.left _

/-- Epimorphisms in the actual finite étale category are surjective on
underlying scheme points, for every base scheme. -/
theorem coverHom_surjective_of_epi {Y Z : Scheme.FiniteEtale X} (f : Y ⟶ Z) [Epi f] :
    Surjective f.hom.left := by
  have : Epi (coverImageFactor f ≫ coverImageι f) := by
    rw [coverImageFactor_ι]
    infer_instance
  have : Epi (coverImageι f) := epi_of_epi (coverImageFactor f) (coverImageι f)
  have : IsIso (coverImageι f) := cover_isIso_of_mono_epi (coverImageι f)
  have : IsIso (coverImageOpen f).ι := by
    change IsIso ((forgetToScheme X).map (coverImageι f))
    infer_instance
  constructor
  intro z
  obtain ⟨p, hp⟩ := (inferInstance : Surjective (coverImageOpen f).ι).surj z
  obtain ⟨y, hy⟩ := p.property
  exact ⟨y, hy.trans hp⟩

/-- Geometric point lifting through the actual étale scheme map proves
surjectivity of the actual finite-valued fibre map. -/
theorem fiberToFinite_surjective_of_epi {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ X) {Y Z : Scheme.FiniteEtale X} (f : Y ⟶ Z) [Epi f] :
    Function.Surjective ((fiberToFinite s).map f) := by
  intro q
  let := coverHom_surjective_of_epi f
  obtain ⟨y, hy⟩ := (inferInstance : Surjective f.hom.left).surj
    (q.left (default : Spec (CommRingCat.of Ω)))
  obtain ⟨l, hl, _⟩ := Scheme.exists_fac_of_etale_of_isSepClosed f.hom.left q.left y hy
  let p : Fiber s Y := Over.homMk l (by
    calc
      l ≫ Y.obj.hom = l ≫ (f.hom.left ≫ Z.obj.hom) :=
        congrArg (fun g : Y.obj.left ⟶ X => l ≫ g) (Over.w f.hom).symm
      _ = (l ≫ f.hom.left) ≫ Z.obj.hom := (Category.assoc _ _ _).symm
      _ = q.left ≫ Z.obj.hom := congrArg (fun g => g ≫ Z.obj.hom) hl
      _ = s := Over.w q)
  refine ⟨p, ?_⟩
  apply Over.OverMorphism.ext
  exact hl

instance fiberToFinite_map_epi {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ X) {Y Z : Scheme.FiniteEtale X} (f : Y ⟶ Z) [Epi f] :
    Epi ((fiberToFinite s).map f) :=
  ConcreteCategory.epi_of_surjective _ (fiberToFinite_surjective_of_epi s f)

instance instPreservesEpimorphismsFiberToFinite {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ X) : (fiberToFinite s).PreservesEpimorphisms where
  preserves f := fiberToFinite_map_epi s f

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 6f23cdd1f955582e6f2cbda7c1b5f4e8d537ff9f180c884a1e956ab0572efab4.
Definitions, hypotheses and universes are retained modulo native names. -/
