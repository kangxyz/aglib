/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.InvariantSubobject
public import Aglib.RepresentationTheory.FiniteModulePGroup
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import Mathlib.GroupTheory.Torsion

/-! # Actual module-sheaf devissage on a finite group cover

The supplied data are the original cover, action graphs, image and constant
adjunctions, and their actual section comparisons. Invariant sections construct
the subobject map. Its actual cokernel, with its original projection, constructs
the quotient trivialization. No descent functor for arbitrary representations
or finite underlying-set hypothesis on the coefficient module is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open ModuleCat.Sheaf.ConstantRing

universe u v r w g a b

namespace CategoryTheory.FiniteGroupAction

/-- Original operational cover data. The section value law fixes the supplied
section isomorphism through the actual constant unit and trivialization. -/
structure ModuleCoverData.{uc, vc, rc, wc, gc, ac, bc}
    {C : Type uc} [Category.{vc} C] (J : GrothendieckTopology C)
    (R : Type rc) [CommRing R] (G : Type gc) [Group G]
    (D : Type ac) [Category.{bc} D] [HasSheafify J (ModuleCat.{wc} R)] where
  /-- The original terminal test object. -/
  terminal : C
  /-- The original cover object. -/
  cover : C
  /-- The original self-overlap of the cover. -/
  overlap : C
  /-- Terminality of the original test object. -/
  isTerminal : IsTerminal terminal
  /-- The original group action by automorphisms of the cover. -/
  action : G →* Aut cover
  /-- The original structural arrow from the cover to the terminal object. -/
  arrow : cover ⟶ terminal
  arrow_covering :
    Sieve.ofArrows (fun _ : Unit => cover) (fun _ => arrow) ∈ J terminal
  /-- The first projection from the original self-overlap. -/
  first : overlap ⟶ cover
  /-- The second projection from the original self-overlap. -/
  second : overlap ⟶ cover
  isPullback : IsPullback first second arrow arrow
  /-- The original family of action graphs covering the self-overlap. -/
  graph : G → (cover ⟶ overlap)
  graph_covering : Sieve.ofArrows (fun _ : G => cover) graph ∈ J overlap
  graph_first : ∀ σ, graph σ ≫ first = 𝟙 cover
  graph_second : ∀ σ, graph σ ≫ second = (action σ).hom
  /-- The supplied original image functor on module sheaves. -/
  image : Sheaf J (ModuleCat.{wc} R) ⥤ D
  /-- The original right adjoint of the image functor. -/
  directImage : D ⥤ Sheaf J (ModuleCat.{wc} R)
  /-- The original constant-module functor on the cover. -/
  «constant» : ModuleCat.{wc} R ⥤ D
  /-- The original section functor on the cover category. -/
  sections : D ⥤ ModuleCat.{wc} R
  /-- The actual adjunction between the original image functors. -/
  imageAdjunction : image ⊣ directImage
  /-- The actual constant-module and section adjunction on the cover. -/
  constantAdjunction : «constant» ⊣ sections
  /-- The original comparison between direct-image sections and cover sections. -/
  rightSectionsIso : directImage ⋙
    ((sheafSections J (ModuleCat.{wc} R)).obj (op terminal)) ≅ sections
  /-- The original constant-module comparison for the image functor. -/
  constantIso : constantSheaf J (ModuleCat.{wc} R) ⋙ image ≅ «constant»
  constantIso_eq : constantIso = Adjunction.leftAdjointCompIso
    (constantSheafAdj J (ModuleCat.{wc} R) isTerminal)
    imageAdjunction constantAdjunction rightSectionsIso
  /-- The original comparison from image sections to sections on the cover object. -/
  sectionComparison : ∀ F : Sheaf J (ModuleCat.{wc} R),
    sections.obj (image.obj F) ≅ F.obj.obj (op cover)
  sectionComparison_naturality : ∀ {F F' : Sheaf J (ModuleCat.{wc} R)} (f : F ⟶ F'),
    sections.map (image.map f) ≫ (sectionComparison F').hom =
      (sectionComparison F).hom ≫ f.hom.app (op cover)
  /-- The original module-to-section isomorphism from an actual trivialization. -/
  sectionIso : ∀ (F : Sheaf J (ModuleCat.{wc} R)) (M : ModuleCat.{wc} R),
    IsAddTorsion M → (image.obj F ≅ constant.obj M) → (M ≅ F.obj.obj (op cover))
  sectionIso_hom : ∀ (F : Sheaf J (ModuleCat.{wc} R)) (M : ModuleCat.{wc} R)
    (hM : IsAddTorsion M) (t : image.obj F ≅ constant.obj M),
    (sectionIso F M hM t).hom = constantAdjunction.unit.app M ≫
      sections.map t.inv ≫ (sectionComparison F).hom
  restriction : ∀ F : Sheaf J (ModuleCat.{wc} R),
    imageAdjunction.unitSectionMap
      ((sheafSections J (ModuleCat.{wc} R)).obj (op terminal)) rightSectionsIso F ≫
        (sectionComparison F).hom = F.obj.map arrow.op

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type r) [CommRing R] (G : Type g) [Group G]
  (D : Type a) [Category.{b} D] [HasSheafify J (ModuleCat.{w} R)]


namespace ModuleCoverData

variable {J R G D} (d : ModuleCoverData.{u, v, r, w, g, a, b} J R G D)

/-- Graph-cover separatedness supplies the actual overlap condition. -/
theorem invariant_overlap (F : Sheaf J (ModuleCat.{w} R))
    {E : ModuleCat.{w} R} (z : E ⟶ F.obj.obj (op d.cover))
    (hz : ∀ σ : G, z ≫ F.obj.map (d.action σ).hom.op = z) :
    z ≫ F.obj.map d.first.op = z ≫ F.obj.map d.second.op :=
  invariantSection_overlap F d.action d.first d.second d.graph
    d.graph_covering d.graph_first d.graph_second z hz

/-- The original inverse-restriction action in the original coefficient module. -/
def representation (F : Sheaf J (ModuleCat.{w} R)) (M : ModuleCat.{w} R)
    (hM : IsAddTorsion M) (t : d.image.obj F ≅ d.constant.obj M) :
    Representation R G M :=
  Presheaf.transportedRestrictionRepresentation F.obj d.action (d.sectionIso F M hM t)

variable (F : Sheaf J (ModuleCat.{w} R)) (M : ModuleCat.{w} R)
  (hM : IsAddTorsion M) (t : d.image.obj F ≅ d.constant.obj M)
  {N : ModuleCat.{w} R} (i : N ⟶ M)
  (hi : ∀ (σ : G) (x : N), d.representation F M hM t σ (i x) = i x)

/-- Actual invariant-section amalgamation transposed by the original constant adjunction. -/
def subobjectMap : (constantSheaf J (ModuleCat.{w} R)).obj N ⟶ F :=
  invariantSubobjectMap J F d.action d.arrow d.arrow_covering d.first d.second
    d.isPullback (d.invariant_overlap F) (d.sectionIso F M hM t) i hi d.isTerminal

/-- The constructed map has the literal supplied constant image. -/
@[reassoc]
theorem subobjectMap_image :
    d.image.map (d.subobjectMap F M hM t i hi) ≫ t.hom =
      d.constantIso.hom.app N ≫ d.constant.map i :=
  invariantSubobjectMap_pullback J F d.action d.arrow d.arrow_covering
    d.first d.second d.isPullback (d.invariant_overlap F) (d.sectionIso F M hM t)
    i hi d.isTerminal d.imageAdjunction d.constantAdjunction d.rightSectionsIso
    d.constantIso d.constantIso_eq t (d.sectionComparison F)
    (d.sectionIso_hom F M hM t) (d.restriction F)

/-- The same actual map and its literal cokernel form the short exact sequence. -/
theorem subobjectMap_shortExact [d.image.Faithful]
    [d.constant.PreservesMonomorphisms] [Mono i] :
    (ShortComplex.cokernelSequence (d.subobjectMap F M hM t i hi)).ShortExact :=
  invariantSubobjectMap_shortExact J F d.action d.arrow d.arrow_covering
    d.first d.second d.isPullback (d.invariant_overlap F) (d.sectionIso F M hM t)
    i hi d.isTerminal d.imageAdjunction d.constantAdjunction d.rightSectionsIso
    d.constantIso d.constantIso_eq t (d.sectionComparison F)
    (d.sectionIso_hom F M hM t) (d.restriction F)

/-- The actual cokernel comparison through the original image and constant functors. -/
def subobjectCokernelIso [Preadditive D] [d.image.PreservesZeroMorphisms]
    [d.constant.PreservesZeroMorphisms] :
    d.image.obj (cokernel (d.subobjectMap F M hM t i hi)) ≅
      d.constant.obj (cokernel i) :=
  invariantSubobjectCokernelIso J F d.action d.arrow d.arrow_covering
    d.first d.second d.isPullback (d.invariant_overlap F) (d.sectionIso F M hM t)
    i hi d.isTerminal d.imageAdjunction d.constantAdjunction d.rightSectionsIso
    d.constantIso d.constantIso_eq t (d.sectionComparison F)
    (d.sectionIso_hom F M hM t) (d.restriction F)

/-- The quotient comparison retains the original cokernel projection. -/
@[reassoc]
theorem subobjectCokernelIso_projection [Preadditive D]
    [d.image.PreservesZeroMorphisms] [d.constant.PreservesZeroMorphisms] :
    d.image.map (cokernel.π (d.subobjectMap F M hM t i hi)) ≫
      (d.subobjectCokernelIso F M hM t i hi).hom = t.hom ≫ d.constant.map (cokernel.π i) :=
  invariantSubobjectCokernelIso_projection J F d.action d.arrow d.arrow_covering
    d.first d.second d.isPullback (d.invariant_overlap F) (d.sectionIso F M hM t)
    i hi d.isTerminal d.imageAdjunction d.constantAdjunction d.rightSectionsIso
    d.constantIso d.constantIso_eq t (d.sectionComparison F)
    (d.sectionIso_hom F M hM t) (d.restriction F)

/-- A trivial actual action gives the identity-map case of the same construction. -/
def trivialActionIso [d.image.Faithful]
    (htriv : ∀ (σ : G) (x : M), d.representation F M hM t σ x = x) :
    (constantSheaf J (ModuleCat.{w} R)).obj M ≅ F := by
  let f := d.subobjectMap F M hM t (𝟙 M) htriv
  have hf : d.image.map f ≫ t.hom = d.constantIso.hom.app M := by
    simpa only [Functor.map_id, Category.comp_id] using
      d.subobjectMap_image F M hM t (𝟙 M) htriv
  have : IsIso (d.image.map f ≫ t.hom) := by
    rw [hf]
    infer_instance
  have : IsIso (d.image.map f) := IsIso.of_isIso_comp_right _ t.hom
  have : IsIso f := isIso_of_reflects_iso f d.image
  exact asIso f

variable {F M} {hM} {t}

/-- Naturality of the actual unit and section comparison fixes quotient actions. -/
theorem representation_naturality {F' : Sheaf J (ModuleCat.{w} R)}
    {M' : ModuleCat.{w} R} (hM' : IsAddTorsion M')
    (t' : d.image.obj F' ≅ d.constant.obj M') (f : F ⟶ F') (j : M ⟶ M')
    (hf : d.image.map f ≫ t'.hom = t.hom ≫ d.constant.map j) (σ : G) (x : M) :
    j (d.representation F M hM t σ x) = d.representation F' M' hM' t' σ (j x) := by
  apply Presheaf.transportedRestrictionRepresentation_naturality F.obj d.action f.hom
    (d.sectionIso F M hM t) (d.sectionIso F' M' hM' t') j
  rw [d.sectionIso_hom, d.sectionIso_hom]
  exact d.constantAdjunction.unit_iso_sections_naturality t t' (d.image.map f) j hf
    (d.sectionComparison F).hom (d.sectionComparison F').hom
    (f.hom.app (op d.cover)) (d.sectionComparison_naturality f)

private theorem torsion_of_nsmul_eq_zero (M : ModuleCat.{w} R) (p : ℕ)
    (hp : 0 < p) (hM : ∀ x : M, p • x = 0) : IsAddTorsion M :=
  fun x => isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨p, hp, hM x⟩

/-- Full actual-sheaf induction through finite trivial subobjects and actual cokernels.
Finite generation is over the original ring; the additive group may be infinite. -/
theorem property_of_pGroup_trivialization [Preadditive D] [d.image.Faithful]
    [d.constant.PreservesMonomorphisms] [d.image.PreservesZeroMorphisms]
    [d.constant.PreservesZeroMorphisms] [Finite G] (p : ℕ) [Fact p.Prime]
    (hG : IsPGroup p G) (P : Sheaf J (ModuleCat.{w} R) → Prop)
    (hconstant : ∀ M : ModuleCat.{w} R, ∀ [Module.Finite R M],
      (∀ x : M, p • x = 0) → P ((constantSheaf J (ModuleCat.{w} R)).obj M))
    (hiso : ∀ {E E' : Sheaf J (ModuleCat.{w} R)}, (E ≅ E') → P E → P E')
    (hstep : ∀ S : ShortComplex (Sheaf J (ModuleCat.{w} R)), S.ShortExact →
      P S.X₁ → P S.X₃ → P S.X₂)
    (F : Sheaf J (ModuleCat.{w} R)) (M : ModuleCat.{w} R) [Module.Finite R M]
    (hM : ∀ x : M, p • x = 0) (t : d.image.obj F ≅ d.constant.obj M) : P F := by
  let U := forget₂ (Rep.{w} R G) (ModuleCat.{w} R)
  let K := d.constant
  let Q : Rep.{w} R G → Prop := fun A =>
    ∀ (_ : Module.Finite R A) (hp : ∀ x : A, p • x = 0)
      (E : Sheaf J (ModuleCat.{w} R)) (e : d.image.obj E ≅ K.obj (U.obj A)),
      d.representation E (U.obj A)
        (torsion_of_nsmul_eq_zero (U.obj A) p (Nat.Prime.pos (Fact.out)) hp) e =
          A.ρ → P E
  have hQ : ∀ A : Rep.{w} R G, ∀ [Module.Finite R A],
      (∀ x : A, p • x = 0) → Q A := by
    intro A _ hp
    apply Rep.induction_finite_of_prime_nsmul_trivial_subobject p hG Q ?_ ?_ A hp
    · intro B _ _ hB hfinite hpB E e hρ
      let := hfinite
      let := hB
      let ht := torsion_of_nsmul_eq_zero (U.obj B) p (Nat.Prime.pos (Fact.out)) hpB
      have htriv (σ : G) (x : U.obj B) :
          d.representation E (U.obj B) ht e σ x = x := by
        rw [hρ]
        exact Representation.isTrivial_apply B.ρ σ x
      exact hiso (d.trivialActionIso E (U.obj B) ht e htriv) (hconstant (U.obj B) hpB)
    · intro S hS hfinite₁ hp₁ htriv₁ hquot hfinite₂ hp₂ E e hρ
      let := hfinite₁
      let := hfinite₂
      let := htriv₁
      let T := S.map U
      have hT : T.ShortExact := hS.map_of_exact U
      have : Mono S.f := hS.mono_f
      have : Epi S.g := hS.epi_g
      have : Epi T.g := hT.epi_g
      let ht := torsion_of_nsmul_eq_zero (U.obj S.X₂) p (Nat.Prime.pos (Fact.out)) hp₂
      have hfix (σ : G) (x : U.obj S.X₁) :
          d.representation E (U.obj S.X₂) ht e σ (T.f x) = T.f x := by
        rw [hρ]
        exact (Rep.hom_comm_apply S.f σ x).symm.trans
          (congrArg S.f (Representation.isTrivial_apply S.X₁.ρ σ x))
      let f := d.subobjectMap E (U.obj S.X₂) ht e T.f hfix
      let E' := cokernel f
      have : Mono T.f := hT.mono_f
      have hf : (ShortComplex.cokernelSequence f).ShortExact :=
        d.subobjectMap_shortExact E (U.obj S.X₂) ht e T.f hfix
      have hsurj : Function.Surjective S.g :=
        (Rep.epi_iff_surjective S.g).mp inferInstance
      have hfinite₃ : Module.Finite R S.X₃ :=
        Module.Finite.of_surjective S.g.hom.toLinearMap hsurj
      have hp₃ (x : S.X₃) : p • x = 0 := by
        obtain ⟨y, rfl⟩ := hsurj x
        rw [← map_nsmul, hp₂, map_zero]
      have : Mono (cokernel.desc T.f T.g T.zero) := hT.exact.mono_cokernelDesc
      have : IsIso (cokernel.desc T.f T.g T.zero) := isIso_of_mono_of_epi _
      let c : cokernel T.f ≅ U.obj S.X₃ := asIso (cokernel.desc T.f T.g T.zero)
      let e' : d.image.obj E' ≅ K.obj (U.obj S.X₃) :=
        d.subobjectCokernelIso E (U.obj S.X₂) ht e T.f hfix ≪≫ K.mapIso c
      have hprojection : d.image.map (cokernel.π f) ≫ e'.hom = e.hom ≫ K.map T.g := by
        change d.image.map (cokernel.π f) ≫
          ((d.subobjectCokernelIso E (U.obj S.X₂) ht e T.f hfix).hom ≫ K.map c.hom) = _
        rw [← Category.assoc, subobjectCokernelIso_projection, Category.assoc, ← K.map_comp]
        change e.hom ≫ K.map (cokernel.π T.f ≫ cokernel.desc T.f T.g T.zero) = _
        rw [cokernel.π_desc]
      let ht₃ := torsion_of_nsmul_eq_zero (U.obj S.X₃) p (Nat.Prime.pos (Fact.out)) hp₃
      have hρ₃ : d.representation E' (U.obj S.X₃) ht₃ e' = S.X₃.ρ := by
        ext σ x
        obtain ⟨y, rfl⟩ := hsurj x
        have hn := d.representation_naturality (hM := ht) ht₃ e'
          (cokernel.π f) T.g hprojection σ y
        rw [hρ] at hn
        exact hn.symm.trans (Rep.hom_comm_apply S.g σ y)
      exact hstep (ShortComplex.cokernelSequence f) hf (hconstant (U.obj S.X₁) hp₁)
        (hquot hfinite₃ hp₃ E' e' hρ₃)
  let ht := torsion_of_nsmul_eq_zero M p (Nat.Prime.pos (Fact.out)) hM
  exact hQ (Rep.of (d.representation F M ht t)) hM inferInstance hM F t rfl

end ModuleCoverData

end CategoryTheory.FiniteGroupAction
