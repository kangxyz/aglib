/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Schemes
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Proper
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Aglib.AlgebraicGeometry.Surfaces.Birational.IsomorphismLocus
public import Aglib.AlgebraicGeometry.Stalk.FlatBaseChange
public import Aglib.AlgebraicGeometry.FunctionField.Restriction
public import Aglib.AlgebraicGeometry.FunctionField.LocalSpectrum
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Aglib.AlgebraicGeometry.Properties.Regular.Basic

/-!
# Local replacement of an actual stalk modification

Let `X` be a normal integral Noetherian scheme of dimension at most two,
and let `x` be a closed nongeneric point. An actual normal integral proper
birational modification `p : T ⟶ Spec (X.presheaf.stalk x)` extends to an
actual proper modification `h : Y ⟶ X`, isomorphic over the complement of
`x`, with `T` in the original cartesian square over `X.fromSpecStalk x`.

The construction uses the original affine-neighbourhood section rings and
germ maps. Finite-presentation descent gives an actual stage model;
eventual properness and eventual isomorphy on the quasi-compact punctured
neighbourhoods refine that same model. Binary open gluing then constructs
`Y`, `h`, and the original localization comparison.

Normality of `Y` follows from actual stalk-map isomorphisms along the flat
preimmersion `X.fromSpecStalk x` and the identity away from `x`. The image
of the generic point of `T` proves irreducibility of `Y`. The original
function-field map of `h` is an isomorphism through the actual common open.
`LocalReplacement` is constructed output of `exists_localReplacement`;
no replacement diagram, finite normalization, excellence, rationality or
resolution premise is an input.

This is the geometric local-replacement step for global higher-direct-image
vanishing arguments. Flat localization of cohomology is a separate result.
The descent and gluing route is Stacks Tags 0B3X and 0BFN.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.LocalModification

universe u

/-- Eventual isomorphy for the structural morphism itself. The existing
descent theorem is for maps in `Over`; this retains the literal base-change
projection that is needed on punctured neighbourhoods. -/
theorem exists_isIso_structural_baseChange
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (q : i ⟶ j), IsAffineHom (D.map q)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {Z : Scheme.{u}} (f : Z ⟶ D.obj i)
    [LocallyOfFinitePresentation f] [QuasiCompact f]
    [IsIso (pullback.snd f (c.π.app i))] :
    ∃ j : Over i, IsIso (pullback.snd f (D.map j.hom)) := by
  let b : Over.mk f ⟶ Over.mk (𝟙 (D.obj i)) := Over.homMk f (by simp)
  have : IsIso ((Over.pullback (c.π.app i)).map b) := by
    have hw : ((Over.pullback (c.π.app i)).map b).left ≫
        pullback.snd (𝟙 (D.obj i)) (c.π.app i) = pullback.snd f (c.π.app i) :=
      Over.w ((Over.pullback (c.π.app i)).map b)
    have : IsIso (((Over.pullback (c.π.app i)).map b).left ≫
        pullback.snd (𝟙 (D.obj i)) (c.π.app i)) := by
      rw [hw]
      infer_instance
    have : IsIso (((Over.pullback (c.π.app i)).map b).left) :=
      IsIso.of_isIso_comp_right _ (pullback.snd (𝟙 (D.obj i)) (c.π.app i))
    have : IsIso ((Over.forget c.pt).map ((Over.pullback (c.π.app i)).map b)) := by
      simpa only [Over.forget_map] using
        (inferInstance : IsIso (((Over.pullback (c.π.app i)).map b).left))
    exact isIso_of_reflects_iso ((Over.pullback (c.π.app i)).map b) (Over.forget c.pt)
  obtain ⟨j, hj⟩ := Scheme.exists_isIso_baseChange_map_of_isLimit D c hc i f (𝟙 _) b
  let := hj
  have : IsIso (((Over.pullback (D.map j.hom)).map b).left) :=
    inferInstanceAs (IsIso ((Over.forget (D.obj j.left)).map
      ((Over.pullback (D.map j.hom)).map b)))
  have hw : ((Over.pullback (D.map j.hom)).map b).left ≫
      pullback.snd (𝟙 (D.obj i)) (D.map j.hom) = pullback.snd f (D.map j.hom) :=
    Over.w ((Over.pullback (D.map j.hom)).map b)
  refine ⟨j, ?_⟩
  rw [← hw]
  infer_instance

/-- Restrict an actual cartesian square, retaining the original restricted
structural map. This equivalence is used both at the limit and after rebasing. -/
theorem isIso_restrict_iff_pullback_snd {T Z S B : Scheme.{u}}
    (b : T ⟶ Z) (p : T ⟶ S) (q : Z ⟶ B) (c : S ⟶ B)
    (H : IsPullback b p q c) (U : B.Opens) (V : S.Opens)
    (hV : V = c ⁻¹ᵁ U) :
    IsIso (p ∣_ V) ↔ IsIso (pullback.snd (q ∣_ U) (c.resLE U V hV.le)) := by
  have hpre : p ⁻¹ᵁ V = b ⁻¹ᵁ (q ⁻¹ᵁ U) := by
    rw [hV, ← Scheme.Hom.comp_preimage, ← H.w, Scheme.Hom.comp_preimage]
  have HR := Scheme.Hom.isPullback_resLE H hV.le (le_refl (q ⁻¹ᵁ U))
    (UY := p ⁻¹ᵁ V) (by rw [← hpre]; exact (inf_idem _).symm)
  simp only [Scheme.Hom.resLE_eq_morphismRestrict] at HR
  constructor
  · intro hi
    let := hi
    rw [← HR.isoPullback_inv_snd]
    infer_instance
  · intro hi
    let := hi
    rw [← HR.isoPullback_hom_snd]
    infer_instance

/-- Actual affine open neighbourhoods of the specified original point. -/
abbrev AffineNeighborhood (X : Scheme.{u}) (x : X) :=
  { U : OpenNhds x // IsAffineOpen U.1 }

instance affineNeighborhood_isCofiltered (X : Scheme.{u}) (x : X) :
    IsCofiltered (AffineNeighborhood X x) where
  nonempty := by
    obtain ⟨U, hU, hxU, _⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (Opens.mem_top x)
    exact ⟨⟨⟨U, hxU⟩, hU⟩⟩
  cone_objs U V := by
    obtain ⟨W, hW, hxW, hWV⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ U.1.1 ⊓ V.1.1 from ⟨U.1.2, V.1.2⟩)
    refine ⟨⟨⟨W, hxW⟩, hW⟩, homOfLE ?_, homOfLE ?_, trivial⟩
    · exact hWV.trans inf_le_left
    · exact hWV.trans inf_le_right
  cone_maps {U V} f g := ⟨U, 𝟙 U, Subsingleton.elim _ _⟩

/-- Inclusion into all neighbourhoods, with the ordinary inclusion order. -/
def affineNeighborhoodInclusion (X : Scheme.{u}) (x : X) :
    AffineNeighborhood X x ⥤ OpenNhds x :=
  (Subtype.mono_coe _).functor

instance affineNeighborhoodInclusion_initial (X : Scheme.{u}) (x : X) :
    (affineNeighborhoodInclusion X x).Initial := by
  apply Functor.initial_of_exists_of_isCofiltered
  · intro V
    obtain ⟨U, hU, hxU, hUV⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens V.2
    exact ⟨⟨⟨U, hxU⟩, hU⟩, ⟨homOfLE hUV⟩⟩
  · intro V U f g
    exact ⟨U, 𝟙 U, Subsingleton.elim _ _⟩

/-- The original section rings and original restriction homomorphisms. -/
abbrev affineNeighborhoodRings (X : Scheme.{u}) (x : X) :
    (AffineNeighborhood X x)ᵒᵖ ⥤ CommRingCat.{u} :=
  (affineNeighborhoodInclusion X x).op ⋙
    ((OpenNhds.inclusion x).op ⋙ X.presheaf)

/-- Its point is definitionally the original stalk, and its maps are germs. -/
abbrev affineNeighborhoodStalkCocone (X : Scheme.{u}) (x : X) :
    Cocone (affineNeighborhoodRings X x) :=
  (colimit.cocone ((OpenNhds.inclusion x).op ⋙ X.presheaf)).whisker
    (affineNeighborhoodInclusion X x).op

def affineNeighborhoodStalkCoconeIsColimit (X : Scheme.{u}) (x : X) :
    IsColimit (affineNeighborhoodStalkCocone X x) :=
  (Functor.Final.isColimitWhiskerEquiv (affineNeighborhoodInclusion X x).op
    (colimit.cocone ((OpenNhds.inclusion x).op ⋙ X.presheaf))).symm
      (colimit.isColimit _)

/-- Affine schemes with the actual section rings. The double opposite is
kept explicitly to avoid replacing the original stalk cocone. -/
abbrev affineNeighborhoodDiagram (X : Scheme.{u}) (x : X) :
    (AffineNeighborhood X x)ᵒᵖᵒᵖ ⥤ Scheme.{u} :=
  (affineNeighborhoodRings X x).op ⋙ Scheme.Spec

/-- The point is literally `Spec (X.presheaf.stalk x)`. -/
abbrev affineNeighborhoodCone (X : Scheme.{u}) (x : X) :
    Cone (affineNeighborhoodDiagram X x) where
  pt := Spec (X.presheaf.stalk x)
  π :=
    { app i := Spec.map (X.presheaf.germ i.unop.unop.1.1 x i.unop.unop.1.2)
      naturality {i j} q := by
        change 𝟙 _ ≫ Spec.map (X.presheaf.germ j.unop.unop.1.1 x j.unop.unop.1.2) =
          Spec.map (X.presheaf.germ i.unop.unop.1.1 x i.unop.unop.1.2) ≫
            Spec.map (X.presheaf.map (homOfLE q.unop.unop.le).op)
        let ij : i.unop.unop.1.1 ⟶ j.unop.unop.1.1 := homOfLE q.unop.unop.le
        have hg : X.presheaf.map ij.op ≫
            X.presheaf.germ i.unop.unop.1.1 x i.unop.unop.1.2 =
              X.presheaf.germ j.unop.unop.1.1 x j.unop.unop.1.2 :=
          X.presheaf.germ_res ij x i.unop.unop.1.2
        exact (Category.id_comp _).trans
          ((congrArg (fun k : Γ(X, j.unop.unop.1.1) ⟶ X.presheaf.stalk x => Spec.map k)
            hg).symm.trans (Spec.map_comp _ _)) }

def affineNeighborhoodConeIsLimit (X : Scheme.{u}) (x : X) :
    IsLimit (affineNeighborhoodCone X x) := by
  change IsLimit (Scheme.Spec.mapCone (affineNeighborhoodStalkCocone X x).op)
  exact isLimitOfPreserves Scheme.Spec (affineNeighborhoodStalkCoconeIsColimit X x).op

instance affineNeighborhoodDiagram_isAffine (X : Scheme.{u}) (x : X)
    (i : (AffineNeighborhood X x)ᵒᵖᵒᵖ) :
    IsAffine ((affineNeighborhoodDiagram X x).obj i) :=
  inferInstanceAs (IsAffine (Spec Γ(X, i.unop.unop.1.1)))

instance affineNeighborhoodDiagram_isLocallyNoetherian (X : Scheme.{u})
    [IsLocallyNoetherian X] (x : X) (i : (AffineNeighborhood X x)ᵒᵖᵒᵖ) :
    IsLocallyNoetherian ((affineNeighborhoodDiagram X x).obj i) := by
  let : IsNoetherianRing Γ(X, i.unop.unop.1.1) :=
    IsLocallyNoetherian.component_noetherian ⟨i.unop.unop.1.1, i.unop.unop.2⟩
  exact inferInstanceAs (IsLocallyNoetherian (Spec Γ(X, i.unop.unop.1.1)))

/-- The specified affine identification followed by the actual open inclusion. -/
def affineNeighborhoodToBase (X : Scheme.{u}) (x : X)
    (i : (AffineNeighborhood X x)ᵒᵖᵒᵖ) :
    (affineNeighborhoodDiagram X x).obj i ⟶ X :=
  i.unop.unop.2.fromSpec

instance affineNeighborhoodToBase_isOpenImmersion (X : Scheme.{u}) (x : X)
    (i : (AffineNeighborhood X x)ᵒᵖᵒᵖ) :
    IsOpenImmersion (affineNeighborhoodToBase X x i) := by
  exact IsAffineOpen.isOpenImmersion_fromSpec i.unop.unop.2

@[reassoc]
theorem affineNeighborhoodCone_comp (X : Scheme.{u}) (x : X)
    (i : (AffineNeighborhood X x)ᵒᵖᵒᵖ) :
    (affineNeighborhoodCone X x).π.app i ≫ affineNeighborhoodToBase X x i =
      X.fromSpecStalk x := by
  change Spec.map (X.presheaf.germ i.unop.unop.1.1 x i.unop.unop.1.2) ≫
    i.unop.unop.2.fromSpec = X.fromSpecStalk x
  exact i.unop.unop.2.fromSpecStalk_eq_fromSpecStalk i.unop.unop.1.2

@[reassoc]
theorem affineNeighborhoodToBase_naturality (X : Scheme.{u}) (x : X)
    {i j : (AffineNeighborhood X x)ᵒᵖᵒᵖ} (q : i ⟶ j) :
    (affineNeighborhoodDiagram X x).map q ≫ affineNeighborhoodToBase X x j =
      affineNeighborhoodToBase X x i := by
  change Spec.map (X.presheaf.map (homOfLE q.unop.unop.le).op) ≫
    j.unop.unop.2.fromSpec = i.unop.unop.2.fromSpec
  exact j.unop.unop.2.map_fromSpec i.unop.unop.2 (homOfLE q.unop.unop.le).op

theorem affineNeighborhoodToBase_opensRange (X : Scheme.{u}) (x : X)
    (i : (AffineNeighborhood X x)ᵒᵖᵒᵖ) :
    (affineNeighborhoodToBase X x i).opensRange = i.unop.unop.1.1 :=
  i.unop.unop.2.opensRange_fromSpec

/-- A proper morphism over the original stalk has an actual proper model on
one affine neighbourhood. Neither normality nor punctured isomorphy is
assumed or claimed for this intermediate model. -/
theorem exists_proper_affineNeighborhood_model (X : Scheme.{u})
    [IsLocallyNoetherian X] (x : X) {T : Scheme.{u}}
    (p : T ⟶ Spec (X.presheaf.stalk x)) [IsProper p] :
    ∃ i : (AffineNeighborhood X x)ᵒᵖᵒᵖ,
      ∃ M : Scheme.FinitePresentationDescent.Model
          ((affineNeighborhoodCone X x).π.app i) p,
        IsProper M.f := by
  let D := affineNeighborhoodDiagram X x
  let c := affineNeighborhoodCone X x
  have hc : IsLimit c := affineNeighborhoodConeIsLimit X x
  have : IsLocallyNoetherian (Spec (X.presheaf.stalk x)) := inferInstance
  have : LocallyOfFinitePresentation p :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := p)).mpr inferInstance
  have : QuasiCompact p := inferInstance
  have : QuasiSeparated p := inferInstance
  obtain ⟨i, ⟨M⟩⟩ := Scheme.exists_model_of_isLimit_of_isAffine D c hc p
  have : LocallyOfFinitePresentation M.f := M.locallyOfFinitePresentation
  have : QuasiCompact M.f := M.quasiCompact
  have : QuasiSeparated M.f := M.quasiSeparated
  have : IsProper (pullback.fst (c.π.app i) M.f) := by
    rw [← M.rawIso_inv_struct]
    infer_instance
  obtain ⟨j, hj⟩ := Scheme.exists_isProper_baseChange_of_isLimit D c hc i M.f
  let := hj
  refine ⟨j.left, M.rebase D c i j, ?_⟩
  change IsProper (pullback.snd M.f (D.map j.hom))
  rw [← pullbackSymmetry_hom_comp_fst M.f (D.map j.hom)]
  infer_instance

/-- Restrict every actual neighbourhood to the same original open in X. -/
abbrev affineNeighborhoodOpenDiagram (X : Scheme.{u}) (x : X) (U : X.Opens) :
    (AffineNeighborhood X x)ᵒᵖᵒᵖ ⥤ Scheme.{u} where
  obj i := (affineNeighborhoodToBase X x i ⁻¹ᵁ U).toScheme
  map {i j} q := ((affineNeighborhoodDiagram X x).map q).resLE
    (affineNeighborhoodToBase X x j ⁻¹ᵁ U)
    (affineNeighborhoodToBase X x i ⁻¹ᵁ U) (by
      rw [← Scheme.Hom.comp_preimage, affineNeighborhoodToBase_naturality])
  map_id i := by
    apply (cancel_mono (affineNeighborhoodToBase X x i ⁻¹ᵁ U).ι).mp
    simp
  map_comp q r := by
    apply (cancel_mono (affineNeighborhoodToBase X x _ ⁻¹ᵁ U).ι).mp
    simp [Category.assoc]

abbrev affineNeighborhoodOpenDiagramι (X : Scheme.{u}) (x : X) (U : X.Opens) :
    affineNeighborhoodOpenDiagram X x U ⟶ affineNeighborhoodDiagram X x where
  app i := (affineNeighborhoodToBase X x i ⁻¹ᵁ U).ι
  naturality {i j} q := by
    simp [affineNeighborhoodOpenDiagram]

theorem affineNeighborhoodOpenDiagram_isPullback (X : Scheme.{u}) (x : X) (U : X.Opens)
    {i j : (AffineNeighborhood X x)ᵒᵖᵒᵖ} (q : i ⟶ j) :
    IsPullback ((affineNeighborhoodOpenDiagram X x U).map q)
      (affineNeighborhoodToBase X x i ⁻¹ᵁ U).ι
      (affineNeighborhoodToBase X x j ⁻¹ᵁ U).ι
      ((affineNeighborhoodDiagram X x).map q) := by
  apply IsOpenImmersion.isPullback
  · simp [affineNeighborhoodOpenDiagram]
  · simp only [Scheme.Opens.opensRange_ι, ← Scheme.Hom.comp_preimage,
      affineNeighborhoodToBase_naturality]

instance affineNeighborhoodOpenDiagram_map_isAffineHom (X : Scheme.{u})
    (x : X) (U : X.Opens) {i j : (AffineNeighborhood X x)ᵒᵖᵒᵖ} (q : i ⟶ j) :
    IsAffineHom ((affineNeighborhoodOpenDiagram X x U).map q) :=
  MorphismProperty.of_isPullback (affineNeighborhoodOpenDiagram_isPullback X x U q).flip
    inferInstance

instance affineNeighborhoodOpenDiagram_isLocallyNoetherian (X : Scheme.{u})
    [IsLocallyNoetherian X] (x : X) (U : X.Opens)
    (i : (AffineNeighborhood X x)ᵒᵖᵒᵖ) :
    IsLocallyNoetherian ((affineNeighborhoodOpenDiagram X x U).obj i) := by
  change IsLocallyNoetherian (affineNeighborhoodToBase X x i ⁻¹ᵁ U).toScheme
  infer_instance

instance affineNeighborhoodOpenDiagram_compactSpace (X : Scheme.{u})
    [IsLocallyNoetherian X] (x : X) (U : X.Opens)
    (i : (AffineNeighborhood X x)ᵒᵖᵒᵖ) :
    CompactSpace ((affineNeighborhoodOpenDiagram X x U).obj i) := by
  have : IsLocallyNoetherian ((affineNeighborhoodDiagram X x).obj i) :=
    affineNeighborhoodDiagram_isLocallyNoetherian X x i
  have : QuasiCompact (affineNeighborhoodToBase X x i ⁻¹ᵁ U).ι := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace
    (affineNeighborhoodToBase X x i ⁻¹ᵁ U).ι

/-- The point is the actual preimage of U in the original local spectrum. -/
abbrev affineNeighborhoodOpenCone (X : Scheme.{u}) (x : X) (U : X.Opens) :
    Cone (affineNeighborhoodOpenDiagram X x U) where
  pt := (X.fromSpecStalk x ⁻¹ᵁ U).toScheme
  π :=
    { app i := ((affineNeighborhoodCone X x).π.app i).resLE
        (affineNeighborhoodToBase X x i ⁻¹ᵁ U) (X.fromSpecStalk x ⁻¹ᵁ U) (by
          rw [← Scheme.Hom.comp_preimage, affineNeighborhoodCone_comp])
      naturality {i j} q := by
        apply (cancel_mono (affineNeighborhoodToBase X x j ⁻¹ᵁ U).ι).mp
        calc
          _ = (X.fromSpecStalk x ⁻¹ᵁ U).ι ≫ (affineNeighborhoodCone X x).π.app j := by
            exact (congrArg (· ≫ (affineNeighborhoodToBase X x j ⁻¹ᵁ U).ι)
              (Category.id_comp _)).trans
                (Scheme.Hom.resLE_comp_ι ((affineNeighborhoodCone X x).π.app j) _)
          _ = (X.fromSpecStalk x ⁻¹ᵁ U).ι ≫ (affineNeighborhoodCone X x).π.app i ≫
              (affineNeighborhoodDiagram X x).map q := by
            rw [(affineNeighborhoodCone X x).w q]
          _ = _ := by
            rw [Category.assoc, Scheme.Hom.resLE_comp_ι,
              Scheme.Hom.resLE_comp_ι_assoc] }

def affineNeighborhoodOpenConeIsLimit (X : Scheme.{u}) (x : X) (U : X.Opens) :
    IsLimit (affineNeighborhoodOpenCone X x U) := by
  let : IsConnected ((AffineNeighborhood X x)ᵒᵖᵒᵖ) := IsCofiltered.isConnected _
  apply isLimitOfIsPullbackOfIsConnected (affineNeighborhoodOpenDiagramι X x U)
    (affineNeighborhoodOpenCone X x U) (affineNeighborhoodCone X x)
    { hom := (X.fromSpecStalk x ⁻¹ᵁ U).ι
      w := by
        intro i
        exact (Scheme.Hom.resLE_comp_ι ((affineNeighborhoodCone X x).π.app i) _).symm }
  · intro i
    change IsPullback _ (X.fromSpecStalk x ⁻¹ᵁ U).ι
      (affineNeighborhoodToBase X x i ⁻¹ᵁ U).ι ((affineNeighborhoodCone X x).π.app i)
    apply IsOpenImmersion.isPullback
    · exact (Scheme.Hom.resLE_comp_ι ((affineNeighborhoodCone X x).π.app i) _).symm
    · simp only [Scheme.Opens.opensRange_ι, ← Scheme.Hom.comp_preimage]
      change ((affineNeighborhoodCone X x).π.app i ≫
        affineNeighborhoodToBase X x i) ⁻¹ᵁ U = X.fromSpecStalk x ⁻¹ᵁ U
      rw [affineNeighborhoodCone_comp]
  · exact affineNeighborhoodConeIsLimit X x

/-- Actual proper local data, isomorphic over the original inverse image of
U, produces a proper model whose entire overlap with U is an isomorphism.
The model and overlap isomorphism are conclusions, not caller premises. -/
theorem exists_proper_affineNeighborhood_model_isIso (X : Scheme.{u})
    [IsLocallyNoetherian X] (x : X) (U : X.Opens) {T : Scheme.{u}}
    (p : T ⟶ Spec (X.presheaf.stalk x)) [IsProper p]
    (hU : IsIso (p ∣_ X.fromSpecStalk x ⁻¹ᵁ U)) :
    ∃ i : (AffineNeighborhood X x)ᵒᵖᵒᵖ,
      ∃ M : Scheme.FinitePresentationDescent.Model
          ((affineNeighborhoodCone X x).π.app i) p,
        IsProper M.f ∧ IsIso (M.f ∣_ affineNeighborhoodToBase X x i ⁻¹ᵁ U) := by
  let D := affineNeighborhoodDiagram X x
  let c := affineNeighborhoodCone X x
  let E := affineNeighborhoodOpenDiagram X x U
  let e := affineNeighborhoodOpenCone X x U
  let V := X.fromSpecStalk x ⁻¹ᵁ U
  obtain ⟨i, M, hMproper⟩ := exists_proper_affineNeighborhood_model X x p
  let := hMproper
  let B := affineNeighborhoodToBase X x i ⁻¹ᵁ U
  have : LocallyOfFinitePresentation M.f := M.locallyOfFinitePresentation
  have : QuasiCompact M.f := M.quasiCompact
  have : LocallyOfFinitePresentation (M.f ∣_ B) := inferInstance
  have : QuasiCompact (M.f ∣_ B) := inferInstance
  have hV : V = c.π.app i ⁻¹ᵁ B := by
    exact (congrArg (fun k : Spec (X.presheaf.stalk x) ⟶ X => k ⁻¹ᵁ U)
      (affineNeighborhoodCone_comp X x i)).symm.trans
        (Scheme.Hom.comp_preimage (c.π.app i) (affineNeighborhoodToBase X x i) U)
  have : IsIso (pullback.snd (M.f ∣_ B) (e.π.app i)) :=
    (isIso_restrict_iff_pullback_snd M.p p M.f (c.π.app i) M.square B V hV).mp hU
  obtain ⟨j, hj⟩ := exists_isIso_structural_baseChange E e
    (affineNeighborhoodOpenConeIsLimit X x U) i (M.f ∣_ B)
  let N := M.rebase D c i j
  let B' := affineNeighborhoodToBase X x j.left ⁻¹ᵁ U
  have hB' : B' = D.map j.hom ⁻¹ᵁ B := by
    exact (congrArg (fun k : D.obj j.left ⟶ X => k ⁻¹ᵁ U)
      (affineNeighborhoodToBase_naturality X x j.hom)).symm.trans
        (Scheme.Hom.comp_preimage (D.map j.hom) (affineNeighborhoodToBase X x i) U)
  have hNiso : IsIso (N.f ∣_ B') := by
    apply (isIso_restrict_iff_pullback_snd
      (pullback.fst M.f (D.map j.hom)) (pullback.snd M.f (D.map j.hom))
      M.f (D.map j.hom) (IsPullback.of_hasPullback M.f (D.map j.hom)) B B' hB').mpr
    exact hj
  refine ⟨j.left, N, ?_, hNiso⟩
  change IsProper (pullback.snd M.f (D.map j.hom))
  infer_instance

/-- Output of actual binary gluing, retaining the neighbourhood chart. -/
structure GluedNeighborhood {X B Z : Scheme.{u}}
    (i : B ⟶ X) (U : X.Opens) (q : Z ⟶ B) where
  Y : Scheme.{u}
  h : Y ⟶ X
  j : Z ⟶ Y
  proper : IsProper h
  square : IsPullback j q h i
  isoRestriction : IsIso (h ∣_ U)

/-- Glue a proper neighbourhood model to the identity on the complementary
open using the original restricted structural isomorphism. -/
def glueNeighborhood {X B Z : Scheme.{u}} (i : B ⟶ X) [IsOpenImmersion i]
    (U : X.Opens) (hcover : ∀ x : X, x ∈ Set.range i ∨ x ∈ U)
    (q : Z ⟶ B) [IsProper q] (hO : IsIso (q ∣_ i ⁻¹ᵁ U)) :
    GluedNeighborhood i U q := by
  classical
  let O := i ⁻¹ᵁ U
  let A := q ⁻¹ᵁ O
  let := hO
  let C : Bool → Scheme.{u} := Bool.rec Z U.toScheme
  let r : ∀ b, A.toScheme ⟶ C b :=
    Bool.rec A.ι ((q ∣_ O) ≫ (i ∣_ U))
  let f : ∀ b, C b ⟶ X := Bool.rec (q ≫ i) U.ι
  have wr : r false ≫ f false = r true ≫ f true := by
    change A.ι ≫ (q ≫ i) = ((q ∣_ O) ≫ (i ∣_ U)) ≫ U.ι
    rw [Category.assoc, morphismRestrict_ι]
    change A.ι ≫ (q ≫ i) = (q ∣_ O) ≫ O.ι ≫ i
    exact (morphismRestrict_ι_assoc q O i).symm
  have hrOpen (b : Bool) : IsOpenImmersion (r b) := by
    cases b
    · change IsOpenImmersion A.ι
      infer_instance
    · change IsOpenImmersion ((q ∣_ O) ≫ (i ∣_ U))
      infer_instance
  let G := WidePushoutShape.wideSpan A.toScheme C r
  have {a b : WidePushoutShape Bool} (k : a ⟶ b) : IsOpenImmersion (G.map k) := by
    cases k with
    | id a =>
      change IsOpenImmersion (𝟙 _)
      infer_instance
    | init b =>
      change IsOpenImmersion (r b)
      exact hrOpen b
  let d : Cocone G := WidePushoutShape.mkCocone (r false ≫ f false) f (by
    intro b
    cases b
    · rfl
    · exact wr.symm)
  let Y := colimit G
  let h : Y ⟶ X := colimit.desc G d
  let jZ : Z ⟶ Y := colimit.ι G (some false)
  let jU : U.toScheme ⟶ Y := colimit.ι G (some true)
  have : IsOpenImmersion jZ := inferInstanceAs (IsOpenImmersion (colimit.ι G (some false)))
  have : IsOpenImmersion jU := inferInstanceAs (IsOpenImmersion (colimit.ι G (some true)))
  have hjZ : jZ ≫ h = q ≫ i := by
    change colimit.ι G (some false) ≫ colimit.desc G d = d.ι.app (some false)
    exact colimit.ι_desc d (some false)
  have hjU : jU ≫ h = U.ι := by
    change colimit.ι G (some true) ≫ colimit.desc G d = d.ι.app (some true)
    exact colimit.ι_desc d (some true)
  have hjZ_apply (z : Z) : h (jZ z) = i (q z) := by
    exact (Scheme.Hom.comp_apply jZ h z).symm.trans
      ((congrArg (fun k : Z ⟶ X => k z) hjZ).trans (Scheme.Hom.comp_apply q i z))
  have hjU_apply (u : U.toScheme) : h (jU u) = U.ι u := by
    exact (Scheme.Hom.comp_apply jU h u).symm.trans
      (congrArg (fun k : U.toScheme ⟶ X => k u) hjU)
  have hU_mem (u : U.toScheme) : U.ι u ∈ U :=
    (@Scheme.Opens.ι_apply X U u).symm ▸ u.2
  have hglue : A.ι ≫ jZ = ((q ∣_ O) ≫ (i ∣_ U)) ≫ jU := by
    change r false ≫ colimit.ι G (some false) = r true ≫ colimit.ι G (some true)
    exact (colimit.w G (.init false)).trans (colimit.w G (.init true)).symm
  have hYcover : ∀ y : Y, (∃ z : Z, jZ z = y) ∨ (∃ u : U.toScheme, jU u = y) := by
    intro y
    obtain ⟨k, z, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective G y
    cases k with
    | none =>
      left
      refine ⟨A.ι z, ?_⟩
      have hw : A.ι ≫ jZ = colimit.ι G none := by
        change G.map (.init false) ≫ colimit.ι G (some false) = colimit.ι G none
        exact colimit.w G (.init false)
      exact (Scheme.Hom.comp_apply A.ι jZ z).symm.trans
        (congrArg (fun v : A.toScheme ⟶ Y => v z) hw)
    | some b =>
      cases b
      · exact Or.inl ⟨z, rfl⟩
      · exact Or.inr ⟨z, rfl⟩
  have hpreB : h ⁻¹ᵁ i.opensRange = jZ.opensRange := by
    ext y
    change h y ∈ Set.range i ↔ y ∈ Set.range jZ
    constructor
    · intro hy
      rcases hYcover y with ⟨z, rfl⟩ | ⟨u, rfl⟩
      · exact ⟨z, rfl⟩
      · obtain ⟨b, hb⟩ := hy
        have hbu : i b = U.ι u := by
          exact hb.trans (hjU_apply u)
        have hbO : b ∈ O := by
          change i b ∈ U
          rw [hbu]
          exact hU_mem u
        obtain ⟨t, ht⟩ := (q ∣_ O).surjective ⟨b, hbO⟩
        have htu : ((q ∣_ O) ≫ (i ∣_ U)) t = u := by
          apply U.ι.injective
          rw [Scheme.Hom.comp_apply, ht]
          exact (morphismRestrict_base_coe i U ⟨b, hbO⟩).trans hbu
        refine ⟨A.ι t, ?_⟩
        have ht := congrArg (fun v : A.toScheme ⟶ Y => v t) hglue
        change jZ (A.ι t) = jU (((q ∣_ O) ≫ (i ∣_ U)) t) at ht
        exact ht.trans (congrArg jU htu)
    · rintro ⟨z, rfl⟩
      refine ⟨q z, ?_⟩
      exact (hjZ_apply z).symm
  have hpreU : h ⁻¹ᵁ U = jU.opensRange := by
    ext y
    change h y ∈ U ↔ y ∈ Set.range jU
    constructor
    · intro hy
      rcases hYcover y with ⟨z, rfl⟩ | ⟨u, rfl⟩
      · have hzA : z ∈ A := by
          change i (q z) ∈ U
          rwa [hjZ_apply z] at hy
        let t : A.toScheme := ⟨z, hzA⟩
        refine ⟨((q ∣_ O) ≫ (i ∣_ U)) t, ?_⟩
        exact (congrArg (fun v : A.toScheme ⟶ Y => v t) hglue).symm
      · exact ⟨u, rfl⟩
    · rintro ⟨u, rfl⟩
      exact (hjU_apply u).symm ▸ hU_mem u
  have HZ : IsPullback jZ q h i :=
    (IsOpenImmersion.isPullback q jZ i h hjZ hpreB).flip
  have HU : IsPullback jU (𝟙 U.toScheme) h U.ι := by
    apply (IsOpenImmersion.isPullback (𝟙 U.toScheme) jU U.ι h ?_ ?_).flip
    · simpa using hjU
    · simpa only [Scheme.Opens.opensRange_ι] using hpreU
  let Bc : Bool → Scheme.{u} := Bool.rec B U.toScheme
  let fc : ∀ b, Bc b ⟶ X := Bool.rec i U.ι
  let 𝒰 : X.OpenCover :=
    { I₀ := Bool
      X := Bc
      f := fc
      mem₀ := by
        rw [presieve₀_mem_precoverage_iff]
        refine ⟨?_, ?_⟩
        · intro x
          rcases hcover x with ⟨b, hb⟩ | hxU
          · exact ⟨false, b, hb⟩
          · exact ⟨true, ⟨x, hxU⟩, rfl⟩
        · intro b
          cases b <;> infer_instance }
  have hproper : IsProper h := by
    apply IsZariskiLocalAtTarget.of_openCover (P := @IsProper) 𝒰
    intro b
    cases b
    · change IsProper (pullback.snd h i)
      rw [← HZ.isoPullback_inv_snd]
      infer_instance
    · change IsProper (pullback.snd h U.ι)
      rw [← HU.isoPullback_inv_snd]
      infer_instance
  have hUiso : IsIso (h ∣_ U) := by
    have : IsIso (pullback.snd h U.ι) := by
      rw [← HU.isoPullback_inv_snd]
      infer_instance
    change IsIso ((pullbackRestrictIsoRestrict h U).inv ≫ pullback.snd h U.ι)
    infer_instance
  exact { Y := Y, h := h, j := jZ, proper := hproper, square := HZ, isoRestriction := hUiso }

/-- The actual complement of the given closed point. -/
def pointComplement {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X)) : X.Opens :=
  ⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩

theorem fromSpecStalk_preimage_pointComplement {X : Scheme.{u}}
    (x : X) (hx : IsClosed ({x} : Set X)) :
    X.fromSpecStalk x ⁻¹ᵁ pointComplement x hx =
      pointComplement (X := Spec (X.presheaf.stalk x))
        (IsLocalRing.closedPoint (X.presheaf.stalk x))
        (IsLocalRing.isClosed_singleton_closedPoint _) := by
  ext z
  change X.fromSpecStalk x z ≠ x ↔ z ≠ IsLocalRing.closedPoint (X.presheaf.stalk x)
  constructor
  · intro hz h
    apply hz
    rw [h, Scheme.fromSpecStalk_closedPoint]
  · intro hz h
    apply hz
    apply (X.fromSpecStalk x).isEmbedding.injective
    simpa only [Scheme.fromSpecStalk_closedPoint] using h

/-- This is the canonical local-spectrum morphism, not a chosen field map. -/
theorem fromSpecStalk_isDominant (X : Scheme.{u}) [IsIntegral X] (x : X) :
    IsDominant (X.fromSpecStalk x) :=
  Scheme.fromSpecStalk_isDominant X x

/-- Normality of the exact local spectrum from the original stalk maps. -/
theorem normalStalks_stalkSpec (X : Scheme.{u}) (hX : NormalStalks X) (x : X) :
    NormalStalks (Spec (X.presheaf.stalk x)) := by
  let : Flat (X.fromSpecStalk x) := Scheme.fromSpecStalk_flat X x
  intro z
  let : IsIso ((X.fromSpecStalk x).stalkMap z) :=
    Scheme.Hom.isIso_stalkMap_of_flat_of_surjectiveOnStalks (X.fromSpecStalk x) z
  let := (hX (X.fromSpecStalk x z)).1
  let := (hX (X.fromSpecStalk x z)).2
  let e := (asIso ((X.fromSpecStalk x).stalkMap z)).commRingCatIsoToRingEquiv
  exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩

theorem stalkSpec_dimension_le (X : Scheme.{u}) (x : X) :
    topologicalKrullDim (Spec (X.presheaf.stalk x)) ≤ topologicalKrullDim X :=
  (X.fromSpecStalk x).isEmbedding.isInducing.topologicalKrullDim_le

private theorem isIso_restrict_of_le {Y X : Scheme.{u}} (f : Y ⟶ X)
    (U V : X.Opens) (hUV : U ≤ V) (hV : IsIso (f ∣_ V)) : IsIso (f ∣_ U) := by
  let W : V.toScheme.Opens := V.ι ⁻¹ᵁ U
  have hW : IsIso ((f ∣_ V) ∣_ W) :=
    IsZariskiLocalAtTarget.restrict (P := .isomorphisms Scheme) hV W
  have himage : V.ι ''ᵁ W = U := by
    change V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hUV]
  have himageIso : IsIso (f ∣_ V.ι ''ᵁ W) :=
    ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict f V W)).mp hW
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictEq f himage)).mp himageIso

/-- A proper birational local surface modification is the identity on the
whole punctured spectrum. Source normality is unnecessary for this step. -/
theorem isIso_restrict_punctured_stalkSpec (X : Scheme.{u})
    [IsIntegral X] [IsNoetherian X] (hX : NormalStalks X)
    (hdim : topologicalKrullDim X ≤ 2) (x : X)
    {T : Scheme.{u}} [IsIntegral T]
    (p : T ⟶ Spec (X.presheaf.stalk x)) [IsProper p] [IsDominant p]
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap p))) :
    IsIso (p ∣_ pointComplement (X := Spec (X.presheaf.stalk x))
      (IsLocalRing.closedPoint (X.presheaf.stalk x))
      (IsLocalRing.isClosed_singleton_closedPoint _)) := by
  let S := Spec (X.presheaf.stalk x)
  let V := pointComplement (X := S) (IsLocalRing.closedPoint (X.presheaf.stalk x))
    (IsLocalRing.isClosed_singleton_closedPoint _)
  have hnormal : NormalStalks S := normalStalks_stalkSpec X hX x
  have hdimS : topologicalKrullDim S ≤ 2 := (stalkSpec_dimension_le X x).trans hdim
  have hVL : V ≤ p.targetIsomorphismLocus := by
    intro z hz
    by_contra hnot
    have hclosed : IsClosed ({z} : Set S) :=
      p.isClosed_singleton_of_not_mem_targetIsomorphismLocus hff hnormal hdimS z hnot
    have hc : IsLocalRing.closedPoint (X.presheaf.stalk x) ∈ closure ({z} : Set S) :=
      specializes_iff_mem_closure.mp (IsLocalRing.specializes_closedPoint z)
    rw [hclosed.closure_eq] at hc
    exact hz (Set.mem_singleton_iff.mp hc).symm
  exact isIso_restrict_of_le p V p.targetIsomorphismLocus hVL
    p.isIso_restrict_targetIsomorphismLocus

/-- Every point of the central fibre lifts along the actual localization
square. This uses the actual closed point and does not assume surjectivity
of the localization morphism onto all of `X`. -/
theorem exists_preimage_over_center {X Y T : Scheme.{u}} (x : X)
    (a : T ⟶ Y) (p : T ⟶ Spec (X.presheaf.stalk x)) (h : Y ⟶ X)
    (H : IsPullback a p h (X.fromSpecStalk x)) (y : Y) (hy : h y = x) :
    ∃ t : T, a t = y ∧ p t = IsLocalRing.closedPoint (X.presheaf.stalk x) := by
  apply Scheme.exists_preimage_of_isPullback H y
    (IsLocalRing.closedPoint (X.presheaf.stalk x))
  simpa only [Scheme.fromSpecStalk_closedPoint] using hy

/-- The original projection, at every point of `T`, induces an isomorphism
of actual local rings. In particular this holds at every point over `x`. -/
theorem isIso_stalkMap_localization_projection {X Y T : Scheme.{u}} (x : X)
    (a : T ⟶ Y) (p : T ⟶ Spec (X.presheaf.stalk x)) (h : Y ⟶ X)
    (H : IsPullback a p h (X.fromSpecStalk x)) (t : T) :
    IsIso (a.stalkMap t) := by
  let : Flat (X.fromSpecStalk x) := Scheme.fromSpecStalk_flat X x
  let : Flat a := MorphismProperty.of_isPullback H.flip inferInstance
  let : IsPreimmersion a := MorphismProperty.of_isPullback H.flip inferInstance
  exact Scheme.Hom.isIso_stalkMap_of_flat_of_surjectiveOnStalks a t

/-- Compatibility is on the actual structure homomorphisms. The endpoint
ring isomorphisms therefore also induce the compatible residue maps. -/
def originalStalkArrowIso {X Y T : Scheme.{u}} (x : X)
    (a : T ⟶ Y) (p : T ⟶ Spec (X.presheaf.stalk x)) (h : Y ⟶ X)
    (H : IsPullback a p h (X.fromSpecStalk x)) (t : T) :
    Arrow.mk (h.stalkMap (a t)) ≅ Arrow.mk (p.stalkMap t) := by
  let : Flat (X.fromSpecStalk x) := Scheme.fromSpecStalk_flat X x
  exact Scheme.Hom.stalkMapIsoOfIsPullbackOfFlatOfPreimmersion H t

/-- Normality is derived from the off-centre identity and the original
localization square. It is not imposed on the spread-out model. -/
theorem normalStalks_of_local_replacement {X Y T : Scheme.{u}}
    (x : X) (hx : IsClosed ({x} : Set X)) (hX : NormalStalks X)
    (hT : NormalStalks T) (a : T ⟶ Y)
    (p : T ⟶ Spec (X.presheaf.stalk x)) (h : Y ⟶ X)
    (H : IsPullback a p h (X.fromSpecStalk x))
    (hU : IsIso (h ∣_ pointComplement x hx)) : NormalStalks Y := by
  let U := pointComplement x hx
  let := hU
  intro y
  by_cases hy : h y = x
  · obtain ⟨t, rfl, _⟩ := exists_preimage_over_center x a p h H y hy
    let : IsIso (a.stalkMap t) := isIso_stalkMap_localization_projection x a p h H t
    let := (hT t).1
    let := (hT t).2
    let e := (asIso (a.stalkMap t)).symm.commRingCatIsoToRingEquiv
    exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩
  · let z : (h ⁻¹ᵁ U).toScheme := ⟨y, hy⟩
    have hz : IsIso ((h ∣_ U).stalkMap z) := inferInstance
    let : IsIso (h.stalkMap y) :=
      ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
        (morphismRestrictStalkMap h U z)).mp hz
    let := (hX (h y)).1
    let := (hX (h y)).2
    let e := (asIso (h.stalkMap y)).commRingCatIsoToRingEquiv
    exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩

/-- Regularity of a supported replacement follows from the supplied resolved
local scheme and the unchanged regular complement. No absolute separatedness
or Noetherian hypothesis is used in this stalkwise transport. -/
theorem regularStalks_of_local_replacement {X Y T : Scheme.{u}}
    (x : X) (hx : IsClosed ({x} : Set X))
    (hUregular : RegularStalks (pointComplement x hx).toScheme)
    (hT : RegularStalks T) (a : T ⟶ Y)
    (p : T ⟶ Spec (X.presheaf.stalk x)) (h : Y ⟶ X)
    (H : IsPullback a p h (X.fromSpecStalk x))
    (hU : IsIso (h ∣_ pointComplement x hx)) : RegularStalks Y := by
  let U := pointComplement x hx
  let := hU
  intro y
  by_cases hy : h y = x
  · obtain ⟨t, rfl, _⟩ := exists_preimage_over_center x a p h H y hy
    let : IsIso (a.stalkMap t) := isIso_stalkMap_localization_projection x a p h H t
    let := hT t
    exact IsRegularLocalRing.of_ringEquiv
      (asIso (a.stalkMap t)).symm.commRingCatIsoToRingEquiv
  · let z : (h ⁻¹ᵁ U).toScheme := ⟨y, hy⟩
    have hV : RegularStalks (h ⁻¹ᵁ U).toScheme :=
      hUregular.of_isOpenImmersion (h ∣_ U)
    let := hV z
    exact IsRegularLocalRing.of_ringEquiv
      (asIso ((h ⁻¹ᵁ U).ι.stalkMap z)).symm.commRingCatIsoToRingEquiv

/-- One generic point is dense in both pieces. This excludes extra components
of the glued scheme, including components supported over the centre. -/
theorem isIntegral_of_local_replacement {X Y T : Scheme.{u}}
    [IsIntegral X] [IsIntegral T]
    (x : X) (hx : IsClosed ({x} : Set X)) (hxη : x ≠ genericPoint X)
    (hX : NormalStalks X) (hT : NormalStalks T)
    (a : T ⟶ Y) (p : T ⟶ Spec (X.presheaf.stalk x)) [IsDominant p]
    (h : Y ⟶ X) (H : IsPullback a p h (X.fromSpecStalk x))
    (hU : IsIso (h ∣_ pointComplement x hx)) : IsIntegral Y := by
  let U := pointComplement x hx
  let V := h ⁻¹ᵁ U
  let := hU
  let : Nonempty U := ⟨⟨genericPoint X, hxη.symm⟩⟩
  let : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  let : IsIntegral V.toScheme := IsIntegral.of_isIso (inv (h ∣_ U))
  let : IsDominant (X.fromSpecStalk x) := fromSpecStalk_isDominant X x
  let η : Y := a (genericPoint T)
  have hη : h η = genericPoint X := by
    calc
      h η = X.fromSpecStalk x (p (genericPoint T)) := by
        simpa only [η, Scheme.Hom.comp_apply] using
          congrArg (fun q : T ⟶ X => q (genericPoint T)) H.w
      _ = X.fromSpecStalk x (genericPoint (Spec (X.presheaf.stalk x))) := by
        rw [Scheme.map_genericPoint_of_isDominant T p]
      _ = genericPoint X := Scheme.map_genericPoint_of_isDominant _ _
  have hηU : h η ∈ U := by
    change h η ≠ x
    rw [hη]
    exact hxη.symm
  let ηV : V.toScheme := ⟨η, hηU⟩
  have hηV : ηV = genericPoint V.toScheme := by
    apply (h ∣_ U).injective
    apply U.ι.injective
    calc
      U.ι ((h ∣_ U) ηV) = h η := morphismRestrict_base_coe h U ηV
      _ = genericPoint X := hη
      _ = U.ι ((h ∣_ U) (genericPoint V.toScheme)) := by
        rw [genericPoint_eq_of_isOpenImmersion (h ∣_ U),
          genericPoint_eq_of_isOpenImmersion U.ι]
  have hspec : ∀ y : Y, η ⤳ y := by
    intro y
    by_cases hy : h y = x
    · obtain ⟨t, rfl, _⟩ := exists_preimage_over_center x a p h H y hy
      exact ((genericPoint_spec T).specializes (y := t) trivial).map a.continuous
    · let yV : V.toScheme := ⟨y, hy⟩
      have hz := ((genericPoint_spec V.toScheme).specializes (y := yV) trivial).map
        V.ι.continuous
      simpa only [← hηV, Scheme.Opens.ι_apply, ηV, yV] using hz
  have hdense : closure ({η} : Set Y) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    exact specializes_iff_mem_closure.mp (hspec y)
  have hirr : IsIrreducible (Set.univ : Set Y) := by
    rw [← hdense]
    exact (isIrreducible_singleton (x := η)).closure
  let : IrreducibleSpace Y :=
    { isPreirreducible_univ := hirr.2
      toNonempty := ⟨η⟩ }
  let : IsReduced Y := (normalStalks_of_local_replacement x hx hX hT a p h H hU).isReduced
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

/-- The inverse on the nonempty open forces dominance of the original `h`. -/
theorem isDominant_of_isIso_restrict {X Y : Scheme.{u}} [IsIntegral X]
    (h : Y ⟶ X) (U : X.Opens) [Nonempty U] (hU : IsIso (h ∣_ U)) :
    IsDominant h := by
  let := hU
  let : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  let j : U.toScheme ⟶ Y := inv (h ∣_ U) ≫ (h ⁻¹ᵁ U).ι
  have hj : j ≫ h = U.ι := by
    dsimp only [j]
    rw [Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  have : IsDominant (j ≫ h) := by
    rw [hj]
    exact Scheme.isDominant_of_isOpenImmersion U.ι
  exact IsDominant.of_comp j h

/-- The actual generic-point field map is invertible because the two open
inclusions and the original restricted map induce the same field triangle. -/
theorem functionFieldMap_isIso_of_isIso_restrict {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (h : Y ⟶ X) [IsDominant h]
    (U : X.Opens) [Nonempty U] (hU : IsIso (h ∣_ U)) :
    IsIso (CommRingCat.ofHom (Scheme.functionFieldMap h)) :=
  Scheme.functionFieldMap_isIso_of_isIso_restrict h U hU

/-- A supported proper replacement, retaining the caller's actual stalk map.
No integrality, normality, dimension or absolute separatedness is required. -/
structure StalkReplacement {X T : Scheme.{u}}
    (x : X) (hx : IsClosed ({x} : Set X))
    (p : T ⟶ Spec (X.presheaf.stalk x)) where
  Y : Scheme.{u}
  h : Y ⟶ X
  proper : IsProper h
  a : T ⟶ Y
  square : IsPullback a p h (X.fromSpecStalk x)
  isoRestriction : IsIso (h ∣_ pointComplement x hx)

/-- Spread an actual punctured-isomorphism proper stalk modification and glue
it to the identity. The square and the supported exceptional locus are outputs. -/
theorem exists_stalkReplacement (X : Scheme.{u}) [IsLocallyNoetherian X]
    (x : X) (hx : IsClosed ({x} : Set X)) {T : Scheme.{u}}
    (p : T ⟶ Spec (X.presheaf.stalk x)) [IsProper p]
    (hpU : IsIso (p ∣_ X.fromSpecStalk x ⁻¹ᵁ pointComplement x hx)) :
    Nonempty (StalkReplacement x hx p) := by
  let U := pointComplement x hx
  obtain ⟨i, M, hMproper, hMiso⟩ :=
    exists_proper_affineNeighborhood_model_isIso X x U p hpU
  let := hMproper
  let n := affineNeighborhoodToBase X x i
  have hcover : ∀ y : X, y ∈ Set.range n ∨ y ∈ U := by
    intro y
    by_cases hy : y = x
    · subst y
      left
      refine ⟨(affineNeighborhoodCone X x).π.app i
        (IsLocalRing.closedPoint (X.presheaf.stalk x)), ?_⟩
      calc
        n (((affineNeighborhoodCone X x).π.app i)
            (IsLocalRing.closedPoint (X.presheaf.stalk x))) =
            (((affineNeighborhoodCone X x).π.app i) ≫ n)
              (IsLocalRing.closedPoint (X.presheaf.stalk x)) :=
          (Scheme.Hom.comp_apply _ _ _).symm
        _ = X.fromSpecStalk x (IsLocalRing.closedPoint (X.presheaf.stalk x)) :=
          congrArg (fun k : Spec (X.presheaf.stalk x) ⟶ X =>
            k (IsLocalRing.closedPoint (X.presheaf.stalk x))) (affineNeighborhoodCone_comp X x i)
        _ = x := Scheme.fromSpecStalk_closedPoint
    · exact Or.inr hy
  let G := glueNeighborhood n U hcover M.f hMiso
  let a : T ⟶ G.Y := M.p ≫ G.j
  have H : IsPullback a p G.h (X.fromSpecStalk x) := by
    have H' : IsPullback a p G.h ((affineNeighborhoodCone X x).π.app i ≫ n) :=
      M.square.paste_horiz G.square
    rwa [affineNeighborhoodCone_comp] at H'
  refine ⟨?_⟩
  exact
    { Y := G.Y
      h := G.h
      proper := G.proper
      a := a
      square := H
      isoRestriction := G.isoRestriction }

/-- Constructed output for the caller's original local modification. All
geometric conditions are conclusions of `exists_localReplacement`. -/
structure LocalReplacement {X T : Scheme.{u}} [IsIntegral X]
    (x : X) (hx : IsClosed ({x} : Set X))
    (p : T ⟶ Spec (X.presheaf.stalk x)) where
  Y : Scheme.{u}
  integral : IsIntegral Y
  normal : NormalStalks Y
  h : Y ⟶ X
  proper : IsProper h
  dominant : IsDominant h
  a : T ⟶ Y
  square : IsPullback a p h (X.fromSpecStalk x)
  isoRestriction : IsIso (h ∣_ pointComplement x hx)
  fieldIso :
    let : IsIntegral Y := integral
    let : IsDominant h := dominant
    IsIso (CommRingCat.ofHom (Scheme.functionFieldMap h))

/-- A normal integral proper birational modification of the original stalk
at a closed nongeneric point of a normal Noetherian surface extends to an
actual proper birational modification of the original scheme, identical
off that point. Its normality, integrality and original function-field
isomorphism are derived from the constructed square and open restriction.
No normalization, excellence, rationality or resolution premise is used. -/
theorem exists_localReplacement (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (hX : NormalStalks X) (hdim : topologicalKrullDim X ≤ 2)
    (x : X) (hx : IsClosed ({x} : Set X)) (hxη : x ≠ genericPoint X)
    {T : Scheme.{u}} [IsIntegral T] (hT : NormalStalks T)
    (p : T ⟶ Spec (X.presheaf.stalk x)) [IsProper p] [IsDominant p]
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap p))) :
    Nonempty (LocalReplacement x hx p) := by
  let U := pointComplement x hx
  have hpU : IsIso (p ∣_ X.fromSpecStalk x ⁻¹ᵁ U) := by
    rw [fromSpecStalk_preimage_pointComplement]
    exact isIso_restrict_punctured_stalkSpec X hX hdim x p hff
  obtain ⟨G⟩ := exists_stalkReplacement X x hx p hpU
  let a := G.a
  have H : IsPullback a p G.h (X.fromSpecStalk x) := G.square
  have hnormal : NormalStalks G.Y :=
    normalStalks_of_local_replacement x hx hX hT a p G.h H G.isoRestriction
  let hIntegral : IsIntegral G.Y :=
    isIntegral_of_local_replacement x hx hxη hX hT a p G.h H G.isoRestriction
  let : Nonempty U := ⟨⟨genericPoint X, hxη.symm⟩⟩
  let hDominant : IsDominant G.h := isDominant_of_isIso_restrict G.h U G.isoRestriction
  have hField : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap G.h)) :=
    functionFieldMap_isIso_of_isIso_restrict G.h U G.isoRestriction
  exact ⟨{
    Y := G.Y
    integral := hIntegral
    normal := hnormal
    h := G.h
    proper := G.proper
    dominant := hDominant
    a := a
    square := H
    isoRestriction := G.isoRestriction
    fieldIso := hField }⟩

end AlgebraicGeometry.Scheme.LocalModification
