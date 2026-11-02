/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.PresheafTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.AdditiveSections

/-! # Typed additive component transport -/

@[expose] public noncomputable section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

/-- Lift an actual additive map with the native universe lift functor. -/
abbrev liftSectionAddHom := @CategoryTheory.PresheafTransport.liftSectionAddHom

/-- Lift an actual additive equivalence with the native universe lift functor. -/
abbrev liftSectionAddIso := @CategoryTheory.PresheafTransport.liftSectionAddIso

/-- Construct additive natural transformations from their literal component equations. -/
abbrev sectionNatTrans := @CategoryTheory.PresheafTransport.sectionNatTrans

/-- Construct additive natural isomorphisms from their literal component equations. -/
abbrev sectionNatIso := @CategoryTheory.PresheafTransport.sectionNatIso

/-- Natural additive maps between original Type transports, including base restriction. -/
abbrev liftTransportHom := @CategoryTheory.PresheafTransport.liftTransportHom

/-- Natural additive equivalences between original Type transports. -/
abbrev liftTransportIso := @CategoryTheory.PresheafTransport.liftTransportIso

/-- Type naturality supplies the coherence for the specified additive equivalences. -/
abbrev liftTransportIsoOfTypeIso := @CategoryTheory.PresheafTransport.liftTransportIsoOfTypeIso

/-- Compare an original Type transport with a native additive presheaf, before value lift. -/
abbrev liftTransportNativeIso := @CategoryTheory.PresheafTransport.liftTransportNativeIso

/-- Same-site additive transport of the supplied component maps. -/
abbrev liftTransportHomSame := @CategoryTheory.PresheafTransport.liftTransportHomSame

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
