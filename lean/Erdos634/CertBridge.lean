import Erdos634.AreaDet
import Erdos634.SssCongruent

/-!
# The certified-search bridge, in one constructor

Erdős #634. Three files supply the three parts of the passage from a checked search certificate to
a `CongruentDissection`:

* `ConvexCover.ofCertificate` — (C2) containment and (C3) disjoint interiors, together with the
  area identity, give the pointwise covering that `Dissection` demands;
* `AreaDet.area_identity_of_det` — the **exact** identity `∑ᵢ |det tᵢ| = |det T|` gives that area
  identity, so no measure theory is left on the certificate side;
* `SssCongruent.congruent_of_dist_three` — equal side lengths give a genuine isometry of the plane,
  which is what `Tri.Congruent` demands.

`ofCert` puts them together. Its hypotheses are exactly the four checks a certificate performs, and
each is a statement about explicit coordinates: three distance equalities per piece, one
containment per piece, one separating inequality per pair, and one determinant sum.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.CertBridge

open Erdos634.Geometry MeasureTheory

/-- **A `CongruentDissection` from a search certificate.** -/
noncomputable def ofCert {N : ℕ} (target model : Tri) (tile : Fin N → Tri)
    (hd01 : ∀ i, dist ((tile i).pts 0) ((tile i).pts 1) = dist (model.pts 0) (model.pts 1))
    (hd12 : ∀ i, dist ((tile i).pts 1) ((tile i).pts 2) = dist (model.pts 1) (model.pts 2))
    (hd20 : ∀ i, dist ((tile i).pts 2) ((tile i).pts 0) = dist (model.pts 2) (model.pts 0))
    (hsub : ∀ i, (tile i).carrier ⊆ target.carrier)
    (hdisj : Pairwise fun i j =>
      Disjoint (interior (tile i).carrier) (interior (tile j).carrier))
    (hdet : ∑ i, |Erdos634.AreaDet.detTri (tile i)| = |Erdos634.AreaDet.detTri target|) :
    CongruentDissection N where
  toDissection := Erdos634.AreaDet.ofDetCertificate target tile hsub hdisj hdet
  model := model
  tiles_congruent := fun i =>
    Erdos634.SssCongruent.congruent_of_dist_three (hd01 i) (hd12 i) (hd20 i)

section
variable {N : ℕ} (target model : Tri) (tile : Fin N → Tri)
  (hd01 : ∀ i, dist ((tile i).pts 0) ((tile i).pts 1) = dist (model.pts 0) (model.pts 1))
  (hd12 : ∀ i, dist ((tile i).pts 1) ((tile i).pts 2) = dist (model.pts 1) (model.pts 2))
  (hd20 : ∀ i, dist ((tile i).pts 2) ((tile i).pts 0) = dist (model.pts 2) (model.pts 0))
  (hsub : ∀ i, (tile i).carrier ⊆ target.carrier)
  (hdisj : Pairwise fun i j =>
    Disjoint (interior (tile i).carrier) (interior (tile j).carrier))
  (hdet : ∑ i, |Erdos634.AreaDet.detTri (tile i)| = |Erdos634.AreaDet.detTri target|)

@[simp] theorem ofCert_target :
    (ofCert target model tile hd01 hd12 hd20 hsub hdisj hdet).target = target := rfl

@[simp] theorem ofCert_model :
    (ofCert target model tile hd01 hd12 hd20 hsub hdisj hdet).model = model := rfl

include hd01 hd12 hd20 hsub hdisj hdet in
/-- **The area equation that follows**: the target is `N` times the tile. This is the numerical
content the tables record, now a consequence rather than an assumption. -/
theorem ofCert_volume :
    volume target.carrier = (N : ENNReal) * volume model.carrier :=
  Erdos634.CongruentArea.congruentDissection_volume_target
    (ofCert target model tile hd01 hd12 hd20 hsub hdisj hdet)

end

end Erdos634.CertBridge
