import Guralnick.MainPacketCoordinate
import Guralnick.FamilyDescents
import Guralnick.FamilyUpperMatrix
import Guralnick.CanonicalSpherical

/-! # The actual marked and full-spherical raw coordinates

These specialize the proved arbitrary-orbit gallery formula using the
independently checked affine windows. They discharge the original raw
coordinate inputs in the family multiplicity and descending correction.
-/
noncomputable section
namespace Guralnick.MainFamilyCoordinate
open Hecke ParabolicWeb WindowPacketMatrix MainPacketCoordinate OrbitMatrix

variable {m : ℕ} {c : WindowCoxeter (2*m+1)} (K : KLRealization c)
  (D : ∀ I : Index (2*m+1), LongestData c I) (L : Laws K D)

/-- The packet object from actual inverse-window residues is the marked
matrix specified in the manuscript. -/
theorem marked_entries {j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    (hs : Supported (Guralnick.Family.upper hm hj hjm)) :
    (packetMatrix m (Guralnick.Family.upper hm hj hjm) hs).entries =
      Guralnick.Family.prescribedArray m j := by
  funext i q
  exact (entries_eq_matrixEntry m _ i q).trans
    (Guralnick.Family.upper_matrixEntry_eq_prescribedArray hm hj hjm i q)

theorem marked_parameters {j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    (hs : Supported (Guralnick.Family.upper hm hj hjm)) :
    let A := packetMatrix m (Guralnick.Family.upper hm hj hjm) hs
    A.rank = j ∧ A.corank = (m-j : ℕ) ∧ A.a = 1 ∧ A.s = 1 ∧ A.beta = 0 ∧ A.delta = 1 := by
  dsimp only
  have he := marked_entries hm hj hjm hs
  norm_num [CanonicalMatrix.PacketMatrix.rank,CanonicalMatrix.PacketMatrix.corank,
    CanonicalMatrix.PacketMatrix.a,CanonicalMatrix.PacketMatrix.s,
    CanonicalMatrix.PacketMatrix.beta,CanonicalMatrix.PacketMatrix.delta,he,
    Guralnick.Family.prescribedArray,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Nat.cast_zero,Nat.cast_one] <;> omega

/-- Exact type-F coordinate at every member of the original family. -/
theorem marked_raw_coordinate {j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    (C : FlagConvolution.Input K D L) (G : GeneralLatticeFlagInput)
    (O : CoordinateInput (2*m+1)) (Q : ThreeColumnLengthInput c)
    (hblocks : FiniteBlocks.BlockLengthInput D)
    (hsource : FiniteBlocks.StandardFiniteLongestInput D) :
    K.standard.repr (Family.raw K D L) (Guralnick.Family.upper hm hj hjm) =
      normalize (CanonicalGallery.gap (m-j : ℕ) 1 1 0 1)
        (CanonicalGallery.count (m-j : ℕ) 1 1 0 1) := by
  let hs := Guralnick.Family.upper_supported hm hj hjm
  let A := packetMatrix m (Guralnick.Family.upper hm hj hjm) hs
  have hc := raw_packet_coordinate K D L hm C G O Q hblocks hsource
    (Guralnick.Family.upper hm hj hjm) hs (Guralnick.Family.upper_doubleMaximal hm hj hjm c)
  change K.standard.repr (Family.raw K D L) _ = normalize
    ((2*(m : ℤ)^2+2*m-3)-PeriodicMatrix.dimension (fun i j => (A.entries i j : ℤ)))
    (CanonicalGallery.count A.corank A.a A.s A.beta A.delta) at hc
  rw [A.raw_gap] at hc
  obtain ⟨_,hl,ha,hs',hb,hd⟩ := marked_parameters hm hj hjm hs
  dsimp only [A] at hc
  simpa only [hl,ha,hs',hb,hd] using hc

/-- Full-spherical indices have bounded inverse windings, directly from
 their actual explicit translation window. -/
theorem spherical_supported (r : ℕ) : Supported (CanonicalSpherical.index m r) := by
  intro i
  rw [CanonicalSpherical.index_inverse]
  simp only [CanonicalSpherical.index,AffinePermutation.mul_winding,
    AffinePermutation.longest_winding,Pi.zero_apply,zero_add,
    CanonicalSpherical.translation,AffinePermutation.longest_residue,Fin.revPerm_apply]
  unfold Guralnick.Family.winding
  split_ifs <;> norm_num

theorem spherical_entries {r : ℕ} (hr : r ≤ m)
    (hs : Supported (CanonicalSpherical.index m r)) :
    (packetMatrix m (CanonicalSpherical.index m r) hs).entries = CanonicalSpherical.array m r := by
  funext i q
  rw [show (packetMatrix m (CanonicalSpherical.index m r) hs).entries i q =
    entries m (CanonicalSpherical.index m r) i q from rfl,
    entries_eq_matrixEntry,CanonicalSpherical.index,matrixEntry_mul_longest,
    CanonicalSpherical.matrixEntry_eq_array hr]

theorem spherical_parameters {r : ℕ} (hr : r ≤ m)
    (hs : Supported (CanonicalSpherical.index m r)) :
    let A := packetMatrix m (CanonicalSpherical.index m r) hs
    A.rank = r ∧ A.corank = (m-r : ℕ) ∧ A.a = 0 ∧ A.s = 0 ∧ A.beta = 0 ∧ A.delta = 1 := by
  dsimp only
  have he := spherical_entries hr hs
  norm_num [CanonicalMatrix.PacketMatrix.rank,CanonicalMatrix.PacketMatrix.corank,
    CanonicalMatrix.PacketMatrix.a,CanonicalMatrix.PacketMatrix.s,
    CanonicalMatrix.PacketMatrix.beta,CanonicalMatrix.PacketMatrix.delta,he,
    CanonicalSpherical.array,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Nat.cast_zero,Nat.cast_one] <;> omega

/-- The full-spherical coordinate is precisely the smaller raw Y-polynomial
used in the original descending correction, uniformly including r=0. -/
theorem spherical_raw_coordinate (hm : 2 ≤ m) {r : ℕ} (hr : r ≤ m)
    (C : FlagConvolution.Input K D L) (G : GeneralLatticeFlagInput)
    (O : CoordinateInput (2*m+1)) (Q : ThreeColumnLengthInput c)
    (hblocks : FiniteBlocks.BlockLengthInput D)
    (hsource : FiniteBlocks.StandardFiniteLongestInput D) :
    K.standard.repr (Family.raw K D L) (CanonicalSpherical.index m r) =
      CanonicalFullCorrection.rawCoordinate (m-r) := by
  let hs := spherical_supported (m := m) r
  let A := packetMatrix m (CanonicalSpherical.index m r) hs
  have hw := CanonicalSpherical.index_doubleMaximal hr c
  have hmax : CanonicalSchur.DoubleMaximal c (Family.output m) (Family.source m)
      (CanonicalSpherical.index m r) :=
    ⟨fun i hi => hw.1 i (Family.output_source m hi),hw.2⟩
  have hc := raw_packet_coordinate K D L hm C G O Q hblocks hsource
    (CanonicalSpherical.index m r) hs hmax
  change K.standard.repr (Family.raw K D L) _ = normalize
    ((2*(m : ℤ)^2+2*m-3)-PeriodicMatrix.dimension (fun i j => (A.entries i j : ℤ)))
    (CanonicalGallery.count A.corank A.a A.s A.beta A.delta) at hc
  rw [A.raw_gap] at hc
  obtain ⟨_,hl,ha,hs',hb,hd⟩ := spherical_parameters hr hs
  dsimp only [A] at hc
  simp only [hl,ha,hs',hb,hd] at hc
  rw [GalleryCounting.count_source] at hc
  have he : CanonicalGallery.gap (m-r : ℕ) 0 0 0 1 = Gaussian.normalizationDegree (m-r) := by
    unfold CanonicalGallery.gap CanonicalGallery.codimension Gaussian.normalizationDegree
    ring
  rw [he] at hc
  exact hc

end Guralnick.MainFamilyCoordinate
