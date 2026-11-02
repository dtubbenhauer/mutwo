import Guralnick.MainContributionSupport
import Guralnick.CanonicalOneLinePatterns
import Guralnick.CanonicalAuxiliaryMargins
import Guralnick.OneLineMargins

/-! # Discharging all three contribution bounds of the row-sum argument -/
noncomputable section
namespace Guralnick.WebLiterature
open Hecke ParabolicWeb Positivity CanonicalRowSum CanonicalMultiplicityBounds
open WindowPacketMatrix CanonicalMatrix CanonicalCorrection CanonicalChains
open CanonicalOneLinePatterns

variable {m : ℕ}

def Readout (hm : 2≤m) (y : AffinePermutation (2*m+1)) : Prop :=
  y=AffinePermutation.longest (2*m+1) ∨ (∃ j : Fin m, y=familyIndex hm j) ∨
    ∃ r : ℕ, r≤m ∧ y=CanonicalSpherical.index m r

variable (hm : 2≤m) (T : Theory (2*m+1)) (W : WebLiterature T)
include hm W

theorem reflection_readout (w y : AffinePermutation (2*m+1)) (hy : Readout hm y) :
    T.kl.standard.repr (T.kl.canonical (AffineReflection.reflect w)) y =
      T.kl.standard.repr (T.kl.canonical w) y := by
  rcases hy with rfl | ⟨j,rfl⟩ | ⟨r,hr,rfl⟩
  · exact PacketReflection.canonical_fixed_source hm T.kl W.diagram_invariance w
  · exact PacketReflection.canonical_at_family hm (by omega) (by omega)
      T.kl W.diagram_invariance w
  · exact PacketReflection.canonical_at_spherical hm T.kl W.diagram_invariance w r

theorem word_readout (x : Hecke.Algebra (2*m+1)) (w y : AffinePermutation (2*m+1))
    (hx : x=T.kl.canonical w ∨ x=T.kl.canonical (AffineReflection.reflect w))
    (hy : Readout hm y) :
    T.kl.standard.repr (T.kl.canonical w) y=T.kl.standard.repr x y := by
  rcases hx with rfl|rfl
  · rfl
  · exact (reflection_readout hm T W w y hy).symm

omit hm W in
theorem rank_positive_of_s (A : PacketMatrix m) (hs : A.s=1) : 1≤A.rank := by
  have h:=A.outer_columns
  unfold PacketMatrix.s at hs
  unfold PacketMatrix.rank
  omega

/-- Every non-full, non-marked surviving term is an actual strong or weak
one-line canonical word, possibly reflected, with its proved allowance. -/
theorem auxiliary_data (w : AffinePermutation (2*m+1)) (hs : Supported w)
    (hne : T.kl.canonical.repr W.raw w ≠ 0) (p : Pattern)
    (hp : Matches (packetMatrix m w hs) p) (hpfull : p≠.full) (hptwo : p≠.two)
    (hoff : ∀ j : Fin m, w≠familyIndex hm j) :
    ∃ r : Fin (2*m+1), 1≤r.val ∧ r.val<m ∧
      ((LowerBound (T.kl.canonical.repr W.raw w) (-((m : ℤ)-r.val-1)) ∧
        (oneLine T.kl W.longest W.parabolic (by omega) r ⟨m,by omega⟩=T.kl.canonical w ∨
         oneLine T.kl W.longest W.parabolic (by omega) r ⟨m,by omega⟩=
           T.kl.canonical (AffineReflection.reflect w))) ∨
       (LowerBound (T.kl.canonical.repr W.raw w) (-((m : ℤ)-r.val-2)) ∧
        (oneLine T.kl W.longest W.parabolic (by omega) r ⟨m+1,by omega⟩=T.kl.canonical w ∨
         oneLine T.kl W.longest W.parabolic (by omega) r ⟨m+1,by omega⟩=
           T.kl.canonical (AffineReflection.reflect w)))) := by
  have hl:=corank_positive_off_family hm T W w hs hne hoff
  have hbnd:=term_multiplicity_lowerBound hm T W w hs hne p hp hl
  have hmax:=term_maximal hm T W w hne
  have hlt : (rankNode w hs).val<m := by
    change (packetMatrix m w hs).rank<m
    unfold PacketMatrix.corank at hl
    omega
  cases p with
  | full => exact False.elim (hpfull rfl)
  | two => exact False.elim (hptwo rfl)
  | strong =>
    refine ⟨rankNode w hs,(packetMatrix m w hs).typeF_rank_positive hp.1,hlt,Or.inl ⟨?_,?_⟩⟩
    · exact hbnd
    · exact Or.inl (strong_canonical hm T W w hs hmax hp.1 hp.2.1 hp.2.2.1)
  | weak =>
    refine ⟨rankNode w hs,CanonicalOneLineLeading.rank_positive_of_weak w hs hp.2.2.1,
      hlt,Or.inr ⟨?_,?_⟩⟩
    · exact hbnd
    · exact Or.inl (weak_canonical hm T W w hs hmax hp.1 hp.2.1 hp.2.2.1 hp.2.2.2)
  | strongDual =>
    refine ⟨rankNode w hs,rank_positive_of_s _ hp.2.1,hlt,Or.inl ⟨?_,?_⟩⟩
    · exact hbnd
    · exact Or.inr (strongDual_canonical hm T W w hs hmax hp.1 hp.2.1 hp.2.2.1 hp.2.2.2)
  | weakDual =>
    refine ⟨rankNode w hs,rank_positive_of_s _ hp.2.1,hlt,Or.inr ⟨?_,?_⟩⟩
    · exact hbnd
    · exact Or.inr (weakDual_canonical hm T W w hs hmax hp.1 hp.2.1 hp.2.2.1 hp.2.2.2)

/-- All auxiliary terms vanish at the constant degree used to establish
multiplicity one for each member of the marked family. -/
theorem auxiliary_family_bound (j : Fin m) (w : AffinePermutation (2*m+1))
    (hoff : ∀ k : Fin m, w≠familyIndex hm k) :
    LowerBound (T.kl.canonical.repr W.raw w *
      T.kl.standard.repr (T.kl.canonical w) (familyIndex hm j)) 1 := by
  by_cases hz : T.kl.canonical.repr W.raw w=0
  · rw [hz,zero_mul]; intro e he; rfl
  obtain ⟨hs,p,hp⟩:=term_pattern hm T W w hz
  by_cases hpf : p=.full
  · subst p
    exact full_family_contribution hm T W w hs hz hp hoff j
  have hpt : p≠.two := by
    intro he; subst p
    obtain ⟨k,hk⟩:=two_is_family hm T W w hs hz hp
    exact hoff k hk
  obtain ⟨r,hr,hrm,hd⟩:=auxiliary_data hm T W w hs hz p hp hpf hpt hoff
  rcases hd with ⟨hb,hword⟩ | ⟨hb,hword⟩
  · rw [word_readout hm T W _ w _ hword (Or.inr (Or.inl ⟨j,rfl⟩))]
    exact OneLineSpecialization.strong_at_marked_margin T.kl W.longest W.parabolic
      W.convolution W.lattice_flags W.coordinates W.block_lengths W.finite_longest hm
      (by omega) (by omega) r ⟨m,by omega⟩ hr rfl hrm hb
  · rw [word_readout hm T W _ w _ hword (Or.inr (Or.inl ⟨j,rfl⟩))]
    exact OneLineSpecialization.weak_at_marked_margin T.kl W.longest W.parabolic
      W.convolution W.lattice_flags W.coordinates W.block_lengths W.finite_longest hm
      (by omega) (by omega) r ⟨m+1,by omega⟩ hr rfl hrm hb

/-- At every Z_r the non-spherical contribution has positive degree.
Marked terms use ordinary KL triangularity; one-line terms have degree ≥3. -/
theorem nonspherical_bound (r : ℕ) (hr : r<m-1) (w : AffinePermutation (2*m+1))
    (hoffZ : ∀ s<m-1, w≠CanonicalSpherical.index m s) :
    LowerBound (T.kl.canonical.repr W.raw w *
      T.kl.standard.repr (T.kl.canonical w) (CanonicalSpherical.index m r)) 1 := by
  by_cases hz : T.kl.canonical.repr W.raw w=0
  · rw [hz,zero_mul]; intro e he; rfl
  by_cases hf : ∃ j : Fin m, w=familyIndex hm j
  · obtain ⟨j,rfl⟩:=hf
    rw [family_term_one hm T W j hz,one_mul]
    apply T.kl.canonical_lower
    exact (CanonicalSpherical.family_disjoint hm (by omega) (by omega)).symm
  have hoff : ∀ j : Fin m, w≠familyIndex hm j := by simpa only [not_exists] using hf
  obtain ⟨hs,p,hp⟩:=term_pattern hm T W w hz
  have hpf : p≠.full := by
    intro he; subst p
    exact hoffZ _ (full_rank_lt hm T W w hs hz hp hoff) (full_is_spherical hm T W w hs hz hp)
  have hpt : p≠.two := by
    intro he; subst p
    obtain ⟨j,hj⟩:=two_is_family hm T W w hs hz hp
    exact hoff j hj
  obtain ⟨s,hs',hsm,hd⟩:=auxiliary_data hm T W w hs hz p hp hpf hpt hoff
  rcases hd with ⟨hb,hword⟩ | ⟨hb,hword⟩
  · rw [word_readout hm T W _ w _ hword (Or.inr (Or.inr ⟨r,by omega,rfl⟩))]
    exact lowerBound_mono (OneLineSpecialization.strong_at_spherical_margin T.kl W.longest W.parabolic
      W.convolution W.lattice_flags W.coordinates W.block_lengths W.finite_longest hm
      (by omega) s ⟨m,by omega⟩ hs' rfl hb) (by norm_num)
  · rw [word_readout hm T W _ w _ hword (Or.inr (Or.inr ⟨r,by omega,rfl⟩))]
    exact lowerBound_mono (OneLineSpecialization.weak_at_spherical_margin T.kl W.longest W.parabolic
      W.convolution W.lattice_flags W.coordinates W.block_lengths W.finite_longest hm
      (by omega) s ⟨m+1,by omega⟩ hs' rfl hb) (by norm_num)

/-- Every term outside the marked and full-spherical families is invisible
in degree one at the fixed source w0. -/
theorem auxiliary_source_bound (w : AffinePermutation (2*m+1))
    (hoff : ∀ j : Fin m, w≠familyIndex hm j)
    (hoffZ : ∀ r<m-1, w≠CanonicalSpherical.index m r) :
    LowerBound (T.kl.canonical.repr W.raw w *
      T.kl.standard.repr (T.kl.canonical w) (AffinePermutation.longest (2*m+1))) 3 := by
  by_cases hz : T.kl.canonical.repr W.raw w=0
  · rw [hz,zero_mul]; intro e he; rfl
  obtain ⟨hs,p,hp⟩:=term_pattern hm T W w hz
  have hpf : p≠.full := by
    intro he; subst p
    exact hoffZ _ (full_rank_lt hm T W w hs hz hp hoff) (full_is_spherical hm T W w hs hz hp)
  have hpt : p≠.two := by
    intro he; subst p
    obtain ⟨j,hj⟩:=two_is_family hm T W w hs hz hp
    exact hoff j hj
  obtain ⟨r,hr,hrm,hd⟩:=auxiliary_data hm T W w hs hz p hp hpf hpt hoff
  rcases hd with ⟨hb,hword⟩ | ⟨hb,hword⟩
  · rw [word_readout hm T W _ w _ hword (Or.inl rfl)]
    have hq:=CanonicalAuxiliaryMargins.source_lowerBound T.kl W.longest W.parabolic
      W.convolution W.lattice_flags W.block_lengths W.finite_longest
      (by omega) r ⟨m,by omega⟩ hr (by dsimp; omega)
    apply lowerBound_mono (lowerBound_mul hb hq)
    dsimp only
    push_cast
    omega
  · rw [word_readout hm T W _ w _ hword (Or.inl rfl)]
    have hq:=CanonicalAuxiliaryMargins.source_lowerBound T.kl W.longest W.parabolic
      W.convolution W.lattice_flags W.block_lengths W.finite_longest
      (by omega) r ⟨m+1,by omega⟩ hr (by dsimp; omega)
    apply lowerBound_mono (lowerBound_mul hb hq)
    dsimp only
    push_cast
    omega

end Guralnick.WebLiterature
