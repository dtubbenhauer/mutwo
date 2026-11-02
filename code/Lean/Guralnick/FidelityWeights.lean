import Guralnick.Weights

/-!
# Independent comparison with the manuscript's fundamental-weight formula

The manuscript first defines lambda=(c+2)eta_(j-1)+(p-c-3)eta_j+eta_m,
where eta_r=omega_r+omega_(N-r), eta_0=0 and c=m-j. This file
compares its Dynkin labels and full integral coordinates directly with the
actual vector used to select the representation in LiteratureTransfer.familyAlgebraic.
The eta vectors are also identified with the standard rational-coordinate
realization of the indicated fundamental weights.
No cohomological or KL hypothesis is used in this comparison.
-/
namespace Guralnick.FidelityWeights

/-- Dynkin labels of eta_r=omega_r+omega_(2m+1-r). Indices outside
1,...,2m contribute zero; in particular this gives eta_0=0. -/
def etaLabel (m r : ℕ) (i : Fin (2*m)) : ℤ :=
  (if i.val+1=r then 1 else 0) + (if i.val+1=2*m+1-r then 1 else 0)

theorem eta_zero (m : ℕ) (i : Fin (2*m)) : etaLabel m 0 i=0 := by
  have hi:=i.isLt
  simp [etaLabel,show i.val ≠ 2*m by omega]

/-- The primary displayed highest-weight formula in main.tex,
eq:application-weight, expressed in the fundamental-weight basis. -/
def manuscriptDynkin (m j p : ℕ) (i : Fin (2*m)) : ℤ :=
  (((m-j : ℕ) : ℤ)+2)*etaLabel m (j-1) i +
    ((p : ℤ)-(m-j : ℕ)-3)*etaLabel m j i + etaLabel m m i

theorem eta_rev (m r : ℕ) (hr : r ≤ m) (i : Fin (2*m)) :
    etaLabel m r i.rev=etaLabel m r i := by
  have hi:=i.isLt
  unfold etaLabel
  simp only [Fin.val_rev]
  split_ifs <;> norm_num <;> omega

theorem dynkin_rev (m j p : ℕ) (i : Fin (2*m)) :
    Weights.dynkin m j p i.rev=Weights.dynkin m j p i := by
  have hi:=i.isLt
  have he₁ : i.rev.castSucc=i.succ.rev := by apply Fin.ext; simp
  have he₂ : i.rev.succ=i.castSucc.rev := by apply Fin.ext; simp; omega
  unfold Weights.dynkin
  rw [he₁,he₂,Weights.coordinate_rev,Weights.coordinate_rev]
  ring

theorem manuscriptDynkin_rev {m j p : ℕ} (hj : j ≤ m) (i : Fin (2*m)) :
    manuscriptDynkin m j p i.rev=manuscriptDynkin m j p i := by
  unfold manuscriptDynkin
  rw [eta_rev m (j-1) (by omega),eta_rev m j hj,eta_rev m m (le_refl _)]

set_option maxHeartbeats 1000000 in
theorem dynkin_eq_manuscript_left {m j p : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    (i : Fin (2*m)) (hi : i.val<m) : Weights.dynkin m j p i=manuscriptDynkin m j p i := by
  have hi₀:=i.isLt
  unfold Weights.dynkin Weights.coordinate Weights.leftCoordinate manuscriptDynkin etaLabel
  simp only [Fin.coe_castSucc,Fin.val_succ]
  have h₁ : ¬i.val=m := by omega
  have h₂ : ¬i.val+1=2*m+1-(j-1) := by omega
  have h₃ : ¬i.val+1=2*m+1-j := by omega
  have h₄ : ¬i.val+1=2*m+1-m := by omega
  simp only [if_pos hi,if_neg h₁,if_neg h₂,if_neg h₃,if_neg h₄,add_zero]
  by_cases hmid : i.val+1=m
  · simp only [hmid,lt_self_iff_false,if_false,if_true,sub_zero]
    split_ifs <;> norm_num <;> omega
  · have his : i.val+1<m := by omega
    simp only [if_pos his,if_neg hmid]
    split_ifs <;> norm_num <;> omega

/-- Uniform equality of the actual module's Dynkin labels with the
manuscript's primary formula, including j=1 and the overlap j=m. -/
theorem dynkin_eq_manuscript {m j p : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    (i : Fin (2*m)) : Weights.dynkin m j p i=manuscriptDynkin m j p i := by
  by_cases hi : i.val<m
  · exact dynkin_eq_manuscript_left hm hj hjm i hi
  · have hrev : i.rev.val<m := by have hib:=i.isLt; simp only [Fin.val_rev]; omega
    have he:=dynkin_eq_manuscript_left (p:=p) hm hj hjm i.rev hrev
    simpa only [dynkin_rev,manuscriptDynkin_rev hjm] using he

/-- The m=2 examples stated at the end of the application section. -/
theorem m2_j1_labels (p : ℕ) :
    List.ofFn (Weights.dynkin 2 1 p)= [(p : ℤ)-4,1,1,(p : ℤ)-4] := by
  simp [Weights.dynkin,Weights.coordinate,Weights.leftCoordinate,List.ofFn_succ]
  constructor <;> ring

theorem m2_j2_labels (p : ℕ) :
    List.ofFn (Weights.dynkin 2 2 p)= [2,(p : ℤ)-2,(p : ℤ)-2,2] := by
  simp [Weights.dynkin,Weights.coordinate,Weights.leftCoordinate,List.ofFn_succ]

/-- Integral coordinates of eta_r: +1 on its first r positions and -1 on
its last r positions. For r <= m these packets are disjoint. -/
def etaCoordinate (m r : ℕ) (i : Fin (2*m+1)) : ℤ :=
  (if i.val<r then 1 else 0) - (if 2*m+1-r ≤ i.val then 1 else 0)

theorem etaCoordinate_zero (m : ℕ) (i : Fin (2*m+1)) :
    etaCoordinate m 0 i=0 := by
  simp [etaCoordinate,show ¬2*m+1 ≤ i.val by omega]

theorem etaCoordinate_rev (m r : ℕ) (hr : r ≤ m) (i : Fin (2*m+1)) :
    etaCoordinate m r i.rev = -etaCoordinate m r i := by
  have hi:=i.isLt
  unfold etaCoordinate
  simp only [Fin.val_rev]
  split_ifs <;> norm_num <;> omega

theorem etaCoordinate_sum (m r : ℕ) (hr : r ≤ m) :
    ∑ i, etaCoordinate m r i=0 := by
  have h:=Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (2*m+1)))
    (etaCoordinate m r)
  simp only [Fin.revPerm_apply,etaCoordinate_rev m r hr,Finset.sum_neg_distrib] at h
  omega

/-- Standard rational coordinates of the fundamental weight omega_r in
type A_(2m): the indicator of the first r entries minus r/(2m+1).
This also gives zero at r=0 and r=2m+1. -/
def fundamentalCoordinate (m r : ℕ) (i : Fin (2*m+1)) : ℚ :=
  (if i.val<r then 1 else 0) - (r : ℚ)/(2*m+1)

/-- The explicit integral eta vector really is omega_r+omega_(N-r)
in the standard rational sum-zero coordinate realization. -/
theorem etaCoordinate_eq_fundamental (m r : ℕ) (hr : r ≤ m) (i : Fin (2*m+1)) :
    (etaCoordinate m r i : ℚ)=
      fundamentalCoordinate m r i + fundamentalCoordinate m (2*m+1-r) i := by
  have hrn : r ≤ 2*m+1 := by omega
  have hc : ((2*m+1-r : ℕ) : ℚ)=(2*m+1 : ℚ)-r := by
    rw [Nat.cast_sub hrn]
    push_cast
    ring
  have hn : (2*m+1 : ℚ) ≠ 0 := by positivity
  unfold etaCoordinate fundamentalCoordinate
  rw [hc]
  by_cases h : i.val<2*m+1-r
  · have hn' : ¬2*m+1-r ≤ i.val := by omega
    simp only [if_pos h,if_neg hn',sub_zero]
    split_ifs <;> norm_num <;> field_simp <;> ring
  · have hp : 2*m+1-r ≤ i.val := by omega
    simp only [if_neg h,if_pos hp]
    split_ifs <;> norm_num <;> field_simp <;> ring

/-- The manuscript's weight expression as an actual integral root vector,
independently of the Dynkin-label comparison above. -/
def manuscriptCoordinate (m j p : ℕ) (i : Fin (2*m+1)) : ℤ :=
  (((m-j : ℕ) : ℤ)+2)*etaCoordinate m (j-1) i +
    ((p : ℤ)-(m-j : ℕ)-3)*etaCoordinate m j i + etaCoordinate m m i

theorem manuscriptCoordinate_rev {m j p : ℕ} (hj : j ≤ m) (i : Fin (2*m+1)) :
    manuscriptCoordinate m j p i.rev = -manuscriptCoordinate m j p i := by
  unfold manuscriptCoordinate
  rw [etaCoordinate_rev m (j-1) (by omega),etaCoordinate_rev m j hj,
    etaCoordinate_rev m m (le_refl _)]
  ring

theorem coordinate_eq_manuscript_left {m j p : ℕ}
    (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) (i : Fin (2*m+1)) (hi : i.val<m) :
    Weights.coordinate m j p i=manuscriptCoordinate m j p i := by
  unfold Weights.coordinate manuscriptCoordinate etaCoordinate
  simp only [if_pos hi,if_neg (show ¬2*m+1-(j-1) ≤ i.val by omega),
    if_neg (show ¬2*m+1-j ≤ i.val by omega),
    if_neg (show ¬2*m+1-m ≤ i.val by omega),sub_zero]
  unfold Weights.leftCoordinate
  split_ifs <;> norm_num <;> omega

/-- The actual root-lattice character selecting the representation is the
paper's primary highest-weight formula, not just a vector with matching labels. -/
theorem coordinate_eq_manuscript {m j p : ℕ}
    (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) (i : Fin (2*m+1)) :
    Weights.coordinate m j p i=manuscriptCoordinate m j p i := by
  by_cases hi : i.val<m
  · exact coordinate_eq_manuscript_left hm hj hjm i hi
  · by_cases hmid : i.val=m
    · simp [Weights.coordinate,manuscriptCoordinate,etaCoordinate,hmid,
        show ¬m<j-1 by omega,show ¬m<j by omega,
        show ¬2*m+1-(j-1) ≤ m by omega,show ¬2*m+1-j ≤ m by omega,
        show ¬2*m+1-m ≤ m by omega]
    · have hrev : i.rev.val<m := by have hb:=i.isLt; simp only [Fin.val_rev]; omega
      have he:=coordinate_eq_manuscript_left (p:=p) hm hj hjm i.rev hrev
      simpa only [Weights.coordinate_rev,manuscriptCoordinate_rev hjm,neg_inj] using he

end Guralnick.FidelityWeights
