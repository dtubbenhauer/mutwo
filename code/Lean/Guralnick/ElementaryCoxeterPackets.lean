import Guralnick.FiniteBlocks
import Mathlib.Data.List.Scan

/-! # The actual interval partition determined by a list of packet sizes -/
noncomputable section
open scoped BigOperators
namespace Guralnick.ElementaryCoxeterPackets

def packet : (L : List ℕ) → Fin L.sum → Fin L.length
  | [],i => Fin.elim0 i
  | a::L,i => if h : i.val < a then ⟨0,by simp⟩ else
      (packet L ⟨i.val-a,by have hi := i.isLt; simp only [List.sum_cons] at hi; omega⟩).succ

def prefixSum (L : List ℕ) (b : Fin L.length) : ℕ := (L.take b.val).sum

theorem packet_spec (L : List ℕ) (i : Fin L.sum) :
    prefixSum L (packet L i) ≤ i.val ∧
      i.val < prefixSum L (packet L i) + L[(packet L i).val] := by
  induction L with
  | nil => exact Fin.elim0 i
  | cons a L ih =>
      by_cases hi : i.val < a
      · simp [packet,hi,prefixSum]
      · rw [packet,dif_neg hi]
        have hh := ih ⟨i.val-a,by have h := i.isLt; simp only [List.sum_cons] at h; omega⟩
        simp only [prefixSum,Fin.val_succ,List.take_succ_cons,List.sum_cons,
          List.getElem_cons_succ] at *
        omega

theorem prefixSum_end_le (L : List ℕ) (b : Fin L.length) :
    prefixSum L b + L[b.val] ≤ L.sum := by
  have ht := List.sum_take_add_sum_drop L (b.val+1)
  rw [List.sum_take_succ L b.val b.isLt] at ht
  exact Nat.le.intro ht

theorem interval_unique (L : List ℕ) (i : ℕ) (b c : Fin L.length)
    (hb : prefixSum L b ≤ i ∧ i < prefixSum L b + L[b.val])
    (hc : prefixSum L c ≤ i ∧ i < prefixSum L c + L[c.val]) : b = c := by
  induction L generalizing i with
  | nil => exact Fin.elim0 b
  | cons a L ih =>
      revert hb hc
      refine Fin.cases ?_ (fun b => ?_) b
      · refine Fin.cases ?_ (fun c => ?_) c
        · intro _ _; rfl
        · intro hb hc
          simp only [prefixSum,Fin.val_zero,List.take_zero,List.sum_nil,zero_add,
            List.getElem_cons_zero,Fin.val_succ,List.take_succ_cons,List.sum_cons] at hb hc
          omega
      · refine Fin.cases ?_ (fun c => ?_) c
        · intro hb hc
          simp only [prefixSum,Fin.val_zero,List.take_zero,List.sum_nil,zero_add,
            List.getElem_cons_zero,Fin.val_succ,List.take_succ_cons,List.sum_cons] at hb hc
          omega
        · intro hb hc
          apply congrArg Fin.succ
          apply ih (i-a) b c
          · simp only [prefixSum,Fin.val_succ,List.take_succ_cons,List.sum_cons,
              List.getElem_cons_succ] at hb
            dsimp [prefixSum]
            omega
          · simp only [prefixSum,Fin.val_succ,List.take_succ_cons,List.sum_cons,
              List.getElem_cons_succ] at hc
            dsimp [prefixSum]
            omega

theorem packet_eq_iff (L : List ℕ) (i : Fin L.sum) (b : Fin L.length) :
    packet L i = b ↔ prefixSum L b ≤ i.val ∧ i.val < prefixSum L b + L[b.val] := by
  constructor
  · intro h
    simpa only [h] using packet_spec L i
  · exact interval_unique L i.val (packet L i) b (packet_spec L i)

def fiberEquiv (L : List ℕ) (b : Fin L.length) :
    {i : Fin L.sum // packet L i = b} ≃ Fin L[b.val] where
  toFun i := ⟨i.val.val-prefixSum L b,by
    have h := (packet_eq_iff L i.val b).mp i.property
    omega⟩
  invFun j := ⟨⟨prefixSum L b+j.val,by have h := prefixSum_end_le L b; have := j.isLt; omega⟩,by
    apply (packet_eq_iff L _ b).mpr
    change prefixSum L b ≤ prefixSum L b+j.val ∧
      prefixSum L b+j.val < prefixSum L b+L[b.val]
    have := j.isLt
    omega⟩
  left_inv i := by
    apply Subtype.ext
    apply Fin.ext
    change prefixSum L b + (i.val.val-prefixSum L b) = i.val.val
    have h := (packet_eq_iff L i.val b).mp i.property
    omega
  right_inv j := by apply Fin.ext; simp

theorem fiber_card (L : List ℕ) (b : Fin L.length) :
    Nat.card {i : Fin L.sum // packet L i = b} = L[b.val] := by
  rw [Nat.card_congr (fiberEquiv L b)]
  simp

theorem sum_over_packets (L : List ℕ) (f : Fin L.length → ℕ) :
    (∑ i : Fin L.sum, f (packet L i)) = ∑ b : Fin L.length, L[b.val] * f b := by
  classical
  calc
    _ = ∑ x : (b : Fin L.length) × {i : Fin L.sum // packet L i=b}, f x.1 := by
      apply Fintype.sum_equiv (Equiv.sigmaFiberEquiv (packet L)).symm
      intro i
      rfl
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
        ← Nat.card_eq_fintype_card,fiber_card]
      simp

theorem unequal_fiber_count (L : List ℕ) (i : Fin L.sum) :
    (∑ j : Fin L.sum, if packet L i=packet L j ∧ i≠j then 1 else 0) =
      L[(packet L i).val]-1 := by
  classical
  rw [← Finset.card_filter]
  have he : Finset.univ.filter (fun j : Fin L.sum => packet L i=packet L j ∧ i≠j) =
      (Finset.univ.filter (fun j => packet L j=packet L i)).erase i := by
    ext j
    simp [eq_comm,and_comm]
  rw [he,Finset.card_erase_of_mem (by simp),← Fintype.card_subtype,
    ← Nat.card_eq_fintype_card,fiber_card]

theorem sum_packet_values (L : List ℕ) (f : ℕ → ℕ) :
    (∑ b : Fin L.length, f L[b.val]) = (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simpa [Fin.sum_univ_succ] using congrArg (fun x => f a+x) ih

/-- Ordered unequal pairs inside the same actual packet. -/
theorem ordered_pair_count (L : List ℕ) :
    (∑ i : Fin L.sum, ∑ j : Fin L.sum,
      if packet L i=packet L j ∧ i≠j then 1 else 0) =
      (L.map fun a => a*(a-1)).sum := by
  simp_rw [unequal_fiber_count]
  rw [sum_over_packets L (fun b => L[b.val]-1)]
  exact sum_packet_values L (fun a => a*(a-1))

theorem packet_monotone (L : List ℕ) : Monotone (packet L) := by
  induction L with
  | nil => intro i; exact Fin.elim0 i
  | cons a L ih =>
      intro i j hij
      have hij' : i.val ≤ j.val := hij
      by_cases hi : i.val < a
      · simp only [packet,dif_pos hi]
        change 0 ≤ _
        exact Nat.zero_le _
      · have hj : ¬j.val<a := by omega
        simp only [packet,dif_neg hi,dif_neg hj,Fin.succ_le_succ_iff]
        apply ih
        change i.val-a ≤ j.val-a
        omega

theorem scanl_add (L : List ℕ) (a b : ℕ) :
    L.scanl (·+·) (a+b) = (L.scanl (·+·) b).map (a+·) := by
  induction L generalizing b with
  | nil => simp [List.scanl]
  | cons x L ih =>
      simp only [List.scanl,List.map_cons]
      congr 1
      simpa only [Nat.add_assoc] using ih (b+x)

theorem scanl_zero_cons (a : ℕ) (L : List ℕ) :
    (a::L).scanl (·+·) 0 = 0 :: (L.scanl (·+·) 0).map (a+·) := by
  simpa only [List.scanl,zero_add,add_zero] using
    congrArg (List.cons 0) (scanl_add L a 0)

theorem zero_mem_scanl (L : List ℕ) : 0 ∈ L.scanl (·+·) 0 := by
  cases L <;> simp [List.scanl]

theorem sum_take_mem_scanl (L : List ℕ) (r : ℕ) :
    (L.take r).sum ∈ L.scanl (·+·) 0 := by
  induction L generalizing r with
  | nil => simp [List.scanl]
  | cons a L ih =>
      cases r with
      | zero => simpa using zero_mem_scanl (a::L)
      | succ r =>
          rw [scanl_zero_cons]
          apply List.mem_cons.mpr
          right
          exact List.mem_map.mpr ⟨(L.take r).sum,ih r,by simp⟩

theorem prefixSum_mem_scanl (L : List ℕ) (b : Fin L.length) :
    prefixSum L b ∈ L.scanl (·+·) 0 := sum_take_mem_scanl L b.val

theorem prefixSum_end_mem_scanl (L : List ℕ) (b : Fin L.length) :
    prefixSum L b+L[b.val] ∈ L.scanl (·+·) 0 := by
  simpa only [List.sum_take_succ L b.val b.isLt] using sum_take_mem_scanl L (b.val+1)

theorem scanl_le_sum (L : List ℕ) {r : ℕ} (hr : r ∈ L.scanl (·+·) 0) : r ≤ L.sum := by
  induction L generalizing r with
  | nil => simpa [List.scanl] using hr
  | cons a L ih =>
      rw [scanl_zero_cons] at hr
      rcases List.mem_cons.mp hr with h|h
      · subst r; exact Nat.zero_le _
      · obtain ⟨s,hs,rfl⟩ := List.mem_map.mp h
        simpa only [List.sum_cons] using Nat.add_le_add_left (ih hs) a

theorem mem_scanl_cons_iff (a : ℕ) (L : List ℕ) {r : ℕ} (hr : 0 < r) :
    r ∈ (a::L).scanl (·+·) 0 ↔ a ≤ r ∧ r-a ∈ L.scanl (·+·) 0 := by
  rw [scanl_zero_cons]
  simp only [List.mem_cons,List.mem_map]
  constructor
  · rintro (h|⟨s,hs,h⟩)
    · omega
    · refine ⟨by omega,?_⟩
      have he : r-a=s := by omega
      rwa [he]
  · rintro ⟨h,hs⟩
    exact Or.inr ⟨r-a,hs,by omega⟩

theorem adjacent_same_iff (L : List ℕ) (hpos : ∀ a ∈ L,0<a)
    (r : ℕ) (hr : r+1<L.sum) :
    packet L ⟨r,by omega⟩ = packet L ⟨r+1,hr⟩ ↔
      r+1 ∉ L.scanl (·+·) 0 := by
  induction L generalizing r with
  | nil => simp at hr
  | cons a L ih =>
      have ha : 0<a := hpos a (by simp)
      have hp : ∀ b∈L,0<b := by intro b hb; exact hpos b (by simp [hb])
      simp only [List.sum_cons] at hr
      rw [mem_scanl_cons_iff a L (by omega)]
      by_cases h₀ : r<a
      · by_cases h₁ : r+1<a
        · simp [packet,h₀,h₁,show ¬a≤r+1 by omega]
        · have he : r+1=a := by omega
          simp [packet,h₀,he,zero_mem_scanl,Fin.ext_iff]
      · have h₁ : ¬r+1<a := by omega
        have he : r+1-a=(r-a)+1 := by omega
        simpa only [packet,dif_neg h₀,dif_neg h₁,Fin.succ_inj,he,
          show a≤r+1 by omega,true_and] using ih hp (r-a) (by omega)

#print axioms packet_eq_iff
#print axioms fiber_card
#print axioms ordered_pair_count
#print axioms adjacent_same_iff

end Guralnick.ElementaryCoxeterPackets
