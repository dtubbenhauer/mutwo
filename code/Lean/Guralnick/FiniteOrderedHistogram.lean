import Mathlib.Data.Finset.Sort

/-! # A monotone finite sequence is determined by its histogram -/
noncomputable section
namespace Guralnick

theorem antitoneOn_eq_of_histogram {α β : Type*} [LinearOrder α] [LinearOrder β]
    (s : Finset α) (f g : α → β) (hf : AntitoneOn f s) (hg : AntitoneOn g s)
    (h : ∀ b, (s.filter (fun a => f a = b)).card = (s.filter (fun a => g a = b)).card) :
    ∀ a ∈ s, f a = g a := by
  classical
  have hm : s.val.map f = s.val.map g := by
    apply Multiset.ext.mpr
    intro b
    rw [Multiset.count_map,Multiset.count_map]
    simpa only [eq_comm] using h b
  let l := s.sort (· ≤ ·)
  have hp : (l.map f).Perm (l.map g) := by
    apply Multiset.coe_eq_coe.mp
    change Multiset.map f (↑l) = Multiset.map g (↑l)
    rw [show (↑l : Multiset α) = s.val from Finset.sort_eq _ _]
    exact hm
  have hsf : (l.map f).Sorted (· ≥ ·) := by
    change List.Pairwise _ (l.map f)
    rw [List.pairwise_map]
    exact (s.sort_sorted (· ≤ ·)).imp_of_mem (fun ha hb hab =>
      hf ((Finset.mem_sort (· ≤ ·)).mp ha) ((Finset.mem_sort (· ≤ ·)).mp hb) hab)
  have hsg : (l.map g).Sorted (· ≥ ·) := by
    change List.Pairwise _ (l.map g)
    rw [List.pairwise_map]
    exact (s.sort_sorted (· ≤ ·)).imp_of_mem (fun ha hb hab =>
      hg ((Finset.mem_sort (· ≤ ·)).mp ha) ((Finset.mem_sort (· ≤ ·)).mp hb) hab)
  have he := List.eq_of_perm_of_sorted hp hsf hsg
  intro a ha
  exact (List.map_inj_left.mp he) a ((Finset.mem_sort (· ≤ ·)).mpr ha)

end Guralnick
