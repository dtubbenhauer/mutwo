import Guralnick.ElementaryCoxeterLongest

/-!
# Additive length at finite-parabolic coset minima

An omitted cyclic cut turns the actual subgroup into permutations of
ordered packets. A window without parabolic descents is increasing on
each packet. Multiplication therefore preserves every selected descent of
a subgroup element. Induction on its actual Coxeter length gives the
coset length formula, without a parabolic decomposition hypothesis.
-/

noncomputable section
namespace Guralnick.ParabolicCosetFactorization
open Hecke ParabolicWeb ElementaryCoxeterParabolic ElementaryCoxeterCutLength
open ElementaryCoxeterRotation ElementaryCoxeterLongest

variable {n : ℕ}

/-- Distinct residues have distinct actual affine-window entries. -/
theorem entry_injective [NeZero n] (w : AffinePermutation n) :
    Function.Injective w.entry := by
  intro i j h
  have hp : (w.residue i, w.winding i) = (w.residue j, w.winding j) := by
    apply (AffinePermutation.integerIndex n).injective
    simpa only [AffinePermutation.integerIndex_apply, AffinePermutation.entry] using h
  exact w.residue.injective (congrArg Prod.fst hp)

/-- At a selected adjacent edge, the packet label does not change. -/
theorem label_eq_of_selected (a : Fin n) (I : Index n) (i j : Fin n)
    (hij : i.val+1=j.val) (hs : (cutEquiv a).symm j ∈ I.val) :
    label a I i = label a I j := by
  classical
  have hj : j ∉ omittedCuts a I := by
    rintro hj
    obtain ⟨s,hs',he⟩ := Finset.mem_image.mp hj
    have hsj : s = (cutEquiv a).symm j := by
      apply (cutEquiv a).injective
      simpa using he
    exact Finset.mem_compl.mp hs' (hsj ▸ hs)
  apply congrArg Finset.card
  apply Finset.ext
  intro r
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hr,hri⟩
    exact ⟨hr,by have : r.val ≤ i.val := hri; change r.val ≤ j.val; omega⟩
  · rintro ⟨hr,hrj⟩
    refine ⟨hr,?_⟩
    have hne : r ≠ j := fun h => hj (h ▸ hr)
    have hne' : r.val ≠ j.val := fun h => hne (Fin.ext h)
    have : r.val ≤ j.val := hrj
    change r.val ≤ i.val
    omega

/-- No selected right descents means strict increase on each selected edge. -/
theorem label_entry_ascent [NeZero n] (c : WindowCoxeter n) (a : Fin n)
    (I : Index n) (w : AffinePermutation n)
    (hno : ∀ s ∈ I.val, ¬c.system.IsRightDescent w s)
    (i j : Fin n) (hij : i.val+1=j.val) (hp : label a I i=label a I j) :
    (rotation a w).entry i < (rotation a w).entry j := by
  have hij' : i < j := by change i.val<j.val; omega
  have hs := selected_edge a I i j hij' hp
  have hn : ¬c.system.IsRightDescent (rotation a w) j := by
    have h := hno _ hs
    simpa only [←rotation_right_descent c a w ((cutEquiv a).symm j),
      Equiv.apply_symm_apply] using h
  rw [c.finite_descent _ i j hij] at hn
  exact lt_of_le_of_ne (le_of_not_gt hn)
    (fun h => (ne_of_lt hij') (entry_injective _ h))

/-- Increasing adjacent entries imply increasing entries throughout a packet. -/
theorem increasing_on_label [NeZero n] (c : WindowCoxeter n) (a : Fin n)
    (I : Index n) (w : AffinePermutation n)
    (hno : ∀ s ∈ I.val, ¬c.system.IsRightDescent w s)
    (i j : Fin n) (hij : i<j) (hp : label a I i=label a I j) :
    (rotation a w).entry i < (rotation a w).entry j :=
  ElementaryCoxeterLengthBound.decreasing_on_label (γ := ℤᵒᵈ)
    (label a I) (label_monotone a I) (rotation a w).entry
    (label_entry_ascent c a I w hno) i j hij hp

/-- A subgroup element without any generating right descent is the identity. -/
theorem eq_one_of_no_right_descents (c : WindowCoxeter n) (I : Index n)
    (u : subgroup c I) (hno : ∀ s ∈ I.val, ¬c.system.IsRightDescent u.val s) :
    u.val = 1 := by
  obtain ⟨a,ha⟩ := exists_omitted I
  letI : NeZero n := ⟨Nat.ne_of_gt (Fin.pos a)⟩
  let σ := (rotation a u.val).residue
  have hσ : StrictMono σ := by
    intro i j hij
    by_cases hp : label a I i=label a I j
    · have h := increasing_on_label c a I u.val hno i j hij hp
      simpa [AffinePermutation.entry,rotated_zero_winding c a I ha u] using h
    · have hp' : label a I i < label a I j :=
        lt_of_le_of_ne (label_monotone a I (le_of_lt hij)) hp
      by_contra h
      have hle := label_monotone a I (le_of_not_gt h)
      change label a I ((rotation a u.val).residue j) ≤
        label a I ((rotation a u.val).residue i) at hle
      rw [label_preserved c a I ha u,label_preserved c a I ha u] at hle
      exact (not_le_of_gt hp') hle
  have he : (σ : Fin n → Fin n) = id := (hσ.range_inj strictMono_id).mp (by
    rw [σ.surjective.range_eq]
    exact Set.range_id.symm)
  apply (rotation a).injective
  rw [map_one]
  apply AffinePermutation.ext
  · apply Equiv.ext
    intro i
    exact congrFun he i
  · exact rotated_zero_winding c a I ha u

/-- A nonidentity element of the actual parabolic has a selected descent. -/
theorem exists_right_descent (c : WindowCoxeter n) (I : Index n)
    (u : subgroup c I) (hu : u.val ≠ 1) :
    ∃ s ∈ I.val, c.system.IsRightDescent u.val s := by
  by_contra h
  push_neg at h
  exact hu (eq_one_of_no_right_descents c I u h)

/-- Multiplication by a zero-winding window substitutes its literal residue. -/
theorem entry_mul_zero_right (x u : AffinePermutation n) (hu : u.winding=0)
    (i : Fin n) : (x*u).entry i = x.entry (u.residue i) := by
  simp [AffinePermutation.entry,AffinePermutation.mul_residue,
    AffinePermutation.mul_winding,Equiv.Perm.mul_apply,hu]

/-- A packet-increasing left factor preserves every selected right descent
of the parabolic right factor. -/
theorem right_descent_product (c : WindowCoxeter n) (I : Index n)
    (x : AffinePermutation n) (hx : ∀ s ∈ I.val, ¬c.system.IsRightDescent x s)
    (u : subgroup c I) (s : Fin n) (hs : s∈I.val)
    (hd : c.system.IsRightDescent u.val s) :
    c.system.IsRightDescent (x*u.val) s := by
  obtain ⟨a,ha⟩ := exists_omitted I
  letI : NeZero n := ⟨Nat.ne_of_gt (Fin.pos a)⟩
  let j := cutEquiv a s
  have hj0 : 0<j.val := by
    have hz : (cutEquiv a a).val=0 := by
      change (cutRank a a).val=0
      simp [cutRank]
    by_contra h
    have he : cutEquiv a s=cutEquiv a a := Fin.ext (by change j.val=_; omega)
    exact ha ((cutEquiv a).injective he ▸ hs)
  let i : Fin n := ⟨j.val-1,by have := j.isLt; omega⟩
  have hij : i.val+1=j.val := by change j.val-1+1=j.val; omega
  have hp : label a I i=label a I j :=
    label_eq_of_selected a I i j hij (by simpa only [j,Equiv.symm_apply_apply] using hs)
  have hrot : c.system.IsRightDescent (rotation a u.val) j :=
    (rotation_right_descent c a u.val s).mpr hd
  have he := (c.finite_descent (rotation a u.val) i j hij).mp hrot
  have hw := rotated_zero_winding c a I ha u
  have hr : (rotation a u.val).residue j < (rotation a u.val).residue i := by
    simpa [AffinePermutation.entry,hw] using he
  have hp' : label a I ((rotation a u.val).residue j)=
      label a I ((rotation a u.val).residue i) := by
    rw [label_preserved c a I ha u,label_preserved c a I ha u,hp]
  have hinc := increasing_on_label c a I x hx _ _ hr hp'
  apply (rotation_right_descent c a (x*u.val) s).mp
  rw [map_mul]
  apply (c.finite_descent _ i j hij).mpr
  simpa only [entry_mul_zero_right _ _ hw] using hinc

/-- Length is additive on the right of a window with no selected right
descents, for every actual element of the generated finite subgroup. -/
theorem length_mul_right_of_no_descents (c : WindowCoxeter n) (I : Index n)
    (x : AffinePermutation n) (hx : ∀ s ∈ I.val, ¬c.system.IsRightDescent x s)
    (u : subgroup c I) :
    c.system.length (x*u.val)=c.system.length x+c.system.length u.val := by
  have aux (r : ℕ) : ∀ u : subgroup c I, c.system.length u.val=r →
      c.system.length (x*u.val)=c.system.length x+c.system.length u.val := by
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro u hu
      by_cases hone : u.val=1
      · simp [hone]
      · obtain ⟨s,hs,hd⟩ := exists_right_descent c I u hone
        have hs' : c.system.simple s∈subgroup c I :=
          Subgroup.subset_closure ⟨s,hs,rfl⟩
        let v : subgroup c I := u*⟨c.system.simple s,hs'⟩
        have hv : c.system.length v.val+1=c.system.length u.val :=
          c.system.isRightDescent_iff.mp hd
        have hiv := ih (c.system.length v.val) (by omega) v rfl
        have hp := c.system.isRightDescent_iff.mp (right_descent_product c I x hx u s hs hd)
        have he : (x*u.val)*c.system.simple s=x*v.val := by
          change (x*u.val)*c.system.simple s=x*(u.val*c.system.simple s)
          exact mul_assoc _ _ _
        rw [he,hiv] at hp
        omega
  exact aux _ u rfl

/-- The exact coset-minimum length formula used by integral ideal inclusion.
The minimum concerns the actual finite left orbit, not a separately assumed
choice of distinguished representatives. -/
theorem length_mul_of_minimal (c : WindowCoxeter n) (I : Index n)
    (x : AffinePermutation n)
    (hmin : ∀ u : subgroup c I, c.system.length x ≤ c.system.length (u.val*x))
    (u : subgroup c I) :
    c.system.length (u.val*x)=c.system.length u.val+c.system.length x := by
  have hno : ∀ s∈I.val, ¬c.system.IsRightDescent x⁻¹ s := by
    intro s hs hd
    have hs' : c.system.simple s∈subgroup c I := Subgroup.subset_closure ⟨s,hs,rfl⟩
    have hm := hmin ⟨c.system.simple s,hs'⟩
    have hl : c.system.IsLeftDescent x s := c.system.isRightDescent_inv_iff.mp hd
    exact (not_lt_of_ge hm) hl
  have h := length_mul_right_of_no_descents c I x⁻¹ hno u⁻¹
  change c.system.length (x⁻¹*u.val⁻¹)=c.system.length x⁻¹+c.system.length u.val⁻¹ at h
  rw [←mul_inv_rev,c.system.length_inv,c.system.length_inv,c.system.length_inv] at h
  simpa only [Nat.add_comm] using h

#print axioms right_descent_product
#print axioms length_mul_of_minimal

end Guralnick.ParabolicCosetFactorization
