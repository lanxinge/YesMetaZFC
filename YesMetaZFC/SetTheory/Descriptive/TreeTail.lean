import YesMetaZFC.SetTheory.Descriptive.TreeCons

/-! # 内部有限地址的首尾分解

首尾分解由内部后继坐标的函数图构造，不对外部自然数长度递归。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem tree_empty_domain_l (hE : Extensional M) {z t X} (hz : ∀ x, ¬ M.mem x z)
    (ht : M.IsSetFunctionFromTo I t z X) : t = z := by
  apply hE.eq_of_same_members
  intro p
  exact iff_of_false (fun hp => (ht.1.1 p hp).elim fun i ⟨x, hc⟩ =>
    hz i (ht.input_mem_of_pairMember ⟨p, hc, hp⟩)) (hz p)

/-- 空列或唯一的首项加尾列；尾列仍属于同一内部有限列空间。 -/
theorem cons_cases_l (hZF : M.Models ZF) {ω A z t} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hz : ∀ x, ¬ M.mem x z) (ht : M.mem t A) :
    t = z ∨ ∃ a s, M.mem a ω ∧ M.mem s A ∧ Cons_d I z a s t := by
  classical
  obtain ⟨n, hn, ht⟩ := (hA t).mp ht
  by_cases h0 : ∀ x, ¬ M.mem x n
  · have en := hZF.1.eq_of_same_members n z (fun x => iff_of_false (h0 x) (hz x))
    exact Or.inl (tree_empty_domain_l I hZF.1 hz (en ▸ ht))
  have hne : ∃ x, M.mem x n := Classical.byContradiction (fun h => h0 (fun x hx => h ⟨x, hx⟩))
  obtain ⟨m, hm, hnm⟩ := hω.exists_predecessor_of_mem_of_nonempty hZF hn hne
  obtain ⟨a, ha, hza⟩ := ht.2.2 z (Structure.IsOrdinal.empty_mem_of_nonempty
    (ZF.modelsKP hZF) ((hω.isOrdinal hZF).mem hn) hne hz)
  let ρ : Env M 1 := ⟨fun _ => t, fun _ => t⟩
  let φ : BinarySchema 1 := { body := .existsE (.conj (Formula.isSuccessor .newest (.bound 2))
    (Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 3))) }
  have hp i x : φ.denote ρ i x ↔ ∃ j, M.SuccessorOf j i ∧ M.PairMember I j x t := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_isSuccessor_iff, Formula.satisfies_orderedPairMem_iff I]; rfl
  obtain ⟨s, hs, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := m) (target := ω)
    (by
      intro i hi
      obtain ⟨j, hj, _⟩ := hω.1.2 i (hω.transitive hZF m hm i hi)
      have hjn : M.mem j n := (tree_successor_le_l hZF hω hm hi hj).elim
        (fun e => e.symm ▸ hnm.predecessor_mem) (fun h => (hnm j).mpr (Or.inl h))
      obtain ⟨x, _, hx⟩ := ht.2.2 j hjn
      exact ⟨x, (hp i x).mpr ⟨j, hj, hx⟩⟩)
    (by
      intro i _ x y hx hy
      obtain ⟨j, hj, hx⟩ := (hp i x).mp hx
      obtain ⟨k, hk, hy⟩ := (hp i y).mp hy
      exact ht.1.2 j x y hx (Structure.SuccessorOf.eq hZF.1 hk hj ▸ hy))
    (fun i x _ hx => ((hp i x).mp hx).elim fun _ h => ht.output_mem_of_pairMember h.2)
  refine Or.inr ⟨a, s, ha, (hA s).mpr ⟨m, hm, hs⟩, ht.1.1, fun j x => ⟨?_, ?_⟩⟩
  · intro hx
    by_cases h0 : ∀ i, ¬ M.mem i j
    · have e := hZF.1.eq_of_same_members j z (fun i => iff_of_false (h0 i) (hz i))
      exact Or.inl ⟨e, ht.1.2 j x a hx (e.symm ▸ hza)⟩
    · have hne : ∃ i, M.mem i j := Classical.byContradiction (fun h => h0 (fun i hi => h ⟨i, hi⟩))
      have hj := ht.input_mem_of_pairMember hx
      obtain ⟨i, _, hji⟩ := hω.exists_predecessor_of_mem_of_nonempty hZF (hω.transitive hZF n hn j hj) hne
      have hin := ((hω.isOrdinal hZF).mem hn).transitive j hj i hji.predecessor_mem
      have hi : M.mem i m := ((hnm i).mp hin).elim id (fun e => by
        have ei := hZF.1.eq_of_same_members i m e
        have ej := Structure.SuccessorOf.eq hZF.1 (ei ▸ hji) hnm
        exact (KP.mem_irrefl_d (ZF.modelsKP hZF) n (ej ▸ hj)).elim)
      exact Or.inr ⟨i, (he i x).mpr ⟨hi, (hp i x).mpr ⟨j, hji, hx⟩⟩, hji⟩
  · rintro (⟨rfl, rfl⟩ | ⟨i, hi, hj⟩)
    · exact hza
    · obtain ⟨k, hk, hx⟩ := (hp i x).mp ((he i x).mp hi).2
      exact Structure.SuccessorOf.eq hZF.1 hk hj ▸ hx

theorem cons_ne_empty_l {z a s t : M.Domain} (hz : ∀ p, ¬ M.mem p z)
    (h : Cons_d I z a s t) : t ≠ z := by
  intro e
  obtain ⟨p, _, hp⟩ := (h.2 z a).mpr (Or.inl ⟨rfl, rfl⟩)
  exact hz p (e ▸ hp)

/-- 加首项后的节点直接接在根上，当且仅当其尾列为空。 -/
theorem cons_root_l (hZF : M.Models ZF) {ω A z a s t} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hz : ∀ x, ¬ M.mem x z) (hzω : M.mem z ω)
    (ha : M.mem a ω) (hs : M.mem s A) (ht : Cons_d I z a s t) : Step_d I ω z t ↔ s = z := by
  obtain ⟨n, hn, hs⟩ := (hA s).mp hs
  obtain ⟨k, hk, hkn, htf⟩ := cons_type_l I hZF hω hz ha hn hs ht
  rw [tree_step_iff_l I hZF hω hzω hk (ds_empty_fun_l I hz) htf]
  constructor
  · rintro ⟨hkz, _⟩
    have e := Structure.SuccessorOf.predecessor_eq hZF.1 ((hω.isOrdinal hZF).mem hn) hkn hkz
    exact tree_empty_domain_l I hZF.1 hz (e ▸ hs)
  · intro e
    have en := hs.2.1.eq hZF.1 (e.symm ▸ (ds_empty_fun_l I (X := ω) hz).2.1)
    exact ⟨en.trans e ▸ hkn, fun p hp => (hz p hp).elim⟩

end YesMetaZFC.SetTheory.Descriptive
