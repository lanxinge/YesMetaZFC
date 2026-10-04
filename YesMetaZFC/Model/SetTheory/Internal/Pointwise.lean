import YesMetaZFC.Model.SetTheory.Internal.PointwiseQuantifier

/-! # 任意内部公式程序的逐点解释

对原程序的内部长度作原公式归纳。每个状态都包含实际新程序和旧根到新根的
函数图；后继步追加原子、或非或存在量词的翻译。归纳不要求内部 ω 标准。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem pe_compile_bound_l {ω χ c d X R H S q D E F n b t}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ)
    (hH : H_d I χ H) (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (hn : Smem_d I d H S)
    (hq : Smap_d I ω c d X H q) (hD : M.mem D X) (hE : M.IsFunctionSpace I E ω X)
    (hF : Sfm_d I ω n F) (hb : M.mem b ω) (hB : Sbound_d I F b) (ht : M.SuccessorOf t b) :
    ∃ m G T, Pe_state_d I ω b t D X R E F n n m G T := by
  have htω : M.mem t ω := by
    obtain ⟨s, hs, hsω⟩ := hω.1.2 b hb
    exact (hZF.1.eq_of_same_members s t (fun i => (hs i).trans (ht i).symm)) ▸ hsω
  obtain ⟨u, hu, huω⟩ := hω.1.2 t htω
  obtain ⟨σ, hσ, hσω⟩ := hω.1.2 u huω
  have bt : M.MemberSubset b t := fun i hi => (ht i).mpr (Or.inl hi)
  have tu : M.MemberSubset t u := fun i hi => (hu i).mpr (Or.inl hi)
  have uσ : M.MemberSubset u σ := fun i hi => (hσ i).mpr (Or.inl hi)
  have bσ : M.MemberSubset b σ := fun i hi => uσ i (tu i (bt i hi))
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  obtain ⟨V, hV⟩ := seval_exists_l I hZF X R E F hF.2.1.1
  let ρ : Env M 9 := ⟨Fin.cases t (Fin.cases n (Fin.cases F (Fin.cases E (Fin.cases R
    (Fin.cases X (Fin.cases D (Fin.cases b (fun _ => ω)))))))), fun _ => ω⟩
  let φ : UnarySchema 9 := {
    body := .imp (Formula.subset .newest (.bound 2)) (.existsE (.existsE (.existsE
      (pe_state_m (𝒞 := kpair_convention_l) (.bound 12) (.bound 11) (.bound 4) (.bound 10)
        (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 3) (.bound 2) (.bound 1) .newest)))) }
  have hφ k : φ.denote ρ k ↔ (M.MemberSubset k n → ∃ m G T, Pe_state_d I ω b t D X R E F n k m G T) := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_imp_iff, Formula.satisfies_subset_iff,
      Formula.satisfies_exists_iff, pe_state_sat_l I hZF.1]
    rfl
  have build : ∀ k, M.mem k ω → M.MemberSubset k n → ∃ m G T, Pe_state_d I ω b t D X R E F n k m G T := by
    apply hω.induction (fun k => M.MemberSubset k n → ∃ m G T, Pe_state_d I ω b t D X R E F n k m G T)
    · obtain ⟨A, hA⟩ := ZF.separation_exists_d hZF φ ρ ω
      exact ⟨A, fun k => (hA k).trans (and_congr_right fun _ => hφ k)⟩
    · intro e he _
      have seq := Structure.IsSequenceOfLength.empty I he
      have empty : ∀ i j, ¬ M.PairMember I i j e := fun _ _ ⟨p, _, hp⟩ => he p hp
      exact ⟨e, e, e, ⟨num_mem_l hZF.1 hω (show Num_d 0 e from he), seq,
        fun i j h => (empty i j h).elim⟩, ⟨seq.2.1, seq.2.2, fun i hi => (he i hi).elim⟩,
        fun i j h => (empty i j h).elim⟩
    · intro k hk ih l hl hln
      have hkn := hln k hl.predecessor_mem
      obtain ⟨m, G, T, h⟩ := ih (fun i hi => hln i ((hl i).mpr (Or.inl hi)))
      obtain ⟨z, hz⟩ := (hF.2.1.2.2 k).mp hkn
      have step : ∃ v J r, Sbuild_d I ω m G v J r ∧ Pe_row_d I b t D X R E F n v J k r := by
        rcases hF.2.2 k z hz with ⟨i, j, hs, _, _⟩ | ⟨i, j, hs, _, _⟩ |
          ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, _, hj⟩
        · obtain ⟨hi, hj⟩ := hB.operands_l I hz hs
          exact pe_atom_step_l I hZF hω hF hV hX hm hE hB h.1 hz false hs hσω
            (uσ t hu.predecessor_mem) (bσ i hi) (bσ j hj)
        · obtain ⟨hi, hj⟩ := hB.operands_l I hz hs
          exact pe_atom_step_l I hZF hω hF hV hX hm hE hB h.1 hz true hs hσω
            (uσ t hu.predecessor_mem) (bσ i hi) (bσ j hj)
        · obtain ⟨a, ha, hia⟩ := h.2.1.2.2 i hi
          obtain ⟨v, hv, hjv⟩ := h.2.1.2.2 j hj
          exact pe_nor_step_l I hZF hω hF hV h.1 hz hs ha hv (h.2.2 i a hia) (h.2.2 j v hjv)
        · have hi := (hB.operands_l I hz hs).1
          obtain ⟨v, hv, hjv⟩ := h.2.1.2.2 j hj
          exact pe_ex_step_l hZFC hω hχ hωχ hH hX hm hn hq hD hE hF hV h.1 hz hs hv
            (h.2.2 j v hjv) hσω (bσ i hi) (uσ b (tu b ht.predecessor_mem)) hσ.predecessor_mem
            (fun e => ir b (e ▸ tu b ht.predecessor_mem)) (fun e => ir i (e ▸ tu i (bt i hi)))
            (fun e => ir i (e ▸ hi)) (fun e => ir i (e ▸ bt i hi))
      obtain ⟨v, J, r, hg, hr⟩ := step
      obtain ⟨U, hU⟩ := pe_state_append_l I hZF hω hk hl h hg hr
      exact ⟨v, J, U, hU⟩
  exact build n hF.1 (fun _ h => h)

/-- 自动取得支撑外参数槽，返回覆盖每一旧指令的实际翻译表。 -/
theorem pe_compile_l {ω χ c d X R H S q D E F n}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ)
    (hH : H_d I χ H) (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (hn : Smem_d I d H S)
    (hq : Smap_d I ω c d X H q) (hD : M.mem D X) (hE : M.IsFunctionSpace I E ω X)
    (hF : Sfm_d I ω n F) : ∃ b t m G T, M.mem b ω ∧ Sbound_d I F b ∧
      M.SuccessorOf t b ∧ M.mem t ω ∧ Pe_state_d I ω b t D X R E F n n m G T := by
  obtain ⟨b, hb, hB⟩ := sbound_exists_l I hZF hω hF
  obtain ⟨t, ht, htω⟩ := hω.1.2 b hb
  obtain ⟨m, G, T, h⟩ := pe_compile_bound_l hZFC hω hχ hωχ hH hX hm hn hq hD hE hF hb hB ht
  exact ⟨b, t, m, G, T, hb, hB, ht, htω, h⟩

end YesMetaZFC.SetTheory.Internal
