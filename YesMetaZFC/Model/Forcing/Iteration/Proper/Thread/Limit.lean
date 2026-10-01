import YesMetaZFC.Model.Forcing.Iteration.Proper.Thread.Bounds
import YesMetaZFC.Model.Forcing.Iteration.Proper.Natural
import YesMetaZFC.Model.Forcing.Iteration.Proper.Model.Sequence
import YesMetaZFC.Model.SetTheory.Internal.Hereditary

/-! # 任意内部极限的实际主前缀序列

较短 N 区间的迭代引理沿真实共尾指标列使用。初始投影、稠密名称选择及内部
依赖递归均自动构造；极限为 γ=sup(N∩β)，不假定它等于 β 或属于 N。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem row_pr_limit_thread_l {ω δ F G b β χ H N α B R D V p τ K}
    (h : Row_system_d I δ F G b) (hN : Hsub_d I ω χ H N)
    (hFN : M.mem F N) (hGN : M.mem G N) (hωN : M.mem ω N)
    (hβ : M.IsLimitOrdinal β) (hβN : M.mem β N)
    (hPast : ∀ ξ, M.mem ξ N → M.mem ξ β → Row_pil_stage_d I F G b N ξ)
    (hD : Entry_d M β D F) (hV : Entry_d M β V G)
    (hαβ : M.mem α β) (hαN : M.mem α N) (hB : Entry_d M α B F) (hR : Entry_d M α R G)
    (hK : Row_quot_d I α B b D N K) (hτ : Name_d M B τ)
    (hτK : Mem_force_d M B R B p τ K) (hp : Mstr_d M B R B N p) :
    ∃ γ A E X Q x p₀ α₀ B₀ R₀,
      M.MemberSubset γ β ∧ (∀ ξ, M.mem ξ N → M.mem ξ β → M.mem ξ γ) ∧
      M.IsSetFunctionFromTo I A ω γ ∧ M.IsCofinalNondecreasingOrdinalSequence I A ω γ ∧
      (∀ i ξ, Entry_d M i ξ A → M.mem α ξ) ∧ M.IsSetFunctionFromTo I E ω N ∧
      (∀ i T, Entry_d M i T E → Dense_set_d M D V D T) ∧
      (∀ T, M.mem T N → Dense_set_d M D V D T → ∃ i, M.mem i ω ∧ Entry_d M i T E) ∧
      M.IsSetFunctionFromTo I Q ω X ∧ Entry_d M b x Q ∧
      Entry_d M b α₀ A ∧ Entry_d M α₀ B₀ F ∧ Entry_d M α₀ R₀ G ∧ KPair_d M x p₀ τ ∧
      M.IsRestrictionOf I p p₀ α ∧ Row_cut_lower_d I α B R b D N τ p α₀ R₀ p₀ ∧
      (∀ i y, Entry_d M i y Q → Row_pr_thread_d I F G b D N A i y) ∧
      (∀ i j y z, M.SuccessorOf j i → Entry_d M i y Q → Entry_d M j z Q →
        Row_pr_advance_d I F G b D V N A E i y z) ∧
      (∀ i j x y ξ ζ r η s θ, Entry_d M i x Q → Entry_d M j y Q →
        Entry_d M i ξ A → Entry_d M j ζ A → KPair_d M x r η → KPair_d M y s θ →
        M.MemberSubset ξ ζ → M.IsRestrictionOf I r s ξ) ∧ Row_pr_bounds_d I F G b D N A Q ∧
      (∀ i y ζ C T q σ, Entry_d M i y Q → Entry_d M i ζ A →
        Entry_d M ζ C F → Entry_d M ζ T G → KPair_d M y q σ → Row_cut_lower_d I α B R b D N τ p ζ T q) ∧
      ∀ r, M.mem r N → Row_d M β r → Row_supp_d I true ω r → Row_d M γ r := by
  obtain ⟨hω, hχ, hωχ, hH, hCount, c, J, d, S, hM, hSub, hElem⟩ := hN
  have htr := ZF.h_transitive_l I hZF hH
  have hDN := selem_entry_value_l I hM.2 htr hZF hω hSub hElem hFN hβN h.conditions.2.1.2 hD
  have hVN := selem_entry_value_l I hM.2 htr hZF hω hSub hElem hGN hβN h.relations.2.1.2 hV
  obtain ⟨C, γ, A, E, hC, hγ, hγβ, hA, hc, ha, hE, hd, he, hbound⟩ :=
    row_model_sequence_l hZFC hω hχ hωχ hH hM.2 hSub hElem hCount hωN hβ hβN hαβ hαN hDN (h.stages β D V hD hV).order
  have idx i ξ (hi : Entry_d M i ξ A) : M.mem ξ N ∧ M.mem ξ β := (hC ξ).mp (hA.output_mem_of_pairMember hi)
  have inc : Cc_increasing_d I A := by
    intro i j ξ ζ hij hi hj
    rcases hc.2.1.2 i (hA.input_mem_of_pairMember hi) j (hA.input_mem_of_pairMember hj) hij ξ ζ hi hj with he | hlt
    · exact he ▸ (fun _ h => h)
    · exact (hβ.1.mem (idx j ζ hj).2).transitive.memberSubset hlt
  obtain ⟨o, ho, hoω⟩ := hω.1.1
  have hob := hZFC.1.eq_of_same_members o b (fun i => iff_of_false (ho i) (h.empty i))
  have hbω := hob ▸ hoω
  obtain ⟨α₀, _, hα₀⟩ := hA.2.2 b hbω
  have hα₀δ := h.conditions.1.transitive β ((h.conditions.2.2 β).mpr ⟨D, hD⟩) α₀ (idx b α₀ hα₀).2
  obtain ⟨B₀, hB₀⟩ := (h.conditions.2.2 α₀).mp hα₀δ
  obtain ⟨R₀, hR₀⟩ := (h.relations.2.2 α₀).mp hα₀δ
  have hαα₀ := (hβ.1.mem (idx b α₀ hα₀).2).transitive.memberSubset (ha b α₀ hα₀)
  have s := h.stages α B R hB hR
  have t := h.stages α₀ B₀ R₀ hB₀ hR₀
  have k := h.links α α₀ B R B₀ R₀ hB hR hB₀ hR₀ hαα₀
  have l := h.links α₀ β B₀ R₀ D V hB₀ hR₀ hD hV (hβ.1.transitive.memberSubset (idx b α₀ hα₀).2)
  obtain ⟨σ, K', f, T, hσ, hK', hf, hT, happ, hσK, hτσ⟩ :=
    row_project_name_l hZF hω hχ.isLimitOrdinal hH hM.2 hSub hElem (idx b α₀ hα₀).1 hαα₀ s l hK hτ hτK
  obtain ⟨p₀, hp₀, hpre, hmaster, hlower⟩ :=
    hPast α₀ (idx b α₀ hα₀).1 (idx b α₀ hα₀).2 α B R B₀ R₀ hαN hαα₀ hB hR hB₀ hR₀ σ p K' hK' hσ hσK hp
  obtain ⟨g, hg⟩ := gname_exists_l hZF (k.mem b s.base)
  have hσg := row_quot_accept_l hZF s.order t.order k hσ hp₀ hpre hK' hσK hg hlower
  obtain ⟨K'', hK'', hτ', hτK'⟩ := row_quot_transfer_l hZF s t.order k hp₀ hpre hf hT hK hτ hσ hτK hτσ hg hσg
  obtain ⟨x, hx⟩ := (I).total p₀ τ
  have hx' : Row_pr_thread_d I F G b D N A b x := ⟨α₀, B₀, R₀, hα₀, hB₀, hR₀,
    p₀, τ, K'', hx, hmaster, hτ', hK'', hτK'⟩
  obtain ⟨X, Q, hQ, hz, hv, hs⟩ := row_pr_thread_l hZFC hω hχ.isLimitOrdinal hH hM.2 hSub hElem
    h hD hV hFN hGN hDN hVN hA idx inc (fun i ξ hi => hPast ξ (idx i ξ hi).1 (idx i ξ hi).2) hE hd hx'
  have low := row_cut_project_l hZF hω hχ.isLimitOrdinal hH hM.2 hSub hElem (idx b α₀ hα₀).1 hαα₀ s hf happ hlower
  have leβ i ξ (hi : Entry_d M i ξ A) := hβ.1.transitive.memberSubset (idx i ξ hi).2
  have bounds := row_pr_bounds_l hZF hω h hD hV hA inc leβ hQ hv hs
  have original := row_pr_bound_l hZF hω h hD hV hA inc leβ hQ hv hs hB hR hτ hz hα₀ hR₀ hx hαα₀ hpre low
  have zero i (hi : M.mem i ω) : M.mem b i ∨ b = i := by
    rcases (hω.isOrdinal hZF).wellOrder.linear.compare b hbω i hi with he | hb | hi
    · exact Or.inr (hZFC.1.eq_of_same_members b i he)
    · exact Or.inl hb
    · exact (h.empty i hi).elim
  exact ⟨γ, A, E, X, Q, x, p₀, α₀, B₀, R₀, hγβ, fun ξ hn hb => hγ.2.1 ξ ((hC ξ).mpr ⟨hn, hb⟩),
    hA.mono_target_l I hγ.2.1, hc, ha, hE, hd, he, hQ, hz, hα₀, hB₀, hR₀, hx, hpre, low, hv, hs,
    row_pr_coherent_l hZF hω h hA inc hQ hv hs, bounds,
    (fun i y ζ C T q σ hy hζ hC hT hyq => original i y ζ C T q σ (zero i (hQ.input_mem_of_pairMember hy)) hy hζ hC hT hyq), hbound⟩

end YesMetaZFC.Model.Forcing.Internal
