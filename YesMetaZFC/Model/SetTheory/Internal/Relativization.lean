import YesMetaZFC.Model.SetTheory.Internal.RelativizationSteps

/-! # 完整内部程序的统一限制编译

沿模型内部 ω 逐行追加翻译，维护旧根到新根的实际图及纯语法规则。
归纳性质是可分离的原公式，不要求内部程序可解码为宿主语法树。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem sr_state_append_l (hZF : M.Models ZF) {ω b F k m G T l v H z}
    (hω : M.IsOmega ω) (hk : M.mem k ω) (hl : M.SuccessorOf l k) (h : Sr_state_d I ω b F k m G T)
    (hg : Sbuild_d I ω m G v H z) (hz : ∀ c, M.PairMember I k c F → Sr_rule_d I b T H c z) :
    ∃ U, Sr_state_d I ω b F l v H U := by
  have hko := hω.members_areOrdinals hZF k hk
  have seq : M.IsSequenceOfLength I T k := ⟨hko, h.map.1, h.map.2.1⟩
  obtain ⟨U, hU, val⟩ := seq.exists_append (ZF.modelsKP hZF) I
    (KP.successor_isOrdinal (ZF.modelsKP hZF) hko hl) hl (value := z)
  have into i j (h : M.PairMember I i j T) := (val i j).mpr (Or.inl h)
  refine ⟨U, hg.program, ⟨hU.2.1, hU.2.2, fun i hi => ?_⟩, fun r c u hc hu => ?_⟩
  · rcases (hl i).mp hi with hi | hi
    · obtain ⟨u, hu, hiu⟩ := h.map.2.2 i hi
      exact ⟨u, hg.span u hu, into i u hiu⟩
    · exact ⟨z, hg.root, (val i z).mpr (Or.inr ⟨hZF.1.eq_of_same_members i k hi, rfl⟩)⟩
  · rcases (val r u).mp hu with hu | ⟨rfl, rfl⟩
    · exact (h.rules r c u hc hu).mono_l I into (fun i j h => ((hg.cut.2 i j).mp h).2)
    · exact (hz c hc).mono_l I into (fun _ _ h => h)

/-- 给定新载体坐标，实际构造完整语法翻译；新坐标的支撑外条件只在正确性中使用。 -/
theorem sr_compile_at_l (hZF : M.Models ZF) {ω F n b : M.Domain}
    (hω : M.IsOmega ω) (hF : Sfm_d I ω n F) (hb : M.mem b ω) :
    ∃ m G T, Sr_state_d I ω b F n m G T := by
  let ρ : Env M 4 := ⟨Fin.cases n (Fin.cases F (Fin.cases b (fun _ => ω))), fun _ => ω⟩
  let φ : UnarySchema 4 := { body := .imp (Formula.subset .newest (.bound 1)) (.existsE (.existsE (.existsE
    (sr_state_m (𝒞 := 𝒞) (.bound 7) (.bound 6) (.bound 5) (.bound 3) (.bound 2) (.bound 1) .newest)))) }
  have sat k : φ.denote ρ k ↔ (M.MemberSubset k n → ∃ m G T, Sr_state_d I ω b F k m G T) := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_imp_iff, Formula.satisfies_subset_iff,
      Formula.satisfies_exists_iff, sr_state_sat_l I hZF.1]; rfl
  have build : ∀ k, M.mem k ω → M.MemberSubset k n → ∃ m G T, Sr_state_d I ω b F k m G T := by
    apply hω.induction
    · obtain ⟨A, hA⟩ := ZF.separation_exists_d hZF φ ρ ω
      exact ⟨A, fun k => (hA k).trans (and_congr_right fun _ => sat k)⟩
    · intro e he _
      have seq := Structure.IsSequenceOfLength.empty I he
      have empty : ∀ i j, ¬ M.PairMember I i j e := fun _ _ ⟨p, _, hp⟩ => he p hp
      exact ⟨e, e, e, ⟨num_mem_l hZF.1 hω (show Num_d 0 e from he), seq,
        fun i j h => (empty i j h).elim⟩, ⟨seq.2.1, seq.2.2, fun i hi => (he i hi).elim⟩,
        fun r _ u _ h => (empty r u h).elim⟩
    · intro k hk ih l hl hln
      have hkn := hln k hl.predecessor_mem
      obtain ⟨m, G, T, state⟩ := ih (fun i hi => hln i ((hl i).mpr (Or.inl hi)))
      obtain ⟨c, hc⟩ := (hF.2.1.2.2 k).mp hkn
      obtain ⟨v, H, r, hg, rule⟩ := sr_step_l I hZF hω hF hb hc state.map state.program
      have rules d (hd : M.PairMember I k d F) : Sr_rule_d I b T H d r :=
        hF.2.1.2.1.2 k c d hc hd ▸ rule
      obtain ⟨U, hU⟩ := sr_state_append_l I hZF hω hk hl state hg rules
      exact ⟨v, H, U, hU⟩
  exact build n hF.1 (fun _ h => h)

/-- 原程序自动给出支撑外坐标、翻译程序和全部根位置的实际映射。 -/
theorem sr_compile_l (hZF : M.Models ZF) {ω F n : M.Domain} (hω : M.IsOmega ω) (hF : Sfm_d I ω n F) :
    ∃ b m G T, M.mem b ω ∧ Sbound_d I F b ∧ Sr_state_d I ω b F n m G T := by
  obtain ⟨b, hb, bound⟩ := sbound_exists_l I hZF hω hF
  obtain ⟨m, G, T, h⟩ := sr_compile_at_l I hZF hω hF hb
  exact ⟨b, m, G, T, hb, bound, h⟩

end YesMetaZFC.SetTheory.Internal
