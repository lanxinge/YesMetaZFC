import YesMetaZFC.SetTheory.LargeCardinal.IterationWeakPublicWinning
import YesMetaZFC.SetTheory.HereditaryCover

/-! # 可数 nice 树的 ω₁ 弱可迭代性

由给定根到真实 Vθ 的初等嵌入自动构造公开获胜策略。对象选择只进行一次；
任意对手走法均有唯一运行，合法时每个可数阶段保持实际传递极限和完整返回列。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}
section Winning
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 公开枝策略及其对全部对手走法的获胜证书；模型和返回列由内部重放构造。 -/
def Wi_winning_d (ω c Ω Z D Γ : M.Domain) : Prop := ∃ a A S o s₀ Ψ α₀ T₀ Q₀ G₀ P₀,
  (∀ x, ¬ M.mem x o) ∧ M.SuccessorOf α₀ o ∧ Rd_quad_d s₀ T₀ Q₀ G₀ P₀ ∧
  Wi_state_d hZF ω α₀ T₀ Q₀ G₀ a A S P₀ ∧ Rd_entry_d o c Q₀ ∧ Wi_strategy_d hZF o Ψ Ω Z D Γ ∧
  (∀ t d X R T Q G E L, Wi_tree_d t T Q G E L → It_nice_d hZF ω d ω T Q G E L →
    Smem_d I d X R → M.CardinalLessOrEqual I X ω → M.mem t Z) ∧
  ∀ β, (β = Ω ∨ M.mem β Ω) → ∀ F, Fn0_d β Z F → ∃ R, Wi_run_d hZF o Ψ F β Z R ∧
    (∀ R', Wi_run_d hZF o Ψ F β Z R' → R' = R) ∧
    (Wi_legal_d hZF ω β F R → Wi_history_d hZF ω a A S β Z R ∧
      (∀ i s, Rd_entry_d i s R → Wi_reply_d hZF ω a A S o s₀ Ψ F R i s) ∧
      ∀ α ξ F', M.mem α β → M.SuccessorOf α ξ → M.IsRestrictionOf I F' F α →
        ∃ B, Rd_entry_d F' B Γ ∧ Wi_play_d hZF ω a A S F R α ξ B)
end Winning

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- Neeman 推论 2.4：实际 ω₁ 上的 nice 弱迭代博弈有集合编码获胜策略。 -/
theorem it_nice_weakly_iterable_l {ω c X R θ a A S π : M.Domain}
    (source : It_source_d hZF ω c) (mx : Smem_d I c X R) (count : M.CardinalLessOrEqual I X ω)
    (rank : V_d I θ A) (ma : Smem_d I a A S) (embed : Smap_d I ω c a X A π) :
    ∃ Ω Z D Γ, M.IsHartogsNumber I Ω ω ∧ Wi_winning_d hZF ω c Ω Z D Γ := by
  have ready := source
  obtain ⟨_, _, _, _, source₀⟩ := ready
  have hω := source₀.omega
  obtain ⟨o, α₀, T₀, Q₀, G₀, P₀, ho, hα₀, root, hc, _⟩ := wi_root_l hZF source mx count ma embed
  obtain ⟨s₀, pack₀⟩ := rd_quad_exists_l (ZF.modelsKP hZF) T₀ Q₀ G₀ P₀
  obtain ⟨Ω, hΩ⟩ := ZF.exists_hartogsNumber hZF I ω
  obtain ⟨p, pp⟩ := rd_quad_exists_l (ZF.modelsKP hZF) s₀ A Ω ω
  obtain ⟨χ, Z, hχ, hωχ, hZ, hp⟩ := ZFC.h_cover_l I hZFC hω p
  have zt := ZF.h_transitive_l I hZF hZ
  obtain ⟨hs₀, hA, hΩZ, hωZ⟩ := pp.mem_l zt hp
  obtain ⟨z, hz, hzω⟩ := hω.1.1
  have eq := hZF.1.eq_of_same_members z o (fun x => iff_of_false (hz x) (ho x))
  have hoZ := zt ω hωZ o (eq ▸ hzω)
  obtain ⟨u₀, pair⟩ := (I).total o s₀
  obtain ⟨Ψ, select⟩ := wi_selector_exists_l hZFC (ZFC.h_kpair_l hZFC hω hχ hωχ hZ pair hoZ hs₀) pair
    (ω := ω) (a := a) (A := A) (S := S)
  obtain ⟨D, Γ, strategy⟩ := wi_strategy_exists_l hZFC hω hχ hωχ hZ hΩ.1 hΩZ hoZ select
  refine ⟨Ω, Z, D, Γ, hΩ, a, A, S, o, s₀, Ψ, α₀, T₀, Q₀, G₀, P₀,
    ho, hα₀, pack₀, root, hc, strategy, ?_, ?_⟩
  · intro t d Y W T Q G E L pack nice my cy
    exact pack.mem_l hZFC hω hχ hωχ hZ hωZ nice my cy
  · intro β within F moves
    have hb : M.IsOrdinal β := within.elim (fun eq => eq.symm ▸ hΩ.1) hΩ.1.mem
    have hbZ : M.mem β Z := within.elim (fun eq => eq.symm ▸ hΩZ) (zt Ω hΩZ β)
    have sub : M.MemberSubset β Ω := within.elim (fun eq _ hi => eq ▸ hi) (fun hi => hΩ.1.transitive β hi)
    obtain ⟨H, run, unique⟩ := wi_run_exists_l hZFC hω hχ hωχ hZ hb hbZ hoZ select moves
    refine ⟨H, run, unique, fun legal => ?_⟩
    obtain ⟨history, replies⟩ := wi_run_wins_l hZFC hω hχ hωχ hZ hωZ hA hb
      (fun i hi => (hΩ.2 i (hΩ.1.mem (sub i hi))).mp (sub i hi)) ho hα₀ pack₀ root rank ma select run legal
    refine ⟨history, replies, fun α ξ F' hα succ rf => ?_⟩
    have fn := fn0_of_function_l (ZF.modelsKP hZF)
      (rf.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) moves) (hb.transitive α hα))
    obtain ⟨B, _, chosen⟩ := strategy.2.1.2.1 F' ((strategy.1 F').mpr ⟨α, ξ, sub α hα, succ, fn⟩)
    exact ⟨B, chosen, strategy.play_l hZF (fn0_function_l (ZF.modelsKP hZF) select.function).1 ho moves run replies hα succ rf chosen⟩

end YesMetaZFC.SetTheory.LargeCardinal
