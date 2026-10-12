import YesMetaZFC.SetTheory.Descriptive.GameSplice

/-! # 一轮之后的获胜策略拼接

玩家 I 落子时同时接好全部分支；玩家 II 落子时先走选定字母。
同一个拼接图处理这两种情形，因而不需要超限指定获胜等级。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem cg_glue_l {ω X F J B W Z s n a K : M.Domain} (hω : M.IsOmega ω)
    (space : Fseq_space_d I ω X F) (runs : M.IsFunctionSpace I B ω X)
    (strategies : M.IsFunctionSpace I Z F X) (hn : M.mem n ω)
    (hs : M.IsSetFunctionFromTo I s n X) (ha : M.mem a X) (table : M.IsSetFunctionFromTo I K X Z)
    (wins : ∀ x, M.mem x X → (¬ M.mem n J → x = a) → ∀ τ, Rd_entry_d x τ K →
      ∀ t, Fseq_end_d I ω t s x → Cg_tail_win_d I false ω X F J B W t τ) :
    ∃ σ, Cg_tail_win_d I false ω X F J B W s σ := by
  obtain ⟨σ, fn, read⟩ := cg_splice_l hZF space strategies ha table
  refine ⟨σ, fn0_of_function_l (ZF.modelsKP hZF) fn, fun f hf sf follows => ?_⟩
  have ff := (runs f).mp hf
  obtain ⟨x, hx, hfx⟩ := ff.2.2 n hn
  have head : ¬ M.mem n J → x = a := by
    intro turn
    have play := follows n hn turn s ((ds_restrict_iff_l I hs ff.1).mpr sf) (fun _ h => h) x hfx
    rcases ((read s x).mp play).2 with ⟨_, eq⟩ | ⟨v, _, hv, _⟩
    · exact eq
    · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) n (hs.input_mem_of_pairMember hv)).elim
  obtain ⟨τ, _, hτ⟩ := table.2.2 x hx
  obtain ⟨m, t, hm, ft, endt⟩ := ZF.fseq_end_exists_l I hZF hω hn hs hx
  have tf := ds_append_sub_l I hZF.1 hs endt sf hfx
  have tail := wins x hx head τ hτ t endt
  refine tail.2 f hf tf (fun i hi turn h hr th v hv => ?_)
  obtain ⟨j, k, next⟩ := endt
  have kn := next.prefix_sequence.2.2.2.eq hZF.1 hs.2.1
  subst k
  have st := (ds_restrict_iff_l I hs ft.1).mp next.prefix_restriction
  have hnx : Rd_entry_d n x h := next.last_value.elim fun p hp => ⟨p, hp.1, th p hp.2⟩
  have play := follows i hi turn h hr (fun p hp => th p (st p hp)) v hv
  rcases ((read h v).mp play).2 with ⟨no, _⟩ | ⟨y, υ, hny, hυ, move⟩
  · exact (no ⟨x, hnx⟩).elim
  · have fh := hr.isSetFunctionFromTo ff (hω.transitive hZF i hi)
    have eq := fh.1.2 n x y hnx hny
    subst y
    have eq := table.1.2 x τ υ hτ hυ
    exact eq.symm ▸ move

end YesMetaZFC.SetTheory.Descriptive
