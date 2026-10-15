import YesMetaZFC.SetTheory.Descriptive.GameCompletion
import YesMetaZFC.SetTheory.Descriptive.FirstViolationRead

/-! # 获胜策略在合法有限历史上的实际后继

有限追加保持任一方原策略的服从关系及续局获胜性。若获胜策略在合法位置
首次违规，实际无限延拓会被收益判给对手，与该续局获胜性矛盾。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 一项追加的任意严格有限前缀已经包含于旧历史。 -/
theorem ds_before_end_l {ω X F n s t a q : M.Domain} (hω : M.IsOmega ω)
    (space : Fseq_space_d I ω X F) (hn : M.mem n ω) (fs : M.IsSetFunctionFromTo I s n X)
    (endt : Fseq_end_d I ω t s a) (hq : M.mem q F) (qt : M.MemberSubset q t)
    (proper : ¬ M.MemberSubset t q) : M.MemberSubset q s := by
  obtain ⟨m, n', d⟩ := endt
  have eq := d.prefix_sequence.2.2.2.eq hZF.1 fs.2.1
  subst n'
  obtain ⟨k, hk, fq⟩ := (space q).mp hq
  have rq := (ds_restrict_iff_l I fq d.source.2.2.1).mpr qt
  have rs := d.prefix_restriction
  rcases (hω.isOrdinal hZF).wellOrder.linear.compare k hk n hn with eq | lt | gt
  · exact ds_prefix_mono_l I fq fs.1 rq rs (fun x hx => (eq x).mp hx)
  · exact ds_prefix_mono_l I fq fs.1 rq rs ((hω.members_areOrdinals hZF n hn).transitive k lt)
  · have sq := ds_prefix_mono_l I fs fq.1 rs rq ((hω.members_areOrdinals hZF k hk).transitive n gt)
    have last := (rq.2 n a).mpr ⟨gt, d.last_value⟩
    exact (proper (ds_append_sub_l I hZF.1 fs ⟨m, n, d⟩ sq last)).elim

theorem Cg_legal_d.extend_l {ω X F L G n s t a : M.Domain} (legal : Cg_legal_d (M := M) F L G)
    (hω : M.IsOmega ω) (space : Fseq_space_d I ω X F) (hn : M.mem n ω)
    (fs : M.IsSetFunctionFromTo I s n X) (hs : M.mem s G)
    (endt : Fseq_end_d I ω t s a) (ht : M.mem t F) (check : M.mem t L) : M.mem t G := by
  classical
  refine (legal t).mpr ⟨ht, fun q hq qt => ?_⟩
  by_cases tq : M.MemberSubset t q
  · have eq := hZF.1.eq_of_same_members q t (fun x => ⟨qt x, tq x⟩)
    exact eq.symm ▸ check
  · exact ((legal s).mp hs).2 q hq (ds_before_end_l hZF hω space hn fs endt hq qt tq)

theorem Cg_follows_d.extend_l {ι : Bool} {ω X J σ n s t a : M.Domain} (hω : M.IsOmega ω)
    (hn : M.mem n ω) (fs : M.IsSetFunctionFromTo I s n X)
    (follows : Cg_follows_d I ι ω J σ s) (endt : Fseq_end_d I ω t s a)
    (move : (if ι then M.mem n J else ¬ M.mem n J) → Rd_entry_d s a σ) : Cg_follows_d I ι ω J σ t := by
  obtain ⟨m, n', d⟩ := endt
  have eq := d.prefix_sequence.2.2.2.eq hZF.1 fs.2.1
  subst n'
  intro i hi turn h hr v hv
  have him := (d.source.2.2.2 i).mpr ⟨v, hv⟩
  rcases (d.length_successor i).mp him with hin | eq
  · exact follows i hi turn h (d.prefix_restriction.trans hr ((hω.members_areOrdinals hZF n hn).transitive i hin))
      v ((d.prefix_restriction.2 i v).mpr ⟨hin, hv⟩)
  · have eq := hZF.1.eq_of_same_members i n eq
    subst i
    have eh := hr.eq hZF.1 d.prefix_restriction
    have ev := d.source.2.2.1.2 n v a hv d.last_value
    exact eh.symm ▸ ev.symm ▸ move turn

/-- 原策略负责的时刻使用其原值，其余时刻允许任意对手落子。 -/
theorem Cg_tail_win_d.extend_l {ι : Bool} {ω X F J B W σ n s t a : M.Domain}
    (win : Cg_tail_win_d I ι ω X F J B W s σ) (hω : M.IsOmega ω)
    (runs : M.IsFunctionSpace I B ω X) (hn : M.mem n ω) (fs : M.IsSetFunctionFromTo I s n X)
    (endt : Fseq_end_d I ω t s a) (move : (if ι then M.mem n J else ¬ M.mem n J) → Rd_entry_d s a σ) :
    Cg_tail_win_d I ι ω X F J B W t σ := by
  obtain ⟨m, n', d⟩ := endt
  have eq := d.prefix_sequence.2.2.2.eq hZF.1 fs.2.1
  subst n'
  have st := (ds_restrict_iff_l I fs d.source.2.2.1).mp d.prefix_restriction
  refine ⟨win.1, fun f hf tf follows => win.2 f hf (fun p hp => tf p (st p hp)) ?_⟩
  have ff := (runs f).mp hf
  have sf := (ds_restrict_iff_l I fs ff.1).mpr (fun p hp => tf p (st p hp))
  have last : Rd_entry_d n a f := d.last_value.elim fun p hp => ⟨p, hp.1, tf p hp.2⟩
  intro i hi turn h hr sh v hv
  rcases (hω.isOrdinal hZF).wellOrder.linear.compare i hi n hn with eq | lt | gt
  · have eq := hZF.1.eq_of_same_members i n eq
    subst i
    have eh := hr.eq hZF.1 sf
    have ev := ff.1.2 n v a hv last
    exact eh.symm ▸ ev.symm ▸ move turn
  · obtain ⟨x, _, hsx⟩ := fs.2.2 i lt
    have hhx : Rd_entry_d i x h := hsx.elim fun p hp => ⟨p, hp.1, sh p hp.2⟩
    exact (KP.mem_irrefl_d (ZF.modelsKP hZF) i ((hr.2 i x).mp hhx).1).elim
  · have th : M.MemberSubset t h := ds_append_sub_l I hZF.1 fs ⟨m, n, d⟩ sh ((hr.2 n a).mpr ⟨gt, last⟩)
    exact follows i hi turn h hr th v hv

/-- 沿原策略到达的有限位置，其后继续使用同一策略仍获胜。 -/
theorem Cg_win_d.tail_l {ι : Bool} {ω X F J B W σ n s : M.Domain}
    (win : Cg_win_d I ι ω X F J B W σ) (hω : M.IsOmega ω)
    (runs : M.IsFunctionSpace I B ω X) (hn : M.mem n ω) (fs : M.IsSetFunctionFromTo I s n X)
    (played : Cg_follows_d I ι ω J σ s) : Cg_tail_win_d I ι ω X F J B W s σ := by
  classical
  refine ⟨win.1, fun f hf sf follows => win.2 f hf ?_⟩
  have ff := (runs f).mp hf
  have sr := (ds_restrict_iff_l I fs ff.1).mpr sf
  intro i hi turn h hr v hv
  rcases (hω.isOrdinal hZF).wellOrder.linear.compare i hi n hn with eq | lt | gt
  · have ni : M.MemberSubset n i := fun x hx => (eq x).mpr hx
    exact follows i hi turn h hr (ds_prefix_mono_l I fs (hr.isSetFunction ff.1) sr hr ni) v hv
  · exact played i hi turn h (sr.trans hr ((hω.members_areOrdinals hZF n hn).transitive i lt))
      v ((sr.2 i v).mpr ⟨lt, hv⟩)
  · exact follows i hi turn h hr
      (ds_prefix_mono_l I fs (hr.isSetFunction ff.1) sr hr ((hω.members_areOrdinals hZF i hi).transitive n gt)) v hv

/-- 获胜策略不会从合法位置作出首次违规的走法。 -/
theorem Cg_tail_win_d.legal_step_l {ι : Bool} {ω X F L G J B W σ n s t a : M.Domain}
    (win : Cg_tail_win_d I ι ω X F J B W s σ) (hω : M.IsOmega ω)
    (space : Fseq_space_d I ω X F) (runs : M.IsFunctionSpace I B ω X)
    (legal : Cg_legal_d (M := M) F L G) (payoff : Cg_payoff_d ω X F L J B W)
    (hn : M.mem n ω) (fs : M.IsSetFunctionFromTo I s n X) (hs : M.mem s G)
    (ha : M.mem a X) (turn : if ι then M.mem n J else ¬ M.mem n J) (value : Rd_entry_d s a σ)
    (endt : Fseq_end_d I ω t s a) (ht : M.mem t F) : M.mem t G := by
  apply legal.extend_l hZF hω space hn fs hs endt ht
  apply Classical.byContradiction
  intro bad
  have next := win.extend_l hZF hω runs hn fs endt (fun _ => value)
  obtain ⟨m, hm, ft⟩ := (space t).mp ht
  obtain ⟨f, ff, tf, follows⟩ := cg_tail_play_l hZF (ι := ι) hω space win.1 hm ft ha
  have winf := next.2 f ((runs f).mpr ff) tf follows
  obtain ⟨m', n', d⟩ := endt
  have en := d.prefix_sequence.2.2.2.eq hZF.1 fs.2.1
  have em := d.source.2.2.2.eq hZF.1 ft.2.1
  subst n' m'
  have first : Cg_first_d ω X F L n t :=
    ⟨m, hm, fn0_of_function_l (ZF.modelsKP hZF) ft, d.length_successor, bad,
      fun q hq qt tq => ((legal s).mp hs).2 q hq (ds_before_end_l hZF hω space hn fs ⟨m, n, d⟩ hq qt tq)⟩
  cases ι with
  | false => exact winf (payoff.ii_first_l (ZF.modelsKP hZF) (hω.isOrdinal hZF) ff.1 ((runs f).mpr ff) ht tf first turn)
  | true => exact ((payoff.read_l ((runs f).mpr ff)).mpr ⟨t, n, ht, tf, turn, first⟩) winf

end YesMetaZFC.SetTheory.Descriptive
