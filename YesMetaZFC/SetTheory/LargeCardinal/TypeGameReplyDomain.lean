import YesMetaZFC.SetTheory.LargeCardinal.TypeGameContext
import YesMetaZFC.SetTheory.LargeCardinal.TypePoolRead

/-! # 共同秩段唯一确定回答语言的域

两层的相对 Vτ 都限制到同一共同秩段。随后用常量域的外延性和完整
查询域的唯一性识别原表项；不提升两层的无界满足关系。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_context_d.reply_domain_l {ω X R μ K η C Y S μ' K' η' D L W : M.Domain}
    (context : Tg_context_d ω X η C) (current : Tg_context_d ω Y η' D)
    (owner : Ep_source_d hZF ω μ K X R) (source : Ep_source_d hZF ω μ' K' Y S)
    (hW : M.mem W X) (rank : Vr_d X L W) (hW' : M.mem W Y) (rank' : Vr_d Y L W)
    (limit : M.IsLimitOrdinal L)
    (nc : Nonempty {x // M.mem x C}) (nd : Nonempty {x // M.mem x D})
    (ρ : Env (rt_model_l C nc) 11) (θ : Env (rt_model_l D nd) 11)
    (hw : (ρ.bound 0).val = ω) (hw' : (θ.bound 0).val = ω)
    (hn : (θ.bound 3).val = (ρ.bound 3).val) (ht : (θ.bound 4).val = (ρ.bound 4).val)
    (hτ : M.mem (ρ.bound 4).val W)
    (left : Formula.satisfies ρ tg_reply_language0_m) (right : Formula.satisfies θ tg_reply_language0_m) :
    (ρ.bound 5).val = (θ.bound 5).val ∧ (ρ.bound 6).val = (θ.bound 6).val ∧
      (ρ.bound 7).val = (θ.bound 7).val := by
  have fs := (context.read_l hZF owner).1
  have ft := (current.read_l hZF source).1
  simp only [tg_reply_language0_m, Formula.satisfies_conj_iff] at left right
  obtain ⟨_, _, _, _, vr, cons, pool, _⟩ := left
  obtain ⟨_, _, _, _, vr', cons', pool', _⟩ := right
  have vr := (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc ρ (.bound 4) (.bound 5)).mp vr
  have vr' := (vr_sat_l (ZF.modelsKP hZF) ft.transitive nd θ (.bound 4) (.bound 5)).mp vr'
  have full := context.rank.of_rank_l hZF owner.transitive context.member (ρ.bound 5).property vr
  have full' := current.rank.of_rank_l hZF source.transitive current.member (θ.bound 5).property vr'
  have hB := owner.transitive C context.member (ρ.bound 5).val (ρ.bound 5).property
  have hB' := source.transitive D current.member (θ.bound 5).val (θ.bound 5).property
  obtain ⟨hBW, vrW⟩ := rank.rank_l hZF owner.transitive hW limit hτ hB full
  obtain ⟨hBW', vrW'⟩ := rank'.rank_l hZF source.transitive hW' limit (ht.symm ▸ hτ) hB' full'
  have eqB := Vr_d.unique_l hZF (rank.transitive_l hZF owner.transitive hW) hBW hBW' vrW (ht ▸ vrW')
  have cons := (rt_model_delta_l fs.transitive nc (tt_constants0_delta_l (.bound 4) (.bound 5) (.bound 6)) ρ).mp cons
  have cons' := (rt_model_delta_l ft.transitive nd (tt_constants0_delta_l (.bound 4) (.bound 5) (.bound 6)) θ).mp cons'
  simp only [tt_constants0_sat_l hZF.1, @eval_image_env_l (rt_model_l C nc) M Subtype.val] at cons
  simp only [tt_constants0_sat_l hZF.1, @eval_image_env_l (rt_model_l D nd) M Subtype.val] at cons'
  have eqU : (ρ.bound 6).val = (θ.bound 6).val := by
    apply hZF.1.eq_of_same_members
    intro x
    exact (cons x).trans ((or_congr (Iff.of_eq (congrArg (M.mem x) eqB))
      (Iff.of_eq (congrArg (fun y => x = y) ht.symm))).trans (cons' x).symm)
  obtain ⟨A, E, _, _, names, seq, product⟩ := (fs.pool_sat_l (ZF.modelsKP hZF) nc ρ (.bound 0) (.bound 3) (.bound 6) (.bound 7) hw).mp pool
  obtain ⟨A', E', _, _, names', seq', product'⟩ := (ft.pool_sat_l (ZF.modelsKP hZF) nd θ (.bound 0) (.bound 3) (.bound 6) (.bound 7) hw').mp pool'
  have pool : Tt_pool_d I ω (ρ.bound 3).val (ρ.bound 6).val (ρ.bound 7).val := ⟨A, E, names, seq, product⟩
  have pool' : Tt_pool_d I ω (θ.bound 3).val (θ.bound 6).val (θ.bound 7).val := ⟨A', E', names', seq', product'⟩
  exact ⟨eqB, eqU, pool.unique_l hZF.1 I (hn ▸ eqU.symm ▸ pool')⟩

end YesMetaZFC.SetTheory.LargeCardinal
