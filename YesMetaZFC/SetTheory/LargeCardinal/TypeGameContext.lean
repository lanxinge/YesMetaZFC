import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRenewalSyntax
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameReplyCompare
import YesMetaZFC.SetTheory.LargeCardinal.TypeContinueSyntax
import YesMetaZFC.SetTheory.LargeCardinal.TypeContinueRealizeSyntax
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRigidity
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRecoverySyntax
import YesMetaZFC.SetTheory.LargeCardinal.IterationCopyModel
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderReadSource
import YesMetaZFC.Model.SetTheory.LevyReflection
import YesMetaZFC.SetTheory.CumulativeRegularCover
import YesMetaZFC.SetTheory.Card.FiniteParameters

/-! # 工作模型中的有限反射秩段

先反射已证的每轮更新句子，再把所得秩段放入正则工作根。
初等图搬运该秩段及其有界相对句子，因而后继的新参数也受同一全称句子约束。
工作模型本身只使用已经构造的源闭性，不要求它满足整个 ZFC。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_kernel_m : Formula 1 0 := .conj tg_renewal_m
  (.conj tc_transfer_m (.conj ee_rebuild_m (.conj tc_realize_m
    (.conj tc_rigid_m (.conj tc_recover_m tg_reply_compare_m)))))

theorem tg_kernel_closed_l : tg_kernel_m.FreeClosed :=
  ⟨tg_renewal_closed_l, tc_transfer_closed_l, ee_rebuild_closed_l, tc_realize_closed_l,
    tc_rigid_closed_l, tc_recover_closed_l, tg_reply_compare_closed_l⟩

def tg_context_m : Formula 1 1 := lr_rel_m tg_kernel_m .newest (fun i => .bound i.succ)

theorem tg_context_closed_l : tg_context_m.FreeClosed :=
  lr_rel_closed_l _ tg_kernel_closed_l _ _ rfl (fun i => Fin.elim0 i)

theorem tg_context_delta_l : tg_context_m.IsDelta0 := lr_rel_delta_l ..

structure Tg_context_d (ω X η C : M.Domain) : Prop where
  height : M.mem η X
  member : M.mem C X
  rank : Vr_d X η C
  limit : M.IsLimitOrdinal η
  omega : M.mem ω C
  kernel : Formula.satisfies ((⟨Fin.elim0, fun _ => ω⟩ : Env M 0).push C) tg_context_m

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_context_d.read_l {ω κ K X R η C : M.Domain} (h : Tg_context_d ω X η C)
    (source : Ep_source_d hZF ω κ K X R) :
    Fs_read_d ω C ∧ Formula.satisfies
      (⟨Fin.elim0, fun _ => ⟨ω, h.omega⟩⟩ : Env (rt_model_l C ⟨⟨ω, h.omega⟩⟩) 0) tg_kernel_m := by
  have finite := source.rank_read_source_l hZF h.member h.rank h.limit h.omega
  obtain ⟨c, S, code⟩ := smdl_membership_l I hZF ⟨ω, h.omega⟩
  exact ⟨finite, (sc_relative_sat_l I code finite.transitive ⟨⟨ω, h.omega⟩⟩ tg_kernel_m tg_kernel_closed_l
    ⟨Fin.elim0, fun _ => ⟨ω, h.omega⟩⟩ ((⟨Fin.elim0, fun _ => ω⟩ : Env M 0).push C)
    .newest (fun i => .bound i.succ) rfl (fun i => Fin.elim0 i)).mp h.kernel⟩

theorem Tg_context_d.map_l {ω X R c Y S d j η C : M.Domain} (h : Tg_context_d ω X η C)
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (mx : Smem_d I c X R) (my : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j) :
    ∃ η' C', Rd_entry_d η η' j ∧ Rd_entry_d C C' j ∧ Tg_context_d ω Y η' C' := by
  obtain ⟨η', hη', hη⟩ := hj.1.1.2.2 η h.height
  obtain ⟨C', hC', hC⟩ := hj.1.1.2.2 C h.member
  have hw := hj.omega_l I hZF hω hX hY mx my (hX C h.member ω h.omega)
  have tr := smap_delta_l I hZF hω hX hY mx my hj tg_context_m tg_context_closed_l tg_context_delta_l
    ((⟨Fin.elim0, fun _ => ω⟩ : Env M 0).push C) ((⟨Fin.elim0, fun _ => ω⟩ : Env M 0).push C')
    (Fin.cases hC (fun i => Fin.elim0 i))
  exact ⟨η', C', hη, hC, hη', hC', (hj.hierarchy_l hZF hω hX hY mx my hη hC).mp h.rank,
    (hj.limit_l hZF hω hX hY mx my hη).mp h.limit,
    (hj.member_l I hZF hω mx my hw hC).mp h.omega, tr.mp h.kernel⟩

/-- 全称句子在目标秩段内覆盖任意新输入，不局限于旧参数的像。 -/
theorem Tg_context_d.renew_l {ω κ K X R η C : M.Domain} (h : Tg_context_d ω X η C)
    (source : Ep_source_d hZF ω κ K X R) (nc : Nonempty {x // M.mem x C})
    (ρ : Env (rt_model_l C nc) 38) (seed : Formula.satisfies ρ tg_seed0_m) :
    Formula.satisfies ρ tg_successor0_m := by
  have kernel := ((Formula.satisfies_conj_iff ..).mp (h.read_l hZF source).2).1
  have step := (Formula.satisfies_forallClosure_iff (ℳ := rt_model_l C nc) (fun _ => ⟨ω, h.omega⟩)
    (.imp tg_seed0_m tg_successor0_m)).mp kernel ρ.bound
  have moved := (Formula.closed_env_l (.imp tg_seed0_m tg_successor0_m)
    ⟨tg_seed0_closed_l, tg_successor0_closed_l⟩
    (ρ := ⟨ρ.bound, fun _ => ⟨ω, h.omega⟩⟩) (η := ρ) rfl).mp step
  exact (Formula.satisfies_imp_iff ..).mp moved seed

/-- 原继续规则中的新超过见证在当前层直接产生实际像证书。 -/
theorem Tg_context_d.continue_l {ω κ K X R η C : M.Domain} (h : Tg_context_d ω X η C)
    (source : Ep_source_d hZF ω κ K X R) (nc : Nonempty {x // M.mem x C})
    (ρ : Env (rt_model_l C nc) 28) (seed : Formula.satisfies ρ tc_seed0_m) :
    Formula.satisfies ρ tc_result0_m := by
  have kernel := ((Formula.satisfies_conj_iff ..).mp
    ((Formula.satisfies_conj_iff ..).mp (h.read_l hZF source).2).2).1
  have step := (Formula.satisfies_forallClosure_iff (ℳ := rt_model_l C nc) (fun _ => ⟨ω, h.omega⟩)
    (.imp tc_seed0_m tc_result0_m)).mp kernel ρ.bound
  have moved := (Formula.closed_env_l (.imp tc_seed0_m tc_result0_m)
    ⟨tc_seed0_closed_l, tc_result0_closed_l⟩
    (ρ := ⟨ρ.bound, fun _ => ⟨ω, h.omega⟩⟩) (η := ρ) rfl).mp step
  exact (Formula.satisfies_imp_iff ..).mp moved seed

/-- 原程序与原名字列在新层重新解释为完整的四查询语言。 -/
theorem Tg_context_d.language_l {ω κ K X R η C : M.Domain} (h : Tg_context_d ω X η C)
    (source : Ep_source_d hZF ω κ K X R) (nc : Nonempty {x // M.mem x C})
    (ρ : Env (rt_model_l C nc) 10) (seed : Formula.satisfies ρ ee_rebuild_seed_m) :
    Formula.satisfies ρ ee_language0_m := by
  have kernel := ((Formula.satisfies_conj_iff ..).mp ((Formula.satisfies_conj_iff ..).mp
    ((Formula.satisfies_conj_iff ..).mp (h.read_l hZF source).2).2).2).1
  have step := (Formula.satisfies_forallClosure_iff (ℳ := rt_model_l C nc) (fun _ => ⟨ω, h.omega⟩)
    (.imp ee_rebuild_seed_m ee_language0_m)).mp kernel ρ.bound
  have moved := (Formula.closed_env_l (.imp ee_rebuild_seed_m ee_language0_m)
    ⟨ee_rebuild_seed_closed_l, ee_language0_closed_l⟩
    (ρ := ⟨ρ.bound, fun _ => ⟨ω, h.omega⟩⟩) (η := ρ) rfl).mp step
  exact (Formula.satisfies_imp_iff ..).mp moved seed

/-- 完整旧实现与原程序共同解释同一原子类型查询。 -/
theorem Tg_context_d.realize_seed_l {ω κ K X R η C : M.Domain} (h : Tg_context_d ω X η C)
    (source : Ep_source_d hZF ω κ K X R) (nc : Nonempty {x // M.mem x C})
    (ρ : Env (rt_model_l C nc) 27) (seed : Formula.satisfies ρ tc_realize_seed0_m) :
    Formula.satisfies ρ tc_realize_result0_m := by
  have kernel := ((Formula.satisfies_conj_iff ..).mp ((Formula.satisfies_conj_iff ..).mp
    ((Formula.satisfies_conj_iff ..).mp ((Formula.satisfies_conj_iff ..).mp (h.read_l hZF source).2).2).2).2).1
  have step := (Formula.satisfies_forallClosure_iff (ℳ := rt_model_l C nc) (fun _ => ⟨ω, h.omega⟩)
    (.imp tc_realize_seed0_m tc_realize_result0_m)).mp kernel ρ.bound
  have moved := (Formula.closed_env_l (.imp tc_realize_seed0_m tc_realize_result0_m)
    ⟨tc_realize_seed0_closed_l, tc_realize_result0_closed_l⟩
    (ρ := ⟨ρ.bound, fun _ => ⟨ω, h.omega⟩⟩) (η := ρ) rfl).mp step
  exact (Formula.satisfies_imp_iff ..).mp moved seed

/-- 超过关系和 dcp 定义域自动给出原最大序数查询。 -/
theorem Tg_context_d.rigid_seed_l {ω κ K X R η C : M.Domain} (h : Tg_context_d ω X η C)
    (source : Ep_source_d hZF ω κ K X R) (nc : Nonempty {x // M.mem x C})
    (ρ : Env (rt_model_l C nc) 29) (seed : Formula.satisfies ρ tc_rigid_seed0_m) :
    M.mem (ρ.bound 25).val (ρ.bound 20).val := by
  have kernel := ((Formula.satisfies_conj_iff ..).mp ((Formula.satisfies_conj_iff ..).mp
    ((Formula.satisfies_conj_iff ..).mp ((Formula.satisfies_conj_iff ..).mp
      ((Formula.satisfies_conj_iff ..).mp (h.read_l hZF source).2).2).2).2).2).1
  have step := (Formula.satisfies_forallClosure_iff (ℳ := rt_model_l C nc) (fun _ => ⟨ω, h.omega⟩)
    (.imp tc_rigid_seed0_m (.mem (.bound 25) (.bound 20)))).mp kernel ρ.bound
  have moved := (Formula.closed_env_l (.imp tc_rigid_seed0_m (.mem (.bound 25) (.bound 20)))
    ⟨tc_rigid_seed0_closed_l, rfl, rfl⟩
    (ρ := ⟨ρ.bound, fun _ => ⟨ω, h.omega⟩⟩) (η := ρ) rfl).mp step
  exact (Formula.satisfies_mem_iff ..).mp ((Formula.satisfies_imp_iff ..).mp moved seed)

/-- 在同一目标层中恢复新的元组、树节点及恰好一个标签。 -/
theorem Tg_context_d.recover_seed_l {ω κ K X R η C : M.Domain} (h : Tg_context_d ω X η C)
    (source : Ep_source_d hZF ω κ K X R) (nc : Nonempty {x // M.mem x C})
    (ρ : Env (rt_model_l C nc) 22) (seed : Formula.satisfies ρ tc_recover_seed0_m) :
    Formula.satisfies ρ tc_recover_result0_m := by
  have kernel := ((Formula.satisfies_conj_iff ..).mp ((Formula.satisfies_conj_iff ..).mp
    ((Formula.satisfies_conj_iff ..).mp ((Formula.satisfies_conj_iff ..).mp
      ((Formula.satisfies_conj_iff ..).mp (h.read_l hZF source).2).2).2).2).2).2
  have kernel := (Formula.satisfies_conj_iff ..).mp kernel |>.1
  have step := (Formula.satisfies_forallClosure_iff (ℳ := rt_model_l C nc) (fun _ => ⟨ω, h.omega⟩)
    (.imp tc_recover_seed0_m tc_recover_result0_m)).mp kernel ρ.bound
  have moved := (Formula.closed_env_l (.imp tc_recover_seed0_m tc_recover_result0_m)
    ⟨tc_recover_seed0_closed_l, tc_recover_result0_closed_l⟩
    (ρ := ⟨ρ.bound, fun _ => ⟨ω, h.omega⟩⟩) (η := ρ) rfl).mp step
  exact (Formula.satisfies_imp_iff ..).mp moved seed

/-- 完整回答在当前层接受同一基底上的任意原查询代码。 -/
theorem Tg_context_d.reply_queries_l {ω κ K X R η C : M.Domain} (h : Tg_context_d ω X η C)
    (source : Ep_source_d hZF ω κ K X R) (nc : Nonempty {x // M.mem x C})
    (ρ : Env (rt_model_l C nc) 54) (round : Formula.satisfies ρ tg_round0_m) :
    Formula.satisfies ρ tg_reply_compare0_m := by
  have kernel := (h.read_l hZF source).2
  simp only [tg_kernel_m, Formula.satisfies_conj_iff] at kernel
  have step := (Formula.satisfies_forallClosure_iff (ℳ := rt_model_l C nc) (fun _ => ⟨ω, h.omega⟩)
    (.imp tg_round0_m tg_reply_compare0_m)).mp kernel.2.2.2.2.2.2 ρ.bound
  have moved := (Formula.closed_env_l (.imp tg_round0_m tg_reply_compare0_m)
    ⟨tg_round0_closed_l, tg_reply_compare0_closed_l⟩
    (ρ := ⟨ρ.bound, fun _ => ⟨ω, h.omega⟩⟩) (η := ρ) rfl).mp step
  exact (Formula.satisfies_imp_iff ..).mp moved round

/-- 任意给定参数集合进入内层；两层均由已有 ZFC 构造实际产生。 -/
theorem tg_context_l (hZFC : M.Models ZFC) {ω : M.Domain} (hω : M.IsOmega ω) (A : M.Domain) (Φ : List Lr_formula) :
    ∃ θ X R c K η C, M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) θ ∧
      V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) θ X ∧
      Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c X R ∧
      Ic_model_d (ZFC.models_zf_l hZFC) ω ω K X R ∧ Tg_context_d ω X η C ∧ M.mem A C ∧ ∀ q ∈ Φ, Lr_reflect_d q.2.val C := by
  let hZF := ZFC.models_zf_l hZFC
  let J := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨P, pair⟩ := KP.exists_pair (ZF.modelsKP hZF) ω A
  obtain ⟨η, C, rank, limit, hP, reflect⟩ := ZF.lr_finite_l J hZF (⟨0, tg_kernel_m, tg_kernel_closed_l⟩ :: Φ) P
  have trans := ZF.v_transitive_l J hZF rank
  have hωC := trans P hP ω ((pair ω).mpr (Or.inl rfl))
  have hAC := trans P hP A ((pair A).mpr (Or.inr rfl))
  obtain ⟨B, pair'⟩ := KP.exists_pair (ZF.modelsKP hZF) η C
  obtain ⟨θ, X, regular, above, outer, hB⟩ := ZFC.v_regular_cover_l J hZFC hω B
  obtain ⟨K, R, source⟩ := ic_regular_model_l hZFC hω above regular outer
  obtain ⟨c, code⟩ := source.source.code
  have hηX := source.source.transitive B hB η ((pair' η).mpr (Or.inl rfl))
  have hCX := source.source.transitive B hB C ((pair' C).mpr (Or.inr rfl))
  obtain ⟨D, F, hD, hF, cert, _⟩ := vr_source_l hZF outer regular.isLimitOrdinal
    (ZF.v_ordinal_height_l hZF outer limit.1 hηX) rank
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => ω⟩
  exact ⟨θ, X, R, c, K, η, C, regular, outer, code, source,
    ⟨hηX, hCX, ⟨D, F, hD, hF, fun t _ => cert t⟩, limit, hωC,
      (reflect ⟨0, tg_kernel_m, tg_kernel_closed_l⟩ (List.mem_cons_self ..)
        ρ (fun i => Fin.elim0 i)).mp ((Formula.satisfies_conj_iff ..).mpr
          ⟨tg_renewal_true_l hZFC ρ.free, (Formula.satisfies_conj_iff ..).mpr
            ⟨tc_transfer_true_l hZFC ρ.free, (Formula.satisfies_conj_iff ..).mpr
              ⟨ee_rebuild_true_l hZFC ρ.free, (Formula.satisfies_conj_iff ..).mpr
                ⟨tc_realize_true_l hZF ρ.free, (Formula.satisfies_conj_iff ..).mpr
                  ⟨tc_rigid_true_l hZF ρ.free, (Formula.satisfies_conj_iff ..).mpr
                    ⟨tc_recover_true_l hZF ρ.free, tg_reply_compare_true_l hZF ρ.free⟩⟩⟩⟩⟩⟩)⟩, hAC,
      fun q hq => reflect q (List.mem_cons_of_mem _ hq)⟩

end YesMetaZFC.SetTheory.LargeCardinal
