import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRenewalSyntax
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameReplyCompare
import YesMetaZFC.SetTheory.LargeCardinal.TypeContinueSyntax
import YesMetaZFC.SetTheory.LargeCardinal.TypeContinueRealizeSyntax
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRigidity
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRecoverySyntax
import YesMetaZFC.SetTheory.LargeCardinal.IterationCopyModel
import YesMetaZFC.SetTheory.LargeCardinal.IterationHistorySyntax
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderReadSource
import YesMetaZFC.Model.SetTheory.LevyReflection
import YesMetaZFC.SetTheory.CumulativeRegularCover
import YesMetaZFC.SetTheory.Card.FiniteParameters
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameSeedBound
import YesMetaZFC.Model.SetTheory.Internal.RelationRecord

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

/-- 当前结构中的七条原全称规则；结构可以使用任意实际成员关系。 -/
def Tg_kernel_d (N : Structure.{u}) : Prop :=
  ∀ ρ : Env N 0, Formula.satisfies ρ tg_kernel_m

/-- 已证更新规则组成同一反射核，可在给定地模型内部直接调用。 -/
theorem tg_kernel_true_l (hZFC : M.Models ZFC) (z : M.Domain) :
    Formula.satisfies (⟨Fin.elim0, fun _ => z⟩ : Env M 0) tg_kernel_m := by
  simp only [tg_kernel_m, Formula.satisfies_conj_iff]
  exact ⟨tg_renewal_true_l hZFC (fun _ => z), tc_transfer_true_l hZFC (fun _ => z),
    ee_rebuild_true_l hZFC (fun _ => z), tc_realize_true_l (ZFC.models_zf_l hZFC) (fun _ => z),
    tc_rigid_true_l (ZFC.models_zf_l hZFC) (fun _ => z), tc_recover_true_l (ZFC.models_zf_l hZFC) (fun _ => z),
    tg_reply_compare_true_l (ZFC.models_zf_l hZFC) (fun _ => z)⟩

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

/-- 存入内部历史的完整上下文；更新核仍是原来的有限反射句子。 -/
def tg_context_data_m {d} (ω X η C : Term d) : Formula 1 d := .conj
  (set[d] ⟪⌜η⌝ₛ ∈ ⌜X⌝ₛ ∧ ⌜C⌝ₛ ∈ ⌜X⌝ₛ ∧ ⌜pn_rank_m⌝ₚ(⌜X⌝ₛ, ⌜η⌝ₛ, ⌜C⌝ₛ) ∧
    ⌜Formula.isLimitOrdinal⌝ₚ(⌜η⌝ₛ) ∧ ⌜ω⌝ₛ ∈ ⌜C⌝ₛ⟫)
  (tg_context_m.bind (fun _ => C))

@[simp] theorem tg_context_data_closed_l {d} (ω X η C : Term d)
    (hw : ω.freeSupport = []) (hX : X.freeSupport = []) (hη : η.freeSupport = []) (hC : C.freeSupport = []) :
    (tg_context_data_m ω X η C).FreeClosed := by
  simp -implicitDefEqProofs [tg_context_data_m, Definitional.Formula.FreeClosed, hw, hX, hη, hC]
  exact tg_context_closed_l

theorem tg_context_data_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω X η C : Term d) :
    Formula.satisfies ρ (tg_context_data_m ω X η C) ↔
      Tg_context_d (ω.eval ρ) (X.eval ρ) (η.eval ρ) (C.eval ρ) := by
  simp only [tg_context_data_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    pn_rank_sat_l hKP, Formula.satisfies_isLimitOrdinal_iff, Formula.satisfies_bind]
  have eq := Formula.closed_env_l tg_context_m tg_context_closed_l
    (ρ := Definitional.Env.substitute ρ (fun _ => C))
    (η := ((⟨Fin.elim0, fun _ => ω.eval ρ⟩ : Env M 0).push (C.eval ρ)))
    (funext (Fin.cases rfl (fun i => Fin.elim0 i)))
  exact ⟨fun ⟨⟨a, b, c, d, e⟩, f⟩ => ⟨a, b, c, d, e, eq.mp f⟩,
    fun h => ⟨⟨h.height, h.member, h.rank, h.limit, h.omega⟩, eq.mpr h.kernel⟩⟩

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_context_d.kernel_l {ω X η C : M.Domain} (h : Tg_context_d ω X η C)
    (trans : M.TransitiveSet C) (nc : Nonempty {x // M.mem x C}) : Tg_kernel_d (rt_model_l C nc) := by
  intro ρ
  exact (sc_relative_sat_l trans nc tg_kernel_m tg_kernel_closed_l ρ
    ((⟨Fin.elim0, fun _ => ω⟩ : Env M 0).push C)
    .newest (fun i => .bound i.succ) rfl (fun i => Fin.elim0 i)).mp h.kernel

theorem Tg_context_d.read_l {ω κ K X R η C : M.Domain} (h : Tg_context_d ω X η C)
    (source : Ep_source_d hZF ω κ K X R) :
    Fs_read_d ω C ∧ Formula.satisfies
      (⟨Fin.elim0, fun _ => ⟨ω, h.omega⟩⟩ : Env (rt_model_l C ⟨⟨ω, h.omega⟩⟩) 0) tg_kernel_m := by
  have finite := source.rank_read_source_l hZF h.member h.rank h.limit h.omega
  exact ⟨finite, h.kernel_l finite.transitive _ _⟩

theorem Tg_context_d.map_l {ω X R c Y S d j η C : M.Domain} (h : Tg_context_d ω X η C)
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (mx : Smem_d I c X R) (my : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j) :
    ∃ η' C', Rd_entry_d η η' j ∧ Rd_entry_d C C' j ∧ Tg_context_d ω Y η' C' := by
  obtain ⟨η', hη', hη⟩ := hj.1.1.2.2 η h.height
  obtain ⟨C', hC', hC⟩ := hj.1.1.2.2 C h.member
  have hw := hj.omega_l I hZF hω hX hY mx my (hX C h.member ω h.omega)
  -- 更新核作为原关系中的整句搬运，因而仍覆盖目标中的全部新输入。
  have old : Rr_truth_d I X R tg_context_m (fun _ => C) :=
    (rr_truth_mem_l I hX mx tg_context_m tg_context_delta_l _).mpr ⟨fun _ => h.member,
      (Formula.closed_env_l tg_context_m tg_context_closed_l
        (ρ := ((⟨Fin.elim0, fun _ => ω⟩ : Env M 0).push C))
        (η := ⟨fun _ => C, fun _ => C⟩) (funext (Fin.cases rfl (fun i => Fin.elim0 i)))).mp h.kernel⟩
  have moved : Rr_truth_d I Y S tg_context_m (fun _ => C') :=
    old.map_l I hZF hω mx.1 my.1 hj tg_context_closed_l (fun _ => hC)
  have kernel := ((rr_truth_mem_l I hY my tg_context_m tg_context_delta_l _).mp moved).2
  have kernel := (Formula.closed_env_l tg_context_m tg_context_closed_l
    (ρ := (⟨fun _ => C', fun _ => C'⟩ : Env M 1))
    (η := ((⟨Fin.elim0, fun _ => ω⟩ : Env M 0).push C'))
    (funext (Fin.cases rfl (fun i => Fin.elim0 i)))).mp kernel
  exact ⟨η', C', hη, hC, hη', hC', (hj.hierarchy_l hZF hω hX hY mx my hη hC).mp h.rank,
    (hj.limit_l hZF hω hX hY mx my hη).mp h.limit,
    (hj.member_l I hZF hω mx my hw hC).mp h.omega, kernel⟩

/-- 原后继规则覆盖当前结构的全部新参数。 -/
theorem Tg_kernel_d.renew_l (h : Tg_kernel_d M) (ρ : Env M 38)
    (seed : Formula.satisfies ρ tg_seed0_m) : Formula.satisfies ρ tg_successor0_m := by
  have kernel := h ⟨Fin.elim0, ρ.free⟩
  simp only [tg_kernel_m, Formula.satisfies_conj_iff] at kernel
  exact (Formula.satisfies_imp_iff ..).mp
    ((Formula.satisfies_forallClosure_iff (ℳ := M) ρ.free (.imp tg_seed0_m tg_successor0_m)).mp kernel.1 ρ.bound) seed

/-- 继续分支读取原超过见证，产生实际像证书。 -/
theorem Tg_kernel_d.continue_l (h : Tg_kernel_d M) (ρ : Env M 28)
    (seed : Formula.satisfies ρ tc_seed0_m) : Formula.satisfies ρ tc_result0_m := by
  have kernel := h ⟨Fin.elim0, ρ.free⟩
  simp only [tg_kernel_m, Formula.satisfies_conj_iff] at kernel
  exact (Formula.satisfies_imp_iff ..).mp
    ((Formula.satisfies_forallClosure_iff (ℳ := M) ρ.free (.imp tc_seed0_m tc_result0_m)).mp kernel.2.1 ρ.bound) seed

/-- 原程序和名字列重新解释为同一四查询语言。 -/
theorem Tg_kernel_d.language_l (h : Tg_kernel_d M) (ρ : Env M 10)
    (seed : Formula.satisfies ρ ee_rebuild_seed_m) : Formula.satisfies ρ ee_language0_m := by
  have kernel := h ⟨Fin.elim0, ρ.free⟩
  simp only [tg_kernel_m, Formula.satisfies_conj_iff] at kernel
  exact (Formula.satisfies_imp_iff ..).mp
    ((Formula.satisfies_forallClosure_iff (ℳ := M) ρ.free (.imp ee_rebuild_seed_m ee_language0_m)).mp kernel.2.2.1 ρ.bound) seed

/-- 完整旧实现核验同一原子类型查询。 -/
theorem Tg_kernel_d.realize_seed_l (h : Tg_kernel_d M) (ρ : Env M 27)
    (seed : Formula.satisfies ρ tc_realize_seed0_m) : Formula.satisfies ρ tc_realize_result0_m := by
  have kernel := h ⟨Fin.elim0, ρ.free⟩
  simp only [tg_kernel_m, Formula.satisfies_conj_iff] at kernel
  exact (Formula.satisfies_imp_iff ..).mp
    ((Formula.satisfies_forallClosure_iff (ℳ := M) ρ.free (.imp tc_realize_seed0_m tc_realize_result0_m)).mp kernel.2.2.2.1 ρ.bound) seed

/-- 超过关系和 dcp 定义域给出原最大序数查询。 -/
theorem Tg_kernel_d.rigid_seed_l (h : Tg_kernel_d M) (ρ : Env M 29)
    (seed : Formula.satisfies ρ tc_rigid_seed0_m) : M.mem (ρ.bound 25) (ρ.bound 20) := by
  have kernel := h ⟨Fin.elim0, ρ.free⟩
  simp only [tg_kernel_m, Formula.satisfies_conj_iff] at kernel
  exact (Formula.satisfies_imp_iff ..).mp
    ((Formula.satisfies_forallClosure_iff (ℳ := M) ρ.free (.imp tc_rigid_seed0_m (.mem (.bound 25) (.bound 20)))).mp kernel.2.2.2.2.1 ρ.bound) seed

/-- 恢复原元组、树节点及恰好一个新标签。 -/
theorem Tg_kernel_d.recover_seed_l (h : Tg_kernel_d M) (ρ : Env M 22)
    (seed : Formula.satisfies ρ tc_recover_seed0_m) : Formula.satisfies ρ tc_recover_result0_m := by
  have kernel := h ⟨Fin.elim0, ρ.free⟩
  simp only [tg_kernel_m, Formula.satisfies_conj_iff] at kernel
  exact (Formula.satisfies_imp_iff ..).mp
    ((Formula.satisfies_forallClosure_iff (ℳ := M) ρ.free (.imp tc_recover_seed0_m tc_recover_result0_m)).mp kernel.2.2.2.2.2.1 ρ.bound) seed

/-- 完整回答接受同一基底上的全部原查询代码。 -/
theorem Tg_kernel_d.reply_queries_l (h : Tg_kernel_d M) (ρ : Env M 54)
    (seed : Formula.satisfies ρ tg_round0_m) : Formula.satisfies ρ tg_reply_compare0_m := by
  have kernel := h ⟨Fin.elim0, ρ.free⟩
  simp only [tg_kernel_m, Formula.satisfies_conj_iff] at kernel
  exact (Formula.satisfies_imp_iff ..).mp
    ((Formula.satisfies_forallClosure_iff (ℳ := M) ρ.free (.imp tg_round0_m tg_reply_compare0_m)).mp kernel.2.2.2.2.2.2 ρ.bound) seed

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
        ρ (fun i => Fin.elim0 i)).mp (tg_kernel_true_l hZFC ω)⟩, hAC,
      fun q hq => reflect q (List.mem_cons_of_mem _ hq)⟩

end YesMetaZFC.SetTheory.LargeCardinal
