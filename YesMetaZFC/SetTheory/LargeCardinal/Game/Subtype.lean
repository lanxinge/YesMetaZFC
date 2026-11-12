import YesMetaZFC.SetTheory.LargeCardinal.Game.RoundNativeScope
import YesMetaZFC.SetTheory.LargeCardinal.Types.OneStepDropImage
import YesMetaZFC.SetTheory.LargeCardinal.Types.ContinueRealizeSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Game.Rigidity
import YesMetaZFC.SetTheory.LargeCardinal.Game.RecoverySyntax
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Reflection
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.InitialPull
import YesMetaZFC.SetTheory.Card.FiniteParameters
import YesMetaZFC.Model.SetTheory.Internal.MembershipSlice
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawRankSource
import YesMetaZFC.SetTheory.LargeCardinal.Types.ElasticNumericTransfer
import YesMetaZFC.SetTheory.LargeCardinal.Types.PoolRead
import YesMetaZFC.SetTheory.CumulativeRelativeRead
import YesMetaZFC.SetTheory.CumulativeOrdinalHeight
import YesMetaZFC.Model.SetTheory.Types.Embedding
import YesMetaZFC.Model.SetTheory.Types.DropEmbedding
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyAnchor
import YesMetaZFC.Model.SetTheory.Relations.NativeSmemSlice
import YesMetaZFC.Model.SetTheory.Types.SubtypeReflect

/-! # 同一完整回答对原查询表的所有合法代码为真

查询表允许选取不同但语义相同的代码。完整类型的同一个实现把三条查询
还原为同一个根、秩界及末位条件，故无需假定两张查询表逐字相等。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_reply_compare0_m : Formula 1 54 :=
  let p : Fin 54 → Term 54 := Term.bound
  set[54] ⟪∀ r b h,
    ⌜tg_reply_base_m⌝ₚ(⌜p 16⌝ₛ, ⌜p 17⌝ₛ, ⌜p 23⌝ₛ, ⌜p 24⌝ₛ, r, b, h) →
    r ∈ ⌜p 11⌝ₛ ∧ b ∈ ⌜p 11⌝ₛ ∧ h ∈ ⌜p 11⌝ₛ⟫

@[simp] theorem tg_reply_compare0_closed_l : tg_reply_compare0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_reply_compare0_m, Definitional.Formula.FreeClosed]

def tg_reply_compare_m : Formula 1 0 := Formula.forallClosure 54 (.imp tg_round0_m tg_reply_compare0_m)

theorem tg_reply_compare_closed_l : tg_reply_compare_m.FreeClosed :=
  (Definitional.Formula.freeClosed_forallClosure _).mpr ⟨tg_round0_closed_l, tg_reply_compare0_closed_l⟩

theorem tg_reply_compare_true_l (hZF : M.Models ZF) (ε : FreeVarId → M.Domain) :
    Formula.satisfies (⟨Fin.elim0, ε⟩ : Env M 0) tg_reply_compare_m := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  apply (Formula.satisfies_forallClosure_iff ε _).mpr
  intro p
  apply (Formula.satisfies_imp_iff ..).mpr
  intro round
  obtain ⟨seed, data⟩ := (Formula.satisfies_conj_iff ..).mp round
  simp only [tg_seed0_m, Formula.satisfies_rename, tg_seed_m, Formula.satisfies_conj_iff] at seed
  have hω := (Formula.satisfies_isOmega_iff ..).mp seed.1
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, v_sigma_sat_l (ZF.modelsKP hZF), smem_sat_l I,
    tt_realized_sat_l I (ZF.modelsKP hZF), tg_reply_language_sat_l hZF] at data
  obtain ⟨_, _, _, _, rank, model, _, real, _, language, hr, hb, hh, _⟩ := data
  simp only [tg_reply_compare0_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, tg_reply_base_sat_l I (ZF.modelsKP hZF),
    Definitional.Term.eval_weaken]
  intro r b h base
  have hw := (tt_constants_finite_l hZF hω language.finite language.limit language.rank language.constants).1
  obtain ⟨root, bound, height⟩ := base.scope_l I (ZF.modelsKP hZF) real.pool hw
  obtain ⟨S, _, rS⟩ := real.tuple.2.1 (p 17) language.root_slot
  obtain ⟨α, _, rα⟩ := real.tuple.2.1 (p 23) language.last_slot
  have trans := v_transitive_l I rank
  exact ⟨(root.2 _ _ _ _ _ _ S model trans real rS).mpr
      ((language.root.2 _ _ _ _ _ _ S model trans real rS).mp hr),
    (bound.2 _ _ _ _ _ _ _ S α rank model real rS rα).mpr
      ((language.bound.2 _ _ _ _ _ _ _ S α rank model real rS rα).mp hb),
    (height.2 _ _ _ _ _ _ _ α rank model real rα).mpr
      ((language.height.2 _ _ _ _ _ _ _ α rank model real rα).mp hh)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原回答证书已经给出首个临界点的下界

只读取所属短扩展器公式中的 ω∈κ，不为读取这一事实另作一次树后继，
也不把该模型内部的超幂证书整体坍塌到背景。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem tg_image_omega_l {d} (ρ : Env M d) (ω κ δ l n U D u τ Q w b z r q h : Term d)
    (σ : Fin 7 → Term d) (valid : Formula.satisfies ρ (tg_image_m ω κ δ l n U D u τ Q w b z r q h σ)) :
    M.mem (ω.eval ρ) (κ.eval ρ) := by
  simp only [tg_image_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff] at valid
  obtain ⟨X, K, R, L, F, c, d, Y, T, j, κ', U', D', u', core, _⟩ := valid
  simp only [ti_image_m, Formula.satisfies_conj_iff] at core
  have loc := (Formula.satisfies_conj_iff ..).mp core.2.2.2.2.2.1 |>.1
  simp only [ex_local_m, Formula.satisfies_conj_iff] at loc
  have short := loc.2.2.2.2
  change Formula.satisfies _ (.conj _ _) at short
  have pre := (Formula.satisfies_conj_iff ..).mp short |>.1
  change Formula.satisfies _ (.conj _ (.conj _ (.conj _ _))) at pre
  have bound := ((Formula.satisfies_conj_iff ..).mp
    ((Formula.satisfies_conj_iff ..).mp ((Formula.satisfies_conj_iff ..).mp pre).2).2).1
  have bound := (Formula.satisfies_mem_iff ..).mp bound
  cases ω <;> cases κ <;> simpa [Definitional.Term.bind, fin_cases, Fin.cases, Fin.induction,
    Fin.induction.go, Fin.succ, Definitional.Term.weaken, Definitional.Term.rename, Definitional.Term.eval, Env.push] using bound

theorem tg_successor_omega_l (ρ : Env M 38) (valid : Formula.satisfies ρ tg_successor0_m) :
    M.mem (ρ.bound 0) (ρ.bound 5) := by
  simp only [tg_successor0_m, tg_successor_m, Formula.satisfies_exists_iff] at valid
  obtain ⟨τ, C, V, Q, w, η, Z, a, H, f₀, f₁, f₂, f₃, q₀, q₁, q₂, valid⟩ := valid
  simp only [tg_round_m, Formula.satisfies_conj_iff] at valid
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, image⟩ := valid
  exact tg_image_omega_l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ image

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 工作模型中的有限反射秩段

秩段、有限读写闭包和已证更新核都保存在当前模型的原关系中。初等图
整体搬运这些全称证书，覆盖后继中的全部新参数。弱工作根仍由原反射
构造给出；给定地模型使用同一接口，不要求高层载体外部传递。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_kernel_m : Formula 1 0 := .conj tg_renewal_m
  (.conj tc_transfer_m (.conj ee_rebuild_m (.conj tc_realize_m
    (.conj tc_rigid_m (.conj tc_recover_m (.conj tg_reply_compare_m eo_kernel_m))))))

theorem tg_kernel_closed_l : tg_kernel_m.FreeClosed :=
  ⟨tg_renewal_closed_l, tc_transfer_closed_l, ee_rebuild_closed_l, tc_realize_closed_l,
    tc_rigid_closed_l, tc_recover_closed_l, tg_reply_compare_closed_l, eo_kernel_closed_l⟩

/-- 当前结构中的八条原全称规则；结构可以使用任意实际成员关系。 -/
def Tg_kernel_d (N : Structure.{u}) : Prop :=
  ∀ ρ : Env N 0, Formula.satisfies ρ tg_kernel_m

/-- 已证更新规则组成同一反射核，可在给定地模型内部直接调用。 -/
theorem tg_kernel_true_l (hZFC : M.Models ZFC) (z : M.Domain) :
    Formula.satisfies (⟨Fin.elim0, fun _ => z⟩ : Env M 0) tg_kernel_m := by
  simp only [tg_kernel_m, Formula.satisfies_conj_iff]
  exact ⟨tg_renewal_true_l hZFC (fun _ => z), tc_transfer_true_l hZFC (fun _ => z),
    ee_rebuild_true_l hZFC (fun _ => z), tc_realize_true_l (ZFC.models_zf_l hZFC) (fun _ => z),
    tc_rigid_true_l (ZFC.models_zf_l hZFC) (fun _ => z), tc_recover_true_l (ZFC.models_zf_l hZFC) (fun _ => z),
    tg_reply_compare_true_l (ZFC.models_zf_l hZFC) (fun _ => z), eo_kernel_true_l hZFC (fun _ => z)⟩

def tg_context_m : Formula 1 1 := lr_rel_m tg_kernel_m .newest (fun i => .bound i.succ)

theorem tg_context_closed_l : tg_context_m.FreeClosed :=
  lr_rel_closed_l _ tg_kernel_closed_l _ _ rfl (fun i => Fin.elim0 i)

theorem tg_context_delta_l : tg_context_m.IsDelta0 := lr_rel_delta_l ..

/-- 原关系中的整句更新核覆盖反射层的全部输入，包括超幂产生的新参数。 -/
theorem tg_kernel_relation_l {𝒞 : OrderedPairConvention} (J : 𝒞.Interpretation M) {X R : M.Domain}
    (nx : ∃ x, M.mem x X) (C : (smdl_structure_l J (R := R) nx).Domain)
    (trans : (smdl_structure_l J (R := R) nx).TransitiveSet C)
    (nc : Nonempty {x : (smdl_structure_l J (R := R) nx).Domain //
      (smdl_structure_l J (R := R) nx).mem x C})
    (kernel : Rr_truth_d J X R tg_context_m (fun _ => C.val)) : Tg_kernel_d (rt_model_l C nc) := by
  have valid := (rr_truth_native_l J nx tg_context_m tg_context_closed_l (fun _ => C)).mp kernel
  intro ρ
  exact (sc_relative_sat_l trans nc tg_kernel_m tg_kernel_closed_l ρ
    ⟨fun _ => C, fun _ => C⟩ .newest (fun i => .bound i.succ) rfl (fun i => Fin.elim0 i)).mp valid

/-- 反射上下文只陈述当前原关系中的事实，不把对象码当作背景集合。 -/
structure Tg_context_d (I : kpair_convention_l.Interpretation M) (ω X R η C : M.Domain) : Prop where
  rank : Rr_truth_d (n := 1) I X R (v_sigma_m (.bound 1) .newest) (Fin.cases C (fun _ => η))
  limit : Rr_truth_d (n := 0) I X R (Formula.isLimitOrdinal .newest) (fun _ => η)
  finite : Rr_truth_d (n := 1) I X R (fs_read_m (.bound 1) .newest) (Fin.cases C (fun _ => ω))
  kernel : Rr_truth_d I X R tg_context_m (fun _ => C)

def tg_context_data_m {d} (ω X R η C : Term d) : Formula 1 d := .conj
  (rr_truth_m (𝒞 := kpair_convention_l) (n := 1) (v_sigma_m (.bound 1) .newest) X R (Fin.cases C (fun _ => η))) (.conj
  (rr_truth_m (𝒞 := kpair_convention_l) (n := 0) (Formula.isLimitOrdinal .newest) X R (fun _ => η)) (.conj
  (rr_truth_m (𝒞 := kpair_convention_l) (n := 1) (fs_read_m (.bound 1) .newest) X R (Fin.cases C (fun _ => ω)))
  (rr_truth_m (𝒞 := kpair_convention_l) tg_context_m X R (fun _ => C))))

@[simp] theorem tg_context_data_closed_l {d} (ω X R η C : Term d)
    (hw : ω.freeSupport = []) (hX : X.freeSupport = []) (hR : R.freeSupport = [])
    (hη : η.freeSupport = []) (hC : C.freeSupport = []) : (tg_context_data_m ω X R η C).FreeClosed := by
  refine ⟨rr_truth_closed_l _ (by simp -implicitDefEqProofs) _ _ _ hX hR (Fin.cases hC (fun _ => hη)),
    rr_truth_closed_l _ (by simp -implicitDefEqProofs) _ _ _ hX hR (fun _ => hη),
    rr_truth_closed_l _ (by simp -implicitDefEqProofs) _ _ _ hX hR (Fin.cases hC (fun _ => hw)),
    rr_truth_closed_l _ tg_context_closed_l _ _ _ hX hR (fun _ => hC)⟩

theorem tg_context_data_sat_l (I : kpair_convention_l.Interpretation M) {d} (ρ : Env M d) (ω X R η C : Term d) :
    Formula.satisfies ρ (tg_context_data_m ω X R η C) ↔
      Tg_context_d I (ω.eval ρ) (X.eval ρ) (R.eval ρ) (η.eval ρ) (C.eval ρ) := by
  simp only [tg_context_data_m, Formula.satisfies_conj_iff,
    rr_truth_sat_l I ρ (v_sigma_m (.bound 1) (.newest : Term 2)) (by simp -implicitDefEqProofs),
    rr_truth_sat_l I ρ (Formula.isLimitOrdinal (.newest : Term 1)) (by simp -implicitDefEqProofs),
    rr_truth_sat_l I ρ (fs_read_m (.bound 1) (.newest : Term 2)) (by simp -implicitDefEqProofs),
    rr_truth_sat_l I ρ tg_context_m tg_context_closed_l]
  have row (a b : Term d) : (fun i : Fin 2 => ((Fin.cases a (fun _ => b) : Fin 2 → Term d) i).eval ρ) =
      Fin.cases (a.eval ρ) (fun _ => b.eval ρ) := funext (Fin.cases rfl (fun _ => rfl))
  simp only [row]
  exact ⟨fun ⟨r, l, f, k⟩ => ⟨r, l, f, k⟩, fun h => ⟨h.rank, h.limit, h.finite, h.kernel⟩⟩

namespace Tg_context_d
variable {I : kpair_convention_l.Interpretation M} {ω X R η C : M.Domain} (h : Tg_context_d I ω X R η C)
include h

theorem height : M.mem η X := h.rank.elim fun m _ => m 1
theorem member : M.mem C X := h.rank.elim fun m _ => m 0
theorem omega_mem : M.mem ω X := h.finite.elim fun m _ => m 1

/-- 闭包在原结构内读取，适用于尚未坍塌的后继。 -/
theorem finite_l (nx : ∃ x, M.mem x X) (ext : Extensional (smdl_structure_l I (R := R) nx)) :
    Fs_read_d (M := smdl_structure_l I (R := R) nx) ⟨ω, h.omega_mem⟩ ⟨C, h.member⟩ := by
  let N := smdl_structure_l I (R := R) nx
  let v : Fin 2 → N.Domain := fun i => ⟨(Fin.cases C (fun _ => ω) : Fin 2 → M.Domain) i,
    Fin.cases h.member (fun _ => h.omega_mem) i⟩
  exact (fs_read_sat_l ext (⟨v, fun _ => v 0⟩ : Env N 2) (.bound 1) .newest).mp
    ((rr_truth_native_l I nx _ (by simp -implicitDefEqProofs) v).mp h.finite)

theorem kernel_l (nx : ∃ x, M.mem x X)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) nx).Domain //
      (smdl_structure_l I (R := R) nx).mem x ⟨C, h.member⟩}) :
    Tg_kernel_d (rt_model_l (M := smdl_structure_l I (R := R) nx) ⟨C, h.member⟩ nc) := by
  let N := smdl_structure_l I (R := R) nx
  let v : Fin 2 → N.Domain := fun i => ⟨(Fin.cases C (fun _ => ω) : Fin 2 → M.Domain) i,
    Fin.cases h.member (fun _ => h.omega_mem) i⟩
  have valid := (rr_truth_native_l I nx (fs_read_m (.bound 1) .newest)
    (by simp -implicitDefEqProofs) v).mp h.finite
  simp only [fs_read_m, Formula.satisfies_conj_iff, Formula.satisfies_isTransitive_iff] at valid
  exact tg_kernel_relation_l I nx ⟨C, h.member⟩ valid.1 nc h.kernel

/-- 只有实际隶属关系码才能把原关系事实读成背景中的集合事实。 -/
theorem omega_l (code : ∃ c, Smem_d I c X R) : M.mem ω C := by
  obtain ⟨c, model⟩ := code
  obtain ⟨m, valid⟩ := h.finite
  have edge : M.PairMember I ω C R := by
    simp only [fs_read_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at valid
    exact valid.2.1
  exact ((model.2 ω C).mp edge).2.2

theorem rank_l (hKP : M.Models KP) (trans : M.TransitiveSet X) (code : ∃ c, Smem_d I c X R) : Vr_d X η C := by
  obtain ⟨c, model⟩ := code
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, h.omega_mem⟩⟩
  let ρ : Env (rt_model_l X nx) 2 :=
    ⟨fun i => ⟨(Fin.cases C (fun _ => η) : Fin 2 → M.Domain) i,
      Fin.cases h.member (fun _ => h.height) i⟩, fun _ => ⟨ω, h.omega_mem⟩⟩
  obtain ⟨m, valid⟩ := h.rank
  have truth := (smem_formula_l I model nx _ ρ).mpr
    ((Formula.closed_env_l _ (by simp -implicitDefEqProofs)
      (funext fun i => Subtype.ext rfl)).mp valid)
  exact (vr_sat_l hKP trans nx ρ (.bound 1) .newest).mp truth

theorem limit_l (hKP : M.Models KP) (trans : M.TransitiveSet X) (code : ∃ c, Smem_d I c X R) : M.IsLimitOrdinal η := by
  obtain ⟨c, model⟩ := code
  let nx : Nonempty {x // M.mem x X} := ⟨⟨η, h.height⟩⟩
  let a : (rt_model_l X nx).Domain := ⟨η, h.height⟩
  obtain ⟨m, valid⟩ := h.limit
  have truth := (smem_formula_l I model nx _ (⟨fun _ => a, fun _ => a⟩ : Env (rt_model_l X nx) 1)).mpr
    ((Formula.closed_env_l _ (by simp -implicitDefEqProofs)
      (funext fun i => Subtype.ext rfl)).mp valid)
  exact (rt_limit_l trans nx hKP a).mp ((Formula.satisfies_isLimitOrdinal_iff ..).mp truth)

theorem kernel_mem_l (trans : M.TransitiveSet X) (code : ∃ c, Smem_d I c X R)
    (ct : M.TransitiveSet C) (nc : Nonempty {x // M.mem x C}) : Tg_kernel_d (rt_model_l C nc) := by
  obtain ⟨c, model⟩ := code
  have valid := ((rr_truth_mem_l I trans model tg_context_m tg_context_delta_l (fun _ => C)).mp h.kernel).2
  intro ρ
  exact (sc_relative_sat_l ct nc tg_kernel_m tg_kernel_closed_l ρ
    (⟨fun _ => C, fun _ => C⟩ : Env M 1) .newest (fun i => .bound i.succ) rfl (fun i => Fin.elim0 i)).mp valid

omit h in
/-- 给定真实反射层直接产生原关系上下文，有限闭包也进入同一结构。 -/
theorem of_mem_l (hKP : M.Models KP) {c : M.Domain} (trans : M.TransitiveSet X) (model : Smem_d I c X R)
    (hη : M.mem η X) (hC : M.mem C X) (rank : Vr_d X η C) (limit : M.IsLimitOrdinal η)
    (finite : Fs_read_d ω C)
    (kernel : Formula.satisfies ((⟨Fin.elim0, fun _ => ω⟩ : Env M 0).push C) tg_context_m) :
    Tg_context_d I ω X R η C := by
  obtain ⟨hr,hl,hf⟩ := ir_context_data_l I hKP trans model hη hC rank limit finite
  refine ⟨hr,hl,hf,?_⟩
  exact (rr_truth_mem_l I trans model tg_context_m tg_context_delta_l (fun _ => C)).mpr
    ⟨fun _ => hC, (Formula.closed_env_l tg_context_m tg_context_closed_l
      (ρ := ((⟨Fin.elim0, fun _ => ω⟩ : Env M 0).push C))
      (η := ⟨fun _ => C, fun _ => C⟩) (funext (Fin.cases rfl (fun i => Fin.elim0 i)))).mp kernel⟩

end Tg_context_d

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 已有真实源的字面读取；原关系上下文本身没有源闭性前提。 -/
theorem Tg_context_d.read_l {ω κ K X R η C : M.Domain} (h : Tg_context_d I ω X R η C)
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) :
    Fs_read_d ω C ∧ Formula.satisfies
      (⟨Fin.elim0, fun _ => ⟨ω, h.omega_l source.code⟩⟩ :
        Env (rt_model_l C ⟨⟨ω, h.omega_l source.code⟩⟩) 0) tg_kernel_m := by
  have finite := source.rank_read_source_l hZF h.member
    (h.rank_l (ZF.modelsKP hZF) source.transitive source.code) (h.limit_l (ZF.modelsKP hZF) source.transitive source.code) (h.omega_l source.code)
  exact ⟨finite, h.kernel_mem_l source.transitive source.code finite.transitive _ _⟩

/-- 同一初等图搬运完整反射上下文；内部 ω 随其实际像一起搬运。 -/
theorem Tg_context_d.map_l {Ω ω ω' X R c Y S d j η C : M.Domain} (h : Tg_context_d I ω X R η C)
    (hΩ : M.IsOmega Ω) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (hj : Smap_d I Ω c d X Y j) (hw : Rd_entry_d ω ω' j) :
    ∃ η' C', Rd_entry_d η η' j ∧ Rd_entry_d C C' j ∧ Tg_context_d I ω' Y S η' C' := by
  obtain ⟨η', _, hη⟩ := hj.1.1.2.2 η h.height
  obtain ⟨C', _, hC⟩ := hj.1.1.2.2 C h.member
  exact ⟨η', C', hη, hC,
    h.rank.map_l I hZF hΩ mx my hj (by simp -implicitDefEqProofs) (Fin.cases hC (fun _ => hη)),
    h.limit.map_l I hZF hΩ mx my hj (by simp -implicitDefEqProofs) (fun _ => hη),
    h.finite.map_l I hZF hΩ mx my hj (by simp -implicitDefEqProofs) (Fin.cases hC (fun _ => hw)),
    h.kernel.map_l I hZF hΩ mx my hj tg_context_closed_l (fun _ => hC)⟩

/-- 原后继规则覆盖当前结构的全部新参数。 -/
theorem Tg_kernel_d.renew_l (h : Tg_kernel_d M) (ρ : Env M 38)
    (seed : Formula.satisfies ρ tg_seed0_m) : Formula.satisfies ρ tg_successor0_m := by
  have kernel := h ⟨Fin.elim0, ρ.free⟩
  simp only [tg_kernel_m, Formula.satisfies_conj_iff] at kernel
  exact (Formula.satisfies_imp_iff ..).mp
    ((Formula.satisfies_forallClosure_iff (ℳ := M) ρ.free (.imp tg_seed0_m tg_successor0_m)).mp kernel.1 ρ.bound) seed

/-- 继续分支读取原超过见证，产生实际像证书。 -/
theorem Tg_kernel_d.continue_l (h : Tg_kernel_d M) (ρ : Env M 29)
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
    ((Formula.satisfies_forallClosure_iff (ℳ := M) ρ.free (.imp tg_round0_m tg_reply_compare0_m)).mp kernel.2.2.2.2.2.2.1 ρ.bound) seed

/-- 有限核中的原共同秩段构造，供所属原关系内的后继直接读取。 -/
theorem Tg_kernel_d.owned_l (h : Tg_kernel_d M) (ρ : Env M 0) : Formula.satisfies ρ eo_kernel_m := by
  have kernel := h ρ
  simp only [tg_kernel_m, Formula.satisfies_conj_iff] at kernel
  exact kernel.2.2.2.2.2.2.2

/-- 任意给定参数集合进入内层；两层均由已有 ZFC 构造实际产生。 -/
theorem tg_context_l (hZFC : M.Models ZFC) {ω : M.Domain} (hω : M.IsOmega ω) (A : M.Domain) (Φ : List Lr_formula) :
    ∃ θ X R c K η C, M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) θ ∧
      V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) θ X ∧
      Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c X R ∧
      Ic_model_d (ZFC.models_zf_l hZFC) ω ω K X R ∧ Tg_context_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω X R η C ∧ M.mem A C ∧ ∀ q ∈ Φ, Lr_reflect_d q.2.val C := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨θ,X,R,c,K,η,C,regular,outer,code,source,hηX,hCX,relative,limit,finite,hAC,reflect⟩ :=
    ir_context_l hZFC hω A (⟨0,tg_kernel_m,tg_kernel_closed_l⟩ :: Φ)
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => ω⟩
  exact ⟨θ, X, R, c, K, η, C, regular, outer, code, source,
    Tg_context_d.of_mem_l (ZF.modelsKP hZF) source.source.transitive code hηX hCX
      relative limit finite
      ((reflect ⟨0, tg_kernel_m, tg_kernel_closed_l⟩ (List.mem_cons_self ..)
        ρ (fun i => Fin.elim0 i)).mp (tg_kernel_true_l hZFC ω)), hAC,
      fun q hq => reflect q (List.mem_cons_of_mem _ hq)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 完整原共同层中的语言与查询域

实际秩历史与 KP 分离回收常量域、名字域及全部有限列。原语言的数值
程序经共同根传输，非数值查询经完整共同图传输，最后由目标反射核重建。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 源切片的原语言自动给出十个参数和整张名字列的共同层所属。 -/
private theorem tg_language_scope_l (hKP : M.Models KP) {ω η C L U : M.Domain}
    (hω : M.IsOmega ω) (rankC : V_d (kp_pair_l hKP) η C) (fs : Fs_read_d ω C)
    (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 10)
    (rank : V_d (kp_pair_l hKP) L U) (limit : M.IsLimitOrdinal L)
    (hw : (ρ.bound 0).val = ω) (member : M.mem (ρ.bound 1).val U)
    (valid : Formula.satisfies ρ ee_language0_m) :
    M.IsLimitOrdinal (ρ.bound 1).val ∧ M.mem (ρ.bound 2).val ω ∧
      (∀ i, M.mem (ρ.bound i).val U) ∧ Vr_d U (ρ.bound 1).val (ρ.bound 3).val ∧
      ∃ A E, M.mem A U ∧ M.mem E U ∧ Tn_names_d (ρ.bound 2).val (ρ.bound 4).val A ∧
        Fseq_space_d (kp_pair_l hKP) ω A E ∧ M.IsCartesianProduct (kp_pair_l hKP) (ρ.bound 5).val ω E := by
  let J := kp_pair_l hKP
  have ut : M.TransitiveSet U := v_transitive_l J rank
  simp only [ee_language0_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at valid
  obtain ⟨domain,lim,base,constants,hg,hh,hi,he,_,_,numeric⟩ := valid
  have pool := ((Formula.satisfies_conj_iff ..).mp ((Formula.satisfies_conj_iff ..).mp domain).2).1
  have limκ := (rt_limit_l fs.transitive nc hKP (ρ.bound 1)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp lim)
  have base : Vr_d C (ρ.bound 1).val (ρ.bound 3).val :=
    (vr_sat_l hKP fs.transitive nc ρ (.bound 1) (.bound 3)).mp base
  have full : V_d J (ρ.bound 1).val (ρ.bound 3).val := base.absolute_l hKP fs.transitive
    (ρ.bound 3).property (fun A B ha sub => v_subset_mem_l J rankC (A := A) (B := B) ha sub)
  have below := KP.v_ordinal_height_l hKP rank limκ.1 member
  have hB := (KP.v_compare_l hKP full rank (limit.1.transitive _ below)).2 below
  have hwU : M.mem ω U := v_subset_mem_l J rank member (hω.subset_limitOrdinal hKP limκ)
  have constants := (tt_constants0_sat_l hKP.1 ..).mp
    ((rt_model_delta_l fs.transitive nc (tt_constants0_delta_l (.bound 1) (.bound 3) (.bound 4)) ρ).mp constants)
  obtain ⟨P,power⟩ := v_power_exists_l J hKP rank hB
  have hP := v_power_mem_l J rank limit hB power
  have hU : M.mem (ρ.bound 4).val U := v_subset_mem_l J rank hP (fun x hx => by
    rcases (constants x).mp hx with hx | rfl
    · exact (power x).mpr (v_transitive_l J full x hx)
    · exact (power _).mpr (KP.v_ordinal_subset_l hKP full))
  have hn : M.mem (ρ.bound 2).val ω := by
    simp only [ee_numeric_m,Formula.satisfies_bind,ee_numeric0_m,Formula.satisfies_exists_iff,
      Formula.satisfies_conj_iff] at numeric
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,program,_⟩ := numeric
    simp only [ee_stretch_program_m,Formula.satisfies_bind,ee_stretch_program0_m,
      Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at program
    exact hw ▸ program.1
  obtain ⟨A,E,_,_,names,seq,product⟩ :=
    (fs.pool_sat_l hKP nc ρ (.bound 0) (.bound 2) (.bound 4) (.bound 5) hw).mp pool
  have hA : M.mem A U := names.rank_mem_l hKP hω rank limit hwU hn hU
  obtain ⟨D,hD,wd,ad⟩ := v_joint_bound_l J rank hwU hA
  have hE : M.mem E U := v_relations_mem_l J rank limit hD (fun f hf p hp => by
    obtain ⟨n,hn,fn⟩ := (seq f).mp hf
    obtain ⟨a,b,pair⟩ := fn.1.1 p hp
    exact ⟨a,wd a (hω.transitive hKP n hn a (fn.input_mem_of_pairMember ⟨p,pair,hp⟩)),
      b,ad b (fn.output_mem_of_pairMember ⟨p,pair,hp⟩),pair⟩)
  obtain ⟨D',hD',wd',ed⟩ := v_joint_bound_l J rank hwU hE
  have hPool : M.mem (ρ.bound 5).val U := v_relation_mem_l J rank limit hD' (fun p hp => by
    obtain ⟨a,ha,b,hb,pair⟩ := (product p).mp hp
    exact ⟨a,wd' a ha,b,ed b hb,pair⟩)
  have all : ∀ i, M.mem (ρ.bound i).val U := Fin.cases (hw.symm ▸ hwU)
    (Fin.cases member (Fin.cases (ut ω hwU _ hn) (Fin.cases hB (Fin.cases hU (Fin.cases hPool
      (Fin.cases (ut _ hPool _ hg) (Fin.cases (ut _ hPool _ hh)
        (Fin.cases (ut _ hPool _ hi) (Fin.cases (ut _ hPool _ he) (fun i => Fin.elim0 i))))))))))
  obtain ⟨F,hF,cert⟩ := KP.v_history_inside_l hKP rank limit member hB full
  exact ⟨limκ,hn,all,⟨_,F,hB,hF,fun x _ => cert x⟩,A,E,hA,hE,names,seq,product⟩

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 原语言沿完整共同层传输；全部有限查询列由真实乘积与子集闭性回收。 -/
theorem Ic_common_d.language_native_l
    {Ω b B R₀ c X R d Y S j k C₀ w₀ z₀ w z η C w' z' η' C' L l U V Γ t : M.Domain}
    (common : Ic_common_d I X R Y S L l U V Γ t)
    (hΩ : M.IsOmega Ω) (mb : Smdl_d I b B R₀) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (hX : (smdl_structure_l I (R := R) mx.2.1).Models KP)
    (hY : (smdl_structure_l I (R := S) my.2.1).Models KP)
    (left : Smap_d I Ω b c B X j) (right : Smap_d I Ω b d B Y k) (ext : Rf_ext_d I B R₀)
    (root : Rr_layer_d I Ω B R₀ w₀ z₀) (source : Rr_layer_d I Ω X R w z)
    (target : Rr_layer_d I Ω Y S w' z')
    (cx : Tg_context_d I w X R η C) (cy : Tg_context_d I w' Y S η' C')
    (iC : Rd_entry_d C₀ C j) (iD : Rd_entry_d C₀ C' k)
    (inside : ∀ x, Rd_entry_d x V S → Rd_entry_d x C' S)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) mx.2.1).Domain //
      (smdl_structure_l I (R := R) mx.2.1).mem x ⟨C,cx.member⟩})
    (ρ : Env (rt_model_l (M := smdl_structure_l I (R := R) mx.2.1) ⟨C,cx.member⟩ nc) 10)
    (hw : (ρ.bound 0).val.val = w) (hk : Rd_entry_d (ρ.bound 1).val.val U R)
    (valid : Formula.satisfies ρ ee_language0_m) :
    Rd_entry_d (ρ.bound 2).val.val w R ∧ (∀ i, Rd_entry_d (ρ.bound i).val.val U R) ∧
    ∃ nd : Nonempty {x : (smdl_structure_l I (R := S) my.2.1).Domain //
      (smdl_structure_l I (R := S) my.2.1).mem x ⟨C',cy.member⟩},
    ∃ θ : Env (rt_model_l (M := smdl_structure_l I (R := S) my.2.1) ⟨C',cy.member⟩ nd) 10,
      (∀ i, Rd_entry_d (ρ.bound i).val.val (θ.bound i).val.val t) ∧
      (θ.bound 0).val.val = w' ∧ Formula.satisfies θ ee_language0_m := by
  let Xn := smdl_structure_l I (R := R) mx.2.1
  let Yn := smdl_structure_l I (R := S) my.2.1
  let Un : Xn.Domain := ⟨U,common.left_rank.2.1⟩
  let Cn : Xn.Domain := ⟨C,cx.member⟩
  let Dn : Yn.Domain := ⟨C',cy.member⟩
  let wn : Xn.Domain := ⟨w,source.member⟩
  let wn' : Yn.Domain := ⟨w',target.member⟩
  have hwN : (ρ.bound 0).val = wn := Subtype.ext hw
  have fs : Fs_read_d wn Cn := cx.finite_l mx.2.1 hX.1
  have ft : Fs_read_d wn' Dn := cy.finite_l my.2.1 hY.1
  have ru : V_d (kp_pair_l hX) (⟨L,common.left_rank.1⟩ : Xn.Domain) Un :=
    (rr_rank_native_l I mx.2.1 hX _ _).mp common.left_rank
  have rc : V_d (kp_pair_l hX) (⟨η,cx.height⟩ : Xn.Domain) Cn :=
    (rr_rank_native_l I mx.2.1 hX _ _).mp ((rr_rank_truth_l I).mpr cx.rank)
  have rd : V_d (kp_pair_l hY) (⟨η',cy.height⟩ : Yn.Domain) Dn :=
    (rr_rank_native_l I my.2.1 hY _ _).mp ((rr_rank_truth_l I).mpr cy.rank)
  have limit : Xn.IsLimitOrdinal (⟨L,common.left_rank.1⟩ : Xn.Domain) :=
    (Formula.satisfies_isLimitOrdinal_iff ..).mp ((rr_truth_native_l I mx.2.1
      (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => (⟨L,common.left_rank.1⟩ : Xn.Domain))).mp common.limit)
  have limitD : Yn.IsLimitOrdinal (⟨η',cy.height⟩ : Yn.Domain) :=
    (Formula.satisfies_isLimitOrdinal_iff ..).mp ((rr_truth_native_l I my.2.1
      (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => (⟨η',cy.height⟩ : Yn.Domain))).mp cy.limit)
  have omega : Xn.IsOmega wn := source.omega_l I (ZF.modelsKP hZF) hΩ hX.1
  have omega' : Yn.IsOmega wn' := target.omega_l I (ZF.modelsKP hZF) hΩ hY.1
  have ut : Xn.TransitiveSet Un := v_transitive_l (kp_pair_l hX) ru
  obtain ⟨limκ,hn,low,rank,A,E,hA,hE,names,seq,product⟩ :=
    tg_language_scope_l hX omega rc fs nc ρ ru limit hwN hk valid
  have hwU : Xn.mem wn Un := Eq.mp (congrArg (fun a : Xn.Domain => Xn.mem a Un) hwN) (low 0)
  have ey := right.extensional_l hZF hΩ mb my ext
  have digits := common.layer_image_l (ZF.modelsKP hZF) mx.2.1 ey source target ut hwU
  let nu : Nonempty {x : Xn.Domain // Xn.mem x Un} := ⟨⟨wn,hwU⟩⟩
  let nd : Nonempty {y : Yn.Domain // Yn.mem y Dn} := ⟨⟨wn',ft.omega_mem⟩⟩
  have values (a : Xn.Domain) (ha : Xn.mem a Un) :
      ∃ y : (rt_model_l Dn nd).Domain, Rd_entry_d a.val y.val.val t := by
    have haΓ := (common.carrier a.val).mpr ⟨a.property,ha⟩
    obtain ⟨y,hy,ay⟩ := common.injection.1.2.2 a.val haΓ
    exact ⟨⟨⟨y,hy⟩,inside y ((common.image y).mpr ⟨a.val,haΓ,ay⟩)⟩,ay⟩
  obtain ⟨v,points⟩ := Classical.axiomOfChoice (fun i => values (ρ.bound i).val (low i))
  let θ : Env (rt_model_l Dn nd) 10 := ⟨v,fun _ => ⟨wn',ft.omega_mem⟩⟩
  have hw' : (θ.bound 0).val.val = w' :=
    common.injection.1.1.2 w _ w' (hw ▸ points 0) digits.1
  have hwY : (θ.bound 0).val = wn' := Subtype.ext hw'
  obtain ⟨A',AA⟩ := values A hA
  obtain ⟨E',EE⟩ := values E hE
  -- 有界结构数据直接沿完整前驱图搬运，不把任意参数误当作根的像。
  have move {n} (φ : Formula 1 n) (closed : φ.FreeClosed) (delta : φ.IsDelta0)
      (a : Env Xn n) (b : Env Yn n) (ha : ∀ i, Xn.mem (a.bound i) Un)
      (ab : ∀ i, Rd_entry_d (a.bound i).val (b.bound i).val t) :
      Formula.satisfies a φ ↔ Formula.satisfies b φ := by
    let aU : Env (rt_model_l Un nu) n := ⟨fun i => ⟨a.bound i,ha i⟩,fun _ => ⟨wn,hwU⟩⟩
    exact (Formula.closed_env_l φ closed (ρ := a) (η := image_env_l Subtype.val aU) rfl).trans
      (rr_native_delta_l I mx.2.1 my.2.1 Un ut nu common.carrier common.injection common.pred
        φ closed delta aU b ab)
  let a : Env Xn 10 := image_env_l Subtype.val ρ
  let b : Env Yn 10 := image_env_l Subtype.val θ
  have limκ' : Yn.IsLimitOrdinal (θ.bound 1).val :=
    (KP.limit0_sat_l hY b (.bound 1)).mp
      ((move (KP.limit0_m (.bound 1)) (by simp -implicitDefEqProofs) (KP.limit0_delta_l _) a b low points).mp
        ((KP.limit0_sat_l hX a (.bound 1)).mpr limκ))
  let an : Env Xn 3 := ⟨Fin.cases A (Fin.cases (ρ.bound 4).val (fun _ => (ρ.bound 2).val)),fun _ => wn⟩
  let bn : Env Yn 3 := ⟨Fin.cases A'.val (Fin.cases (θ.bound 4).val (fun _ => (θ.bound 2).val)),fun _ => wn'⟩
  have names' : Tn_names_d (θ.bound 2).val (θ.bound 4).val A'.val :=
    (tn_names0_sat_l hY bn (.bound 2) (.bound 1) .newest).mp
      ((move (tn_names0_m (.bound 2) (.bound 1) .newest) (by simp -implicitDefEqProofs)
        (tn_names0_delta_l ..) an bn (Fin.cases hA (Fin.cases (low 4) (fun _ => low 2)))
          (Fin.cases AA (Fin.cases (points 4) (fun _ => points 2)))).mp
            ((tn_names0_sat_l hX an (.bound 2) (.bound 1) .newest).mpr names))
  let ap : Env Xn 3 := ⟨Fin.cases (ρ.bound 5).val (Fin.cases E (fun _ => wn)),fun _ => wn⟩
  let bp : Env Yn 3 := ⟨Fin.cases (θ.bound 5).val (Fin.cases E'.val (fun _ => wn')),fun _ => wn'⟩
  have product' : Yn.IsCartesianProduct (kp_pair_l hY) (θ.bound 5).val wn' E'.val :=
    (sh_product_sat_l hY bp .newest (.bound 2) (.bound 1)).mp
      ((move (sh_product_m .newest (.bound 2) (.bound 1)) (by simp -implicitDefEqProofs)
        (sh_product_delta_l ..) ap bp (Fin.cases (low 5) (Fin.cases hE (fun _ => hwU)))
          (Fin.cases (points 5) (Fin.cases EE (fun _ => digits.1)))).mp
            ((sh_product_sat_l hX ap .newest (.bound 2) (.bound 1)).mpr product))
  -- 反向有限列不预设属于共同层：先用实际乘积界，再由目标子集闭性回收。
  have seq' : Fseq_space_d (kp_pair_l hY) wn' A'.val E'.val := by
    intro f'
    constructor
    · intro hf'
      obtain ⟨f,hf,ff⟩ := (common.pred E.val E'.val.val EE f'.val).mp hf'
      let fn : Xn.Domain := ⟨f,(mx.2.2.2 f E.val hf).1⟩
      obtain ⟨n,hn,fnf⟩ := (seq fn).mp hf
      obtain ⟨n',nn⟩ := values n (ut wn hwU n hn)
      have hn' : Yn.mem n'.val wn' := (common.pred w w' digits.1 n'.val.val).mpr ⟨n.val,hn,nn⟩
      exact ⟨n'.val,hn',fn0_function_l hY
        (rr_native_function_l I mx.2.1 my.2.1 hX.1 hY.1 Un ut common.carrier common.injection
          common.pred n A fn n'.val A'.val f' nn AA ff (fn0_of_function_l hX fnf)).1⟩
    · rintro ⟨n',hn',fnf⟩
      obtain ⟨n,hn,nn⟩ := (common.pred w w' digits.1 n'.val).mp hn'
      let n₀ : Xn.Domain := ⟨n,(mx.2.2.2 n w hn).1⟩
      obtain ⟨P,hP,prod⟩ := KP.v_product_exists_l hX ru limit (ut wn hwU n₀ hn) hA
      obtain ⟨f,_,ff,fn⟩ := rr_cross_capture_l I mx.2.1 my.2.1 hX hY.1 Un n₀ A P ut
        common.carrier common.injection common.image common.pred common.right_closed hP prod
        n' A'.val f' nn AA (fn0_of_function_l hY fnf)
      exact (common.pred E.val E'.val.val EE f'.val).mpr
        ⟨f.val,(seq f).mpr ⟨n₀,hn,fn0_function_l hX fn⟩,ff⟩
  -- 原秩历史经同一图完整搬运，再在目标反射层中取得其实际历史。
  have rawRank := rr_native_rank_value_l I mx.2.1 my.2.1 hY.1 Un (ρ.bound 1).val (ρ.bound 3).val
    ut common.carrier common.injection common.image common.pred common.right_closed (low 1) (low 3)
    (points 1) (points 3)
      ((vr_sat_l hX ut ⟨⟨(ρ.bound 1).val,low 1⟩⟩ _ (.bound 1) .newest).mpr rank)
  have fullRank : V_d (kp_pair_l hY) (θ.bound 1).val (θ.bound 3).val :=
    (rr_rank_native_l I my.2.1 hY _ _).mp rawRank
  obtain ⟨F,hF,cert⟩ := KP.v_history_inside_l hY rd limitD (θ.bound 1).property (θ.bound 3).property fullRank
  have rankD : Vr_d Dn (θ.bound 1).val (θ.bound 3).val :=
    ⟨_,F,(θ.bound 3).property,hF,fun x _ => cert x⟩
  have parts := valid
  simp only [ee_language0_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at parts
  obtain ⟨_,_,_,constants,_,_,_,he,_,_,numeric⟩ := parts
  have constants' : Formula.satisfies θ (tt_constants0_m (.bound 1) (.bound 3) (.bound 4)) :=
    (rt_model_delta_l ft.transitive nd (tt_constants0_delta_l ..) θ).mpr
      ((move (tt_constants0_m (.bound 1) (.bound 3) (.bound 4)) (by simp -implicitDefEqProofs)
        (tt_constants0_delta_l ..) a b low points).mp
          ((rt_model_delta_l fs.transitive nc (tt_constants0_delta_l ..) ρ).mp constants))
  let pick : Fin 8 → Term 10 := Fin.cases (.bound 0) (Fin.cases (.bound 1) (Fin.cases (.bound 2) (Fin.cases (.bound 4)
    (Fin.cases (.bound 6) (Fin.cases (.bound 7) (Fin.cases (.bound 8) (fun _ => .bound 9)))))))
  let ρ₀ := Definitional.Env.substitute ρ pick
  let θ₀ := Definitional.Env.substitute θ pick
  have same : ∀ i, Rd_entry_d (ρ₀.bound i).val.val (θ₀.bound i).val.val t :=
    Fin.cases (points 0) (Fin.cases (points 1) (Fin.cases (points 2) (Fin.cases (points 4)
      (Fin.cases (points 6) (Fin.cases (points 7) (Fin.cases (points 8) (fun _ => points 9)))))))
  have moved := common.numeric_l hZF hΩ mb mx my hX hY left right ext root source target Cn Dn
    fs.transitive ft.transitive nc nd iC iD ρ₀ θ₀ same hw inside A hA names
      ((Formula.satisfies_bind ρ pick ee_numeric0_m).mp numeric)
  refine ⟨hn,low,nd,θ,points,hw',(cy.kernel_l my.2.1 nd).language_l θ ?_⟩
  simp only [ee_rebuild_seed_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff]
  exact ⟨(Formula.satisfies_isOmega_iff ..).mpr (rt_omega_l ft.transitive nd hY.1 _ (hwY.symm ▸ omega')),
    (Formula.satisfies_isLimitOrdinal_iff ..).mpr ((rt_limit_l ft.transitive nd hY _).mpr limκ'),
    (vr_sat_l hY ft.transitive nd θ (.bound 1) (.bound 3)).mpr rankD,constants',
    (ft.pool_sat_l hY nd θ (.bound 0) (.bound 2) (.bound 4) (.bound 5) hwY).mpr
      ⟨A'.val,E'.val,A'.property,E'.property,names',seq',product'⟩,
    (common.pred _ _ (points 5) _).mpr ⟨_,he,points 9⟩,
    (Formula.satisfies_bind θ pick ee_numeric0_m).mpr moved⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 共同秩段中的原弹性语言

相对秩历史识别同一常量域，有限闭性回收同一查询域。自然数程序沿共同根
传输，实际列图在传递层之间读取；目标反射句子重新给出完整语言。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω X Y η C η' D : M.Domain} (nc : Nonempty {x // M.mem x C})
  (ρ : Env (rt_model_l C nc) 10)
local notation "p" => (fun i => Subtype.val (Env.bound ρ i))

/-- 原常量域、完整查询域及其名字列都属于包含 κ 的极限秩段。 -/
theorem Tg_context_d.language_rank_l {κ K R L W : M.Domain}
    (context : Tg_context_d I ω X R η C) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (hW : M.mem W X) (rank : Vr_d X L W) (hL : M.IsLimitOrdinal L)
    (hwW : M.mem ω W) (hkW : M.mem (p 1) W)
    (hw : p 0 = ω) (language : Formula.satisfies ρ ee_language0_m) :
    M.IsLimitOrdinal (p 1) ∧ M.mem (p 2) ω ∧ (∀ i, M.mem (p i) W) ∧ Vr_d W (p 1) (p 3) ∧
      ∃ A E, M.mem A W ∧ M.mem E W ∧ Tn_names_d (p 2) (p 4) A ∧
        Fseq_space_d I ω A E ∧ M.IsCartesianProduct I (p 5) ω E := by
  have fs := (context.read_l hZF source).1
  have wt := rank.transitive_l source.transitive hW
  simp only [ee_language0_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at language
  obtain ⟨domain, limit, base, constants, hg, hh, hi, he, _, _, numeric⟩ := language
  have pool := ((Formula.satisfies_conj_iff ..).mp ((Formula.satisfies_conj_iff ..).mp domain).2).1
  have hκ := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) _).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp limit)
  have vr := (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc ρ (.bound 1) (.bound 3)).mp base
  have vrX := (context.rank_l (ZF.modelsKP hZF) source.transitive source.code).of_rank_l source.transitive context.member (ρ.bound 3).property vr
  have hBX := source.transitive C context.member (p 3) (ρ.bound 3).property
  obtain ⟨hBW, vrW⟩ := rank.rank_l hZF source.transitive hW hL hkW hBX vrX
  have cons := (rt_model_delta_l fs.transitive nc (tt_constants0_delta_l ..) ρ).mp constants
  simp only [tt_constants0_sat_l hZF.1, @eval_image_env_l (rt_model_l C nc) M Subtype.val] at cons
  obtain ⟨c, Q, model⟩ := smdl_membership_l I hZF ⟨ω, hwW⟩
  have theory := source.rank_theory_l hZF hW rank hL model
  obtain ⟨U, hUW, insert⟩ := (theory.algebra_l _ (ZF.modelsKP hZF) wt model).insert_l hBW hkW
  have eqU := hZF.1.eq_of_same_members U (p 4) (fun a => (insert a).trans (cons a).symm)
  have hUW : M.mem (p 4) W := eqU ▸ hUW
  have hn : M.mem (p 2) ω := by
    simp only [ee_numeric_m, Formula.satisfies_bind, ee_numeric0_m, Formula.satisfies_exists_iff,
      Formula.satisfies_conj_iff] at numeric
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, pe, _⟩ := numeric
    simp only [ee_stretch_program_m, Formula.satisfies_bind, ee_stretch_program0_m,
      Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pe
    exact hw ▸ pe.1
  have hnW := wt ω hwW (p 2) hn
  obtain ⟨A, E, _, _, names, seq, product⟩ :=
    (fs.pool_sat_l (ZF.modelsKP hZF) nc ρ (.bound 0) (.bound 2) (.bound 4) (.bound 5) hw).mp pool
  obtain ⟨hPW, poolW⟩ := source.pool_rank_l hZF hW rank hL hwW hnW hUW ⟨A, E, names, seq, product⟩
  have all : ∀ i, M.mem (p i) W := Fin.cases (hw.symm ▸ hwW)
    (Fin.cases hkW (Fin.cases hnW (Fin.cases hBW (Fin.cases hUW (Fin.cases hPW
      (Fin.cases (wt _ hPW _ hg) (Fin.cases (wt _ hPW _ hh)
        (Fin.cases (wt _ hPW _ hi) (Fin.cases (wt _ hPW _ he) (fun i => Fin.elim0 i))))))))))
  exact ⟨hκ, hn, all, vrW, poolW⟩

theorem Tg_context_d.language_peer_l {r B R w z x S y T π σ C₀ κ K κ' K' L W : M.Domain}
    (context : Tg_context_d I ω X S η C) (target : Tg_context_d I ω Y T η' D)
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X S) (next : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ' K' Y T)
    (numbers : Rr_layer_d I ω B R w z) (rootExt : Rf_ext_d I B R)
    (mb : Smdl_d I r B R) (mx : Smem_d I x X S) (my : Smem_d I y Y T)
    (j : Smap_d I ω r x B X π) (k : Smap_d I ω r y B Y σ)
    (iC : Rd_entry_d C₀ C π) (iD : Rd_entry_d C₀ D σ)
    (hW : M.mem W X) (rank : Vr_d X L W) (hW' : M.mem W Y) (rank' : Vr_d Y L W)
    (hL : M.IsLimitOrdinal L) (hwW : M.mem ω W) (hkW : M.mem (p 1) W) (hWD : M.mem W D)
    (hw : p 0 = ω) (language : Formula.satisfies ρ ee_language0_m) :
    M.mem (p 2) ω ∧ (∀ i, M.mem (p i) W) ∧ ∃ nd : Nonempty {a // M.mem a D}, ∃ θ : Env (rt_model_l D nd) 10,
      (∀ i, (θ.bound i).val = p i) ∧ Formula.satisfies θ ee_language0_m := by
  have fs := (context.read_l hZF source).1
  have ft := (target.read_l hZF next).1
  obtain ⟨hκ, hn, all, vrW, N, F, hNW, hFW, names', seq', product'⟩ :=
    context.language_rank_l hZF nc ρ source hW rank hL hwW hkW hw language
  have hBW := all 3
  have inside a (ha : M.mem a W) := ft.transitive W hWD a ha
  simp only [ee_language0_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at language
  obtain ⟨_, _, _, constants, _, _, _, he, _, _, numeric⟩ := language
  have cons := (rt_model_delta_l fs.transitive nc (tt_constants0_delta_l ..) ρ).mp constants
  simp only [tt_constants0_sat_l hZF.1, @eval_image_env_l (rt_model_l C nc) M Subtype.val] at cons
  let nd : Nonempty {a // M.mem a D} := ⟨⟨ω, (target.omega_l next.code)⟩⟩
  let θ : Env (rt_model_l D nd) 10 := ⟨fun i => ⟨p i, inside _ (all i)⟩, fun _ => ⟨ω, (target.omega_l next.code)⟩⟩
  let pick : Fin 8 → Term 10 := Fin.cases (.bound 0) (Fin.cases (.bound 1) (Fin.cases (.bound 2) (Fin.cases (.bound 4)
    (Fin.cases (.bound 6) (Fin.cases (.bound 7) (Fin.cases (.bound 8) (fun _ => .bound 9)))))))
  let ρ₀ := Definitional.Env.substitute ρ pick
  let θ₀ := Definitional.Env.substitute θ pick
  have code : Formula.satisfies ρ₀ ee_numeric0_m := (Formula.satisfies_bind ρ pick ee_numeric0_m).mp numeric
  have same : ∀ i, (ρ₀.bound i).val = (θ₀.bound i).val := by
    intro i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))) i
  have moved := ee_numeric_transfer_l hZF source.omega numbers rootExt source.transitive next.transitive mb mx my
    j k iC iD fs.transitive ft.transitive nc nd ρ₀ θ₀ same hw (inside _ hNW) names' code
  have vrY := rank'.of_rank_l next.transitive hW' hBW vrW
  have hBY := next.transitive W hW' (p 3) hBW
  have vrD := ((target.rank_l (ZF.modelsKP hZF) next.transitive next.code).rank_l hZF next.transitive target.member (target.limit_l (ZF.modelsKP hZF) next.transitive next.code) (inside _ hkW) hBY vrY).2
  refine ⟨hn, all, nd, θ, fun _ => rfl, (target.kernel_mem_l next.transitive next.code (target.read_l hZF next).1.transitive nd).language_l θ ?_⟩
  simp only [ee_rebuild_seed_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff]
  refine ⟨(Formula.satisfies_isOmega_iff ..).mpr (rt_omega_l ft.transitive nd hZF.1 _
      (show M.IsOmega (p 0) from hw.symm ▸ source.omega)),
    (Formula.satisfies_isLimitOrdinal_iff ..).mpr ((rt_limit_l ft.transitive nd (ZF.modelsKP hZF) _).mpr hκ),
    (vr_sat_l (ZF.modelsKP hZF) ft.transitive nd θ (.bound 1) (.bound 3)).mpr vrD, ?_, ?_, he,
    (Formula.satisfies_bind θ pick ee_numeric0_m).mpr moved⟩
  · apply (rt_model_delta_l ft.transitive nd (tt_constants0_delta_l ..) θ).mpr
    exact (tt_constants0_sat_l hZF.1 ..).mpr cons
  · exact (ft.pool_sat_l (ZF.modelsKP hZF) nd θ (.bound 0) (.bound 2) (.bound 4) (.bound 5) hw).mpr
      ⟨N, F, inside _ hNW, inside _ hFW, names', seq', product'⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 继续分支中同一候选的完整证书

原语言与原 dcp 弹性一起进入新反射层。投影集合在目标内由分离构造，
再用字面唯一性识别两边的 dcp；不假定它已有语义实现。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

-- 两个新位置为完整候选 u 及元数 m，后十个位置保留原语言。
def tg_candidate0_m : Formula 1 12 := .conj
  (ee_language0_m.rename (fun i => i.succ.succ))
  (tg_elastic_m (.bound 4) (.bound 1) (.bound 7) (.bound 8) (.bound 9) (.bound 10) (.bound 11) (.bound 0))

theorem tg_candidate0_closed_l : tg_candidate0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_candidate0_m, Definitional.Formula.FreeClosed]

theorem tg_candidate_sat_l (hZFC : M.Models ZFC) (ρ : Env M 12) :
    Formula.satisfies ρ tg_candidate0_m ↔
      Ee_language_d (ZFC.models_zf_l hZFC) (ρ.bound 2) (ρ.bound 3) (ρ.bound 4) (ρ.bound 5) (ρ.bound 6) (ρ.bound 7)
        ⟨ρ.bound 8, ρ.bound 9, ρ.bound 10, ρ.bound 11⟩ ∧
      Tg_elastic_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) (ρ.bound 4) (ρ.bound 1) (ρ.bound 7)
        ⟨ρ.bound 8, ρ.bound 9, ρ.bound 10, ρ.bound 11⟩ (ρ.bound 0) := by
  simp only [tg_candidate0_m, Formula.satisfies_conj_iff, Formula.satisfies_rename, ee_language0_sat_l hZFC, tg_elastic_sat_l (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) (ZFC.models_zf_l hZFC).1]
  rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω X Y η C η' D : M.Domain} (nc : Nonempty {a // M.mem a C}) (ρ : Env (rt_model_l C nc) 12)
local notation "p" => (fun i => Subtype.val (Env.bound ρ i))

theorem Tg_context_d.candidate_peer_l {r B R w z x S y T π σ C₀ κ K κ' K' L W : M.Domain}
    (context : Tg_context_d I ω X S η C) (target : Tg_context_d I ω Y T η' D)
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X S) (next : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ' K' Y T)
    (numbers : Rr_layer_d I ω B R w z) (rootExt : Rf_ext_d I B R)
    (mb : Smdl_d I r B R) (mx : Smem_d I x X S) (my : Smem_d I y Y T)
    (j : Smap_d I ω r x B X π) (k : Smap_d I ω r y B Y σ)
    (iC : Rd_entry_d C₀ C π) (iD : Rd_entry_d C₀ D σ)
    (hW : M.mem W X) (rank : Vr_d X L W) (hW' : M.mem W Y) (rank' : Vr_d Y L W)
    (hL : M.IsLimitOrdinal L) (hwW : M.mem ω W) (hkW : M.mem (p 3) W) (hWD : M.mem W D)
    (hw : p 2 = ω) (hu : M.mem (p 0) D) (valid : Formula.satisfies ρ tg_candidate0_m) :
    M.mem (p 1) ω ∧ (∀ i : Fin 10, M.mem (p i.succ.succ) W) ∧
      ∃ nd : Nonempty {a // M.mem a D}, ∃ θ : Env (rt_model_l D nd) 12,
        (∀ i, (θ.bound i).val = p i) ∧ Formula.satisfies θ tg_candidate0_m := by
  obtain ⟨language, elastic⟩ := (Formula.satisfies_conj_iff ..).mp valid
  let χ := Env.reindex ρ (fun i : Fin 10 => i.succ.succ)
  have language : Formula.satisfies χ ee_language0_m := (Formula.satisfies_rename ..).mp language
  obtain ⟨hn, low, nd, χ', same, moved⟩ := context.language_peer_l hZF nc χ target source next
    numbers rootExt mb mx my j k iC iD hW rank hW' rank' hL hwW hkW hWD hw language
  have fs := (context.read_l hZF source).1
  have ft := (target.read_l hZF next).1
  simp only [tg_elastic_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff] at elastic
  obtain ⟨v, drop, elastic⟩ := elastic
  have drop := (td_dcp_source_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) fs.transitive nc fs.pair
    (ρ.push v) (.bound 5) (.bound 2) (.bound 8) (.bound 1) (.bound 0)).mp drop
  have elastic := (ee_elastic_absolute_l fs.transitive nc (ρ.push v)
    (.bound 9) (.bound 10) (.bound 11) (.bound 12) (.bound 0)).mp elastic
  obtain ⟨m, sm, hm⟩ := source.omega.1.2 (p 4) hn
  have eqm := hZF.1.eq_of_same_members m (p 1) (fun a => (sm a).trans (drop.1 a).symm)
  have hmω : M.mem (p 1) ω := eqm ▸ hm
  have hm : M.mem (p 1) D := ft.transitive ω (target.omega_l next.code) (p 1) hmω
  have tail (i : Fin 10) : M.mem (p i.succ.succ) D :=
    Eq.mp (congrArg (fun a => M.mem a D) (same i)) (χ'.bound i).property
  have hp : ∀ i : Fin 12, M.mem (p i) D := Fin.cases hu (Fin.cases hm tail)
  let θ : Env (rt_model_l D nd) 12 := ⟨fun i => ⟨p i, hp i⟩, fun _ => ⟨ω, (target.omega_l next.code)⟩⟩
  have sameEnv : χ'.bound = (Env.reindex θ (fun i : Fin 10 => i.succ.succ)).bound := by
    funext i
    exact Subtype.ext (same i)
  have lang : Formula.satisfies θ (ee_language0_m.rename (fun i => i.succ.succ)) :=
    (Formula.satisfies_rename ..).mpr ((Formula.closed_env_l ee_language0_m ee_language0_closed_l sameEnv).mp moved)
  obtain ⟨c, Q, model⟩ := smdl_membership_l I hZF ⟨ω, (target.omega_l next.code)⟩
  have theory := next.rank_theory_l hZF target.member (target.rank_l (ZF.modelsKP hZF) next.transitive next.code) (target.limit_l (ZF.modelsKP hZF) next.transitive next.code) model
  obtain ⟨v', hv, project⟩ := td_project_source_exists_l ft.transitive hZF source.omega model theory
    (hp 4) (hp 1) (hp 7) (hp 0)
  have eqv := project.unique_l I hZF.1 drop.2
  have hv : M.mem v.val D := eqv ▸ hv
  let v₀ : (rt_model_l D nd).Domain := ⟨v.val, hv⟩
  refine ⟨hmω, low, nd, θ, fun _ => rfl, (Formula.satisfies_conj_iff ..).mpr ⟨lang, ?_⟩⟩
  simp only [tg_elastic_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff]
  refine ⟨v₀, ?_, ?_⟩
  · exact (td_dcp_source_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ft.transitive nd ft.pair
      (θ.push v₀) (.bound 5) (.bound 2) (.bound 8) (.bound 1) (.bound 0)).mpr drop
  · exact (ee_elastic_absolute_l ft.transitive nd (θ.push v₀)
      (.bound 9) (.bound 10) (.bound 11) (.bound 12) (.bound 0)).mpr elastic

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 共同秩段唯一确定回答语言的域

两层的相对 Vτ 都限制到同一共同秩段。随后用常量域的外延性和完整
查询域的唯一性识别原表项；不提升两层的无界满足关系。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_context_d.reply_domain_l {ω X R μ K η C Y S μ' K' η' D L W : M.Domain}
    (context : Tg_context_d I ω X R η C) (current : Tg_context_d I ω Y S η' D)
    (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K X R) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ' K' Y S)
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
  have full := (context.rank_l (ZF.modelsKP hZF) owner.transitive owner.code).of_rank_l owner.transitive context.member (ρ.bound 5).property vr
  have full' := (current.rank_l (ZF.modelsKP hZF) source.transitive source.code).of_rank_l source.transitive current.member (θ.bound 5).property vr'
  have hB := owner.transitive C context.member (ρ.bound 5).val (ρ.bound 5).property
  have hB' := source.transitive D current.member (θ.bound 5).val (θ.bound 5).property
  obtain ⟨hBW, vrW⟩ := rank.rank_l hZF owner.transitive hW limit hτ hB full
  obtain ⟨hBW', vrW'⟩ := rank'.rank_l hZF source.transitive hW' limit (ht.symm ▸ hτ) hB' full'
  have eqB := Vr_d.unique_l hZF (rank.transitive_l owner.transitive hW) hBW hBW' vrW (ht ▸ vrW')
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

/-! ## 原共同图唯一确定目标查询表中的完整域

两侧实际反射语言先在各自所属模型中读取。原 Vτ 的整个历史和常量域
沿共同图传输；完整有限池的有界原式沿同一完整代表池传输。
目标的实际秩与查询池唯一性随后识别原表项，不比较查询码的字面表示。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u

theorem tg_reply_domain_read_l {M : Structure.{u}} (hZF : M.Models ZF) {ω η C : M.Domain}
    (rank : V_d (kp_pair_l (ZF.modelsKP hZF)) η C) (fs : Fs_read_d ω C)
    (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 11)
    (hw : (ρ.bound 0).val = ω) (valid : Formula.satisfies ρ tg_reply_language0_m) :
    M.mem (ρ.bound 3).val ω ∧ M.IsLimitOrdinal (ρ.bound 4).val ∧
    V_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 4).val (ρ.bound 5).val ∧
    (∀ x, M.mem x (ρ.bound 6).val ↔ M.mem x (ρ.bound 5).val ∨ x = (ρ.bound 4).val) ∧
    Tt_pool_d (kp_pair_l (ZF.modelsKP hZF)) ω (ρ.bound 3).val (ρ.bound 6).val (ρ.bound 7).val := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  simp only [tg_reply_language0_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at valid
  obtain ⟨hn, _, _, limit, base, constants, pool, _⟩ := valid
  have limit := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) (ρ.bound 4)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp limit)
  obtain ⟨B, rB⟩ := ZF.v_exists_l I hZF limit.1
  have hB := ZF.v_mem_l I hZF rB rank (ZF.v_ordinal_height_l hZF rank limit.1 (ρ.bound 4).property)
  have relative := (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc ρ (.bound 4) (.bound 5)).mp base
  have eq := vr_agree_l hZF fs.transitive (ρ.bound 5).property rB (fs.transitive B hB) relative
  have constants := (tt_constants0_sat_l hZF.1 ..).mp
    ((rt_model_delta_l fs.transitive nc (tt_constants0_delta_l (.bound 4) (.bound 5) (.bound 6)) ρ).mp constants)
  obtain ⟨A,E,_,_,names,seq,product⟩ :=
    (fs.pool_sat_l (ZF.modelsKP hZF) nc ρ (.bound 0) (.bound 3) (.bound 6) (.bound 7) hw).mp pool
  exact ⟨hw ▸ hn, limit, eq.symm ▸ rB, constants, A,E,names,seq,product⟩

/-- 完整池图搬运有界有限池原式；两侧实际秩闭包恢复全部内部有限函数。 -/
theorem tg_pool_raw_image_l {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)
    {N R P S Γ t : M.Domain} (nx : ∃ x, M.mem x N) (ny : ∃ y, M.mem y P)
    (hx : (smdl_structure_l I (R := R) nx).Models ZF)
    (hy : (smdl_structure_l I (R := S) ny).Models ZF)
    (B : (smdl_structure_l I (R := R) nx).Domain)
    (trans : (smdl_structure_l I (R := R) nx).TransitiveSet B)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ M.PairMember I x B.val R)
    (ft : M.IsSetInjectionFromTo I t Γ P)
    (pred : ∀ x E, M.PairMember I x E t → ∀ y,
      M.PairMember I y E S ↔ ∃ a, M.PairMember I a x R ∧ M.PairMember I a y t)
    (ρ : Env (smdl_structure_l I (R := R) nx) 5) (σ : Env (smdl_structure_l I (R := S) ny) 5)
    (L : (smdl_structure_l I (R := R) nx).Domain) (l : (smdl_structure_l I (R := S) ny).Domain)
    (rank : V_d (kp_pair_l (ZF.modelsKP hx)) L (ρ.bound 1))
    (rank' : V_d (kp_pair_l (ZF.modelsKP hy)) l (σ.bound 1))
    (limit : (smdl_structure_l I (R := R) nx).IsLimitOrdinal L)
    (limit' : (smdl_structure_l I (R := S) ny).IsLimitOrdinal l)
    (hw : (smdl_structure_l I (R := R) nx).IsOmega (ρ.bound 0))
    (hw' : (smdl_structure_l I (R := S) ny).IsOmega (σ.bound 0))
    (hwV : (smdl_structure_l I (R := R) nx).mem (ρ.bound 0) (ρ.bound 1))
    (hn : (smdl_structure_l I (R := R) nx).mem (ρ.bound 2) (ρ.bound 0))
    (hU : (smdl_structure_l I (R := R) nx).mem (ρ.bound 3) (ρ.bound 1))
    (points : ∀ i, M.PairMember I (ρ.bound i).val (σ.bound i).val t)
    (pool : Tt_pool_d (kp_pair_l (ZF.modelsKP hx)) (ρ.bound 0) (ρ.bound 2) (ρ.bound 3) (ρ.bound 4)) :
    Tt_pool_d (kp_pair_l (ZF.modelsKP hy)) (σ.bound 0) (σ.bound 2) (σ.bound 3) (σ.bound 4) := by
  let X := smdl_structure_l I (R := R) nx
  let Y := smdl_structure_l I (R := S) ny
  have members i : X.mem (ρ.bound i) B := ((carrier _).mp (ft.1.input_mem_of_pairMember (points i))).2
  let nb : Nonempty {x : X.Domain // X.mem x B} := ⟨⟨ρ.bound 0,members 0⟩⟩
  let ε : Env (rt_model_l B nb) 5 := ⟨fun i => ⟨ρ.bound i,members i⟩, fun _ => ⟨ρ.bound 0,members 0⟩⟩
  let ε₀ : Env X 5 := image_env_l Subtype.val ε
  have mem (i j : Fin 5) (h : X.mem (ρ.bound i) (ρ.bound j)) : Y.mem (σ.bound i) (σ.bound j) :=
    (pred _ _ (points j) _).mpr ⟨_,h,points i⟩
  have source := (tt_pool0_rank_l hx ε₀ (.bound 0) (.bound 1)
    (.bound 2) (.bound 3) (.bound 4) hw rank limit hwV hn hU).mpr pool
  have moved := (rr_native_delta_l I nx ny B trans nb carrier ft pred
    (tt_pool0_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4))
    (by simp -implicitDefEqProofs) (tt_pool0_delta_l ..) ε σ points).mp source
  exact (tt_pool0_rank_l hy σ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)
    hw' rank' limit' (mem 0 1 hwV) (mem 2 0 hn) (mem 3 1 hU)).mp moved

section Domain
variable {M : Structure.{u}} (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP
variable {N R P S L l U V Γ k B₀ t : M.Domain}
  (nx : ∃ x, M.mem x N) (ny : ∃ y, M.mem y P)
local notation "X" => smdl_structure_l I (R := R) nx
local notation "Y" => smdl_structure_l I (R := S) ny

/-- 同一完整池中的两份实际回答语言具有同一个查询域。 -/
theorem tg_reply_domain_raw_l (hx : (X).Models ZF) (hy : (Y).Models ZF)
    (common : Ic_common_d I N R P S L l U V Γ k)
    (B : (X).Domain) (trans : (X).TransitiveSet B)
    (carrier : ∀ x, M.mem x B₀ ↔ M.mem x N ∧ Rd_entry_d x B.val R)
    (ft : M.IsSetInjectionFromTo I t B₀ P)
    (pred : ∀ x E, Rd_entry_d x E t → ∀ y, Rd_entry_d y E S ↔ ∃ a, Rd_entry_d a x R ∧ Rd_entry_d a y t)
    (restrict : M.IsRestrictionOf I k t Γ) (iL : Rd_entry_d L l t) (iV : Rd_entry_d U V t)
    (ω n τ A C D : (X).Domain) (ω' n' τ' D' A' C' Q' : (Y).Domain)
    (hw : (X).IsOmega ω) (hw' : (Y).IsOmega ω') (hn : (X).mem n ω)
    (hwU : Rd_entry_d ω.val U R) (hτL : Rd_entry_d τ.val L R)
    (rank : V_d (kp_pair_l (ZF.modelsKP hx)) τ A)
    (constants : ∀ x, (X).mem x C ↔ (X).mem x A ∨ x = τ)
    (pool : Tt_pool_d (kp_pair_l (ZF.modelsKP hx)) ω n C D)
    (rank' : V_d (kp_pair_l (ZF.modelsKP hy)) τ' A')
    (constants' : ∀ x, (Y).mem x C' ↔ (Y).mem x A' ∨ x = τ')
    (pool' : Tt_pool_d (kp_pair_l (ZF.modelsKP hy)) ω' n' C' Q')
    (iω : Rd_entry_d ω.val ω'.val t) (in₀ : Rd_entry_d n.val n'.val t)
    (iτ : Rd_entry_d τ.val τ'.val t) (iD : Rd_entry_d D.val D'.val t) : D' = Q' := by
  let J := kp_pair_l (ZF.modelsKP hx)
  let K := kp_pair_l (ZF.modelsKP hy)
  let a : (X).Domain := ⟨L,common.left_rank.1⟩
  let u : (X).Domain := ⟨U,common.left_rank.2.1⟩
  let b : (Y).Domain := ⟨l,common.right_rank.1⟩
  let v : (Y).Domain := ⟨V,common.right_rank.2.1⟩
  have ru := (rr_rank_native_l I nx (ZF.modelsKP hx) a u).mp common.left_rank
  have rv := (rr_rank_native_l I ny (ZF.modelsKP hy) b v).mp common.right_rank
  have ha : (X).IsLimitOrdinal a := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I nx (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => a)).mp common.limit)
  have haB : (X).mem a B := ((carrier L).mp (ft.1.input_mem_of_pairMember iL)).2
  let nb : Nonempty {x : (X).Domain // (X).mem x B} := ⟨⟨a,haB⟩⟩
  let α : Env (rt_model_l B nb) 1 := ⟨fun _ => ⟨a,haB⟩,fun _ => ⟨a,haB⟩⟩
  let β : Env Y 1 := ⟨fun _ => b,fun _ => b⟩
  have hb : (Y).IsLimitOrdinal b := (KP.limit0_sat_l (ZF.modelsKP hy) β .newest).mp
    ((rr_native_delta_l I nx ny B trans nb carrier ft pred (KP.limit0_m .newest)
      (by simp -implicitDefEqProofs) (KP.limit0_delta_l _) α β (fun _ => iL)).mp
        ((KP.limit0_sat_l (ZF.modelsKP hx) _ .newest).mpr ha))
  have ut := v_transitive_l J ru
  have hτu : (X).mem τ u := KP.v_ordinal_subset_l (ZF.modelsKP hx) ru τ hτL
  have hAu : (X).mem A u := ZF.v_mem_l J hx rank ru hτL
  have hCu : (X).mem C u := tt_constants_rank_l hx ru ha hτL rank constants
  have cut (x : (X).Domain) (y : (Y).Domain) (h : (X).mem x u) (xy : Rd_entry_d x.val y.val t) :
      Rd_entry_d x.val y.val k := (restrict.2 _ _).mpr ⟨(common.carrier _).mpr ⟨x.property,h⟩,xy⟩
  have ττ := cut τ τ' hτu iτ
  obtain ⟨A₁,hA₁,aA⟩ := common.injection.1.2.2 A.val ((common.carrier A.val).mpr ⟨A.property,hAu⟩)
  obtain ⟨C₁,hC₁,cC⟩ := common.injection.1.2.2 C.val ((common.carrier C.val).mpr ⟨C.property,hCu⟩)
  let A₁n : (Y).Domain := ⟨A₁,hA₁⟩
  let C₁n : (Y).Domain := ⟨C₁,hC₁⟩
  let nu : Nonempty {x : (X).Domain // (X).mem x u} := ⟨⟨τ,hτu⟩⟩
  obtain ⟨F,hF,history⟩ := KP.v_history_inside_l (ZF.modelsKP hx) ru ha hτu hAu rank
  have relative : Vr_d u τ A := ⟨A,F,hAu,hF,fun x _ => history x⟩
  have movedRank := rr_native_rank_value_l I nx ny hy.1 u τ A ut common.carrier common.injection
    common.image common.pred common.right_closed hτu hAu ττ aA
    ((vr_sat_l (ZF.modelsKP hx) ut nu _ (.bound 1) .newest).mpr relative)
  have fullRank := (rr_rank_native_l I ny (ZF.modelsKP hy) τ' A₁n).mp movedRank
  have eqA := ZF.v_unique_l K hy fullRank rank'
  let ε : Env (rt_model_l u nu) 3 := ⟨fun i => [⟨τ,hτu⟩,⟨A,hAu⟩,⟨C,hCu⟩].get i,fun _ => ⟨τ,hτu⟩⟩
  let ε₀ : Env X 3 := image_env_l Subtype.val ε
  let ζ : Env Y 3 := ⟨fun i => [τ',A₁n,C₁n].get i,fun _ => τ'⟩
  have points : ∀ i, Rd_entry_d (ε.bound i).val.val (ζ.bound i).val k :=
    Fin.cases ττ (Fin.cases aA (Fin.cases cC (fun i => Fin.elim0 i)))
  have moved := (rr_native_delta_l I nx ny u ut nu common.carrier common.injection common.pred
    (tt_constants0_m (.bound 0) (.bound 1) (.bound 2)) (by simp -implicitDefEqProofs)
    (tt_constants0_delta_l ..) ε ζ points).mp
      ((tt_constants0_sat_l hx.1 ε₀ (.bound 0) (.bound 1) (.bound 2)).mpr constants)
  have cons := (tt_constants0_sat_l hy.1 ζ (.bound 0) (.bound 1) (.bound 2)).mp moved
  have eqC : C₁n = C' := hy.1.eq_of_same_members _ _ (fun x => (cons x).trans
    ((or_congr (Iff.of_eq (congrArg ((Y).mem x) eqA)) Iff.rfl).trans (constants' x).symm))
  let ρ : Env X 5 := ⟨fun i => [ω,u,n,C,D].get i,fun _ => ω⟩
  let σ : Env Y 5 := ⟨fun i => [ω',v,n',C₁n,D'].get i,fun _ => ω'⟩
  have values : ∀ i, Rd_entry_d (ρ.bound i).val (σ.bound i).val t :=
    Fin.cases iω (Fin.cases iV (Fin.cases in₀ (Fin.cases ((restrict.2 _ _).mp cC).2
      (Fin.cases iD (fun i => Fin.elim0 i)))))
  have actual := tg_pool_raw_image_l I nx ny hx hy B trans carrier ft pred ρ σ a b
    ru rv ha hb hw hw' hwU hn hCu values pool
  exact actual.unique_l hy.1 K
    (Eq.mp (congrArg (fun C => Tt_pool_d K ω' n' C Q') eqC.symm) pool')
end Domain

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际像上的原子类型证书返回反射层

名字域在目标内构造。查询对回收原程序码与列图，列图回收七个原槽位；
只需列长度是自然数，不额外假定其余见证在目标内。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_subtype0_m : Formula 1 17 := ts_subtype_m
  (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9)
  (Fin.cases (.bound 10) (Fin.cases (.bound 11) (Fin.cases (.bound 12) (Fin.cases (.bound 13)
    (Fin.cases (.bound 14) (Fin.cases (.bound 15) (fun _ => .bound 16)))))))

theorem tg_subtype0_closed_l : tg_subtype0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_subtype0_m, Fin.forall_fin_succ]

def Tg_subtype_in_d (ω n κ τ m U w b z u : M.Domain) (σ : Fin 7 → M.Domain) (C : M.Domain) : Prop :=
  let p : Fin 17 → M.Domain := fun i => [ω, n, κ, τ, m, U, w, b, z, u, σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6].get i
  (∀ i, M.mem (p i) C) ∧ Formula.satisfies ((⟨p, fun _ => ω⟩ : Env M 17).push C)
    (lr_rel_m tg_subtype0_m .newest (fun i => .bound i.succ))

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_context_d.subtype_l {ω μ K X R η C n κ τ m U w b z u : M.Domain} {σ : Fin 7 → M.Domain}
    (context : Tg_context_d I ω X R η C) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K X R)
    (hU : M.mem U C) (hu : M.mem u C) (hb : M.mem b ω)
    (subtype : Ts_subtype_d ω n κ τ m U w b σ z u) : Tg_subtype_in_d ω n κ τ m U w b z u σ C := by
  have fs := (context.read_l hZF source).1
  obtain ⟨c, T, model⟩ := smdl_membership_l I hZF ⟨ω, (context.omega_l source.code)⟩
  have theory := source.rank_theory_l hZF context.member (context.rank_l (ZF.modelsKP hZF) source.transitive source.code) (context.limit_l (ZF.modelsKP hZF) source.transitive source.code) model
  have data := subtype
  obtain ⟨_, _, q, query, hq⟩ := data
  obtain ⟨hw, hm, hn, hτ, hκ, _⟩ := query.1
  have member x (hx : M.mem x U) := fs.transitive U hU x hx
  obtain ⟨A, hA, names⟩ := tn_names_source_l hZF source.omega fs.transitive model theory (member n hn) hU
  obtain ⟨F, ⟨_, _, v, _, slots, _⟩, code⟩ := query.column_l hZF.1 names
  have zF := code.mem_l M fs.transitive (fs.transitive u hu q hq)
  have hs i := (rd_entry_transitive_l fs.transitive zF.2 (slots i)).1
  let p : Fin 17 → M.Domain := fun i => [ω, n, κ, τ, m, U, w, b, z, u, σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6].get i
  have hp : ∀ i, M.mem (p i) C := by
    simp only [Fin.forall_fin_succ]
    exact ⟨(context.omega_l source.code), member n hn, member κ hκ, member τ hτ, member m hm, hU, member w hw,
      fs.transitive ω (context.omega_l source.code) b hb, zF.1, hu, hs 0, hs 1, hs 2, hs 3, hs 4, hs 5, hs 6, fun i => Fin.elim0 i⟩
  let nc : Nonempty {a // M.mem a C} := ⟨⟨ω, (context.omega_l source.code)⟩⟩
  let ρ : Env (rt_model_l C nc) 17 := ⟨fun i => ⟨p i, hp i⟩, fun _ => ⟨ω, (context.omega_l source.code)⟩⟩
  let f : Fin 7 → Term 17 := fun i =>
    [.bound 10, .bound 11, .bound 12, .bound 13, .bound 14, .bound 15, .bound 16].get i
  have eq : (fun i => ((f i).eval ρ).val) = σ := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  have valid : Formula.satisfies ρ tg_subtype0_m := ts_subtype_reflect_l (ZF.modelsKP hZF) fs.transitive nc
    ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9)
    f hA names (eq.symm ▸ subtype)
  exact ⟨hp, (sc_relative_sat_l fs.transitive nc tg_subtype0_m tg_subtype0_closed_l ρ
    ((⟨p, fun _ => ω⟩ : Env M 17).push C) .newest (fun i => .bound i.succ) rfl (fun _ => rfl)).mpr valid⟩

end YesMetaZFC.SetTheory.LargeCardinal
