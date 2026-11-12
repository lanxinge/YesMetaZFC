import YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype
import YesMetaZFC.Model.SetTheory.Types.SubtypeUp
import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding

/-! # 同一反射结构中的实际实现核调用

完整旧轮、候选、subtype 和数值程序使用同一批参数。查询池由调用方的实际
有限闭包提供；装配和实现只使用原更新核，不要求反射结构自身满足 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem tg_realize_assemble_l (kernel : Tg_kernel_d M)
    (ρ : Env M 54) (χ : Env M 12) (θ : Env M 17) (W : M.Domain)
    (old : Formula.satisfies ρ tg_round0_m) (candidate : Formula.satisfies χ tg_candidate0_m)
    (subtype : Formula.satisfies θ tg_subtype0_m)
    (program : Formula.satisfies (θ.reindex (fun i : Fin 11 => [0,1,7,8,10,11,12,13,14,15,16].get i)) ts_numeric0_m)
    (prior : ∀ i : Fin 5, θ.bound ([0,1,2,5,9].get i) = ρ.bound ([16,24,15,13,11].get i))
    (current : ∀ i : Fin 3, θ.bound ([3,4,6].get i) = χ.bound ([3,1,0].get i))
    (finite : M.mem (χ.bound 1) (θ.bound 0))
    (pool : Formula.satisfies
      (⟨fun i => [θ.bound 0,χ.bound 1,χ.bound 6,W].get i, χ.free⟩ : Env M 4)
      (tt_pool_m (.bound 0) (.bound 1) (.bound 2) (.bound 3))) :
    ∃ ν, M.mem ν (ρ.bound 10) ∧ Formula.satisfies
      (⟨fun i => [ρ.bound 16,ρ.bound 18,ρ.bound 24,ρ.bound 29,χ.bound 1,χ.bound 6,W,χ.bound 0,ν].get i,
        ρ.free⟩ : Env M 9) ts_at0_m := by
  obtain ⟨seed, round⟩ := (Formula.satisfies_conj_iff ..).mp old
  simp only [tg_seed0_m, Formula.satisfies_rename, tg_seed_m, Formula.satisfies_conj_iff] at seed
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff] at round
  obtain ⟨_, _, _, _, rank, code, language, type, _⟩ := round
  simp only [ee_language_m, Formula.satisfies_bind, ee_language0_m, Formula.satisfies_conj_iff] at language
  have newLanguage := ((Formula.satisfies_conj_iff ..).mp candidate).1
  simp only [Formula.satisfies_rename, ee_language0_m, Formula.satisfies_conj_iff] at newLanguage
  obtain ⟨_, limit, base, constants, _⟩ := newLanguage
  let ψ : Env M 27 := ⟨fun i => [ρ.bound 16,ρ.bound 24,θ.bound 7,θ.bound 8,ρ.bound 10,ρ.bound 9,ρ.bound 8,
    ρ.bound 7,ρ.bound 29,ρ.bound 18,ρ.bound 13,ρ.bound 12,ρ.bound 11,ρ.bound 15,
    χ.bound 3,χ.bound 1,χ.bound 5,χ.bound 6,W,χ.bound 0,
    θ.bound 10,θ.bound 11,θ.bound 12,θ.bound 13,θ.bound 14,θ.bound 15,θ.bound 16].get i, ρ.free⟩
  let fo : Fin 10 → Term 54 := fun i => [.bound 16,.bound 8,.bound 9,.bound 7,.bound 24,
    .bound 29,.bound 18,.bound 13,.bound 12,.bound 11].get i
  let ft : Fin 10 → Term 27 := fun i => [.bound 0,.bound 6,.bound 5,.bound 7,.bound 1,
    .bound 8,.bound 9,.bound 10,.bound 11,.bound 12].get i
  have type' : Formula.satisfies ψ (tt_realized_m (.bound 0) (.bound 6) (.bound 5) (.bound 7) (.bound 1)
      (.bound 8) (.bound 9) (.bound 10) (.bound 11) (.bound 12)) := by
    apply (Formula.satisfies_bind ψ ft tt_realized0_m).mpr
    apply (Formula.closed_env_l tt_realized0_m tt_realized0_closed_l ?_).mp
      ((Formula.satisfies_bind ρ fo tt_realized0_m).mp type)
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))) i
  let fp : Fin 11 → Term 27 := fun i => [.bound 0,.bound 1,.bound 2,.bound 3,
    .bound 20,.bound 21,.bound 22,.bound 23,.bound 24,.bound 25,.bound 26].get i
  have prog : Formula.satisfies (Definitional.Env.substitute ψ fp) ts_numeric0_m := by
    apply (Formula.closed_env_l ts_numeric0_m ts_numeric0_closed_l ?_).mp program
    funext i
    exact Fin.cases (prior 0) (Fin.cases (prior 1) (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (fun j => Fin.elim0 j))))))))))) i
  let fq : Fin 17 → Term 27 := fun i => [.bound 0,.bound 1,.bound 13,.bound 14,.bound 15,.bound 10,
    .bound 19,.bound 2,.bound 3,.bound 12,.bound 20,.bound 21,.bound 22,.bound 23,.bound 24,.bound 25,.bound 26].get i
  have sub : Formula.satisfies (Definitional.Env.substitute ψ fq) tg_subtype0_m := by
    apply (Formula.closed_env_l tg_subtype0_m tg_subtype0_closed_l ?_).mp subtype
    funext i
    exact Fin.cases (prior 0) (Fin.cases (prior 1) (Fin.cases (prior 2) (Fin.cases (current 0)
      (Fin.cases (current 1) (Fin.cases (prior 3) (Fin.cases (current 2) (Fin.cases rfl (Fin.cases rfl
        (Fin.cases (prior 4) (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
          (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))))))))))))) i
  have finite' : M.mem (χ.bound 1) (ρ.bound 16) := prior 0 ▸ finite
  have pool' : Formula.satisfies ψ (tt_pool_m (.bound 0) (.bound 15) (.bound 17) (.bound 18)) := by
    let φ : Formula 1 4 := tt_pool_m (.bound 0) (.bound 1) (.bound 2) (.bound 3)
    let g : Fin 4 → Term 27 := fun i => [.bound 0,.bound 15,.bound 17,.bound 18].get i
    change Formula.satisfies ψ (φ.bind g)
    apply (Formula.satisfies_bind ψ g φ).mpr
    apply (Formula.closed_env_l φ (by simp -implicitDefEqProofs [φ]) ?_).mp pool
    funext i
    exact Fin.cases (prior 0) (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))) i
  have raw : Formula.satisfies ψ tc_realize_seed0_m := by
    simp only [tc_realize_seed0_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff]
    exact ⟨seed.1, (Formula.satisfies_bind ψ fp ts_numeric0_m).mpr prog, rank, code, type',
      language.2.1, limit, finite', base, constants, pool',
      (Formula.satisfies_bind ψ fq tg_subtype0_m).mpr sub⟩
  have realized := kernel.realize_seed_l ψ raw
  simp only [tc_realize_result0_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff] at realized
  obtain ⟨ν, bound, realized⟩ := realized
  refine ⟨ν, bound, ?_⟩
  let f : Fin 9 → Term 28 := fun i => [.bound 1,.bound 10,.bound 2,.bound 9,.bound 16,
    .bound 18,.bound 19,.bound 20,.bound 0].get i
  apply (Formula.closed_env_l ts_at0_m ts_at0_closed_l ?_).mp
    ((Formula.satisfies_bind (ψ.push ν) f ts_at0_m).mp realized)
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))))) i

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 继续树边目标中的真实低层实现

从已经搬运的完整旧轮记录读取实现，使用同一子类型程序及同一候选。
候选查询域在目标层实际构造，再调用目标内的已证读取句子；排列由原见证保留。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_realized_in_d (ω δ n r m V W u ν C : M.Domain) : Prop :=
  let p : Fin 9 → M.Domain := fun i => [ω, δ, n, r, m, V, W, u, ν].get i
  (∀ i, M.mem (p i) C) ∧ Formula.satisfies ((⟨p, fun _ => ω⟩ : Env M 9).push C)
    (lr_rel_m ts_at0_m .newest (fun i => .bound i.succ))

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω X η C : M.Domain} (nc : Nonempty {a // M.mem a C})
  (ρ : Env (rt_model_l C nc) 54) (χ : Env (rt_model_l C nc) 12)
local notation "N" => rt_model_l C nc
local notation "p" => (fun i => Subtype.val (Env.bound ρ i))

theorem Tg_context_d.realize_l {μ K R n κ τ m U t u b z : M.Domain} {σ : Fin 7 → M.Domain}
    (context : Tg_context_d I ω X R η C) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K X R)
    (old : Formula.satisfies ρ tg_round0_m) (candidate : Formula.satisfies χ tg_candidate0_m)
    (hn : p 24 = n) (hκ : p 15 = κ) (hU : p 13 = U) (ht : p 11 = t)
    (hτ : (χ.bound 3).val = τ) (hm : (χ.bound 1).val = m) (hu : (χ.bound 0).val = u)
    (finite : M.mem m ω) (program : Ts_program_in_d ω n b z σ C)
    (subtype : Tg_subtype_in_d ω n κ τ m U u b z t σ C) :
    ∃ W ν, Tt_pool_d I ω m (χ.bound 6).val W ∧ M.mem ν (p 10) ∧
      Tg_realized_in_d ω (p 18) n (p 29) m (χ.bound 6).val W u ν C := by
  have fs := (context.read_l hZF source).1
  have seed := ((Formula.satisfies_conj_iff ..).mp old).1
  simp only [tg_seed0_m, Formula.satisfies_rename, tg_seed_m, Formula.satisfies_conj_iff] at seed
  have omega : (N).IsOmega (ρ.bound 16) := (Formula.satisfies_isOmega_iff ..).mp seed.1
  let w₀ : (N).Domain := ⟨ω, fs.omega_mem⟩
  have actual := rt_omega_l fs.transitive nc hZF.1 w₀ source.omega
  have hw : p 16 = ω := congrArg Subtype.val ((rt_model_ext_l hZF.1 fs.transitive nc).eq_of_same_members
    (ρ.bound 16) w₀ (fun x => ⟨omega.2 w₀ actual.1 x, actual.2 (ρ.bound 16) omega.1 x⟩))
  obtain ⟨W, pool⟩ := tt_pool_exists_l I hZF source.omega m (χ.bound 6).val
  obtain ⟨hW, A, E, hA, hE, names, seq, product⟩ := source.pool_rank_l hZF context.member
    (context.rank_l (ZF.modelsKP hZF) source.transitive source.code)
    (context.limit_l (ZF.modelsKP hZF) source.transitive source.code) fs.omega_mem
    (hm ▸ (χ.bound 1).property) (χ.bound 6).property pool
  let W₀ : (N).Domain := ⟨W, hW⟩
  let q : Fin 17 → M.Domain := fun i => [ω,n,κ,τ,m,U,u,b,z,t,σ 0,σ 1,σ 2,σ 3,σ 4,σ 5,σ 6].get i
  let θ : Env N 17 := ⟨fun i => ⟨q i, subtype.1 i⟩, fun _ => w₀⟩
  have sub : Formula.satisfies θ tg_subtype0_m :=
    (sc_relative_sat_l fs.transitive nc tg_subtype0_m tg_subtype0_closed_l θ
      ((⟨q, fun _ => ω⟩ : Env M 17).push C) .newest (fun i => .bound i.succ) rfl (fun _ => rfl)).mp subtype.2
  let pn : Fin 11 → M.Domain := fun i => [ω,n,b,z,σ 0,σ 1,σ 2,σ 3,σ 4,σ 5,σ 6].get i
  have prog : Formula.satisfies (θ.reindex (fun i : Fin 11 => [0,1,7,8,10,11,12,13,14,15,16].get i)) ts_numeric0_m := by
    apply (sc_relative_sat_l fs.transitive nc ts_numeric0_m ts_numeric0_closed_l _
      ((⟨pn, fun _ => ω⟩ : Env M 11).push C) .newest (fun i => .bound i.succ) rfl ?_).mp program.2
    intro i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (fun j => Fin.elim0 j))))))))))) i
  have prior : ∀ i : Fin 5, θ.bound ([0,1,2,5,9].get i) = ρ.bound ([16,24,15,13,11].get i) :=
    Fin.cases (Subtype.ext hw.symm) (Fin.cases (Subtype.ext hn.symm) (Fin.cases (Subtype.ext hκ.symm)
      (Fin.cases (Subtype.ext hU.symm) (Fin.cases (Subtype.ext ht.symm) (fun i => Fin.elim0 i)))))
  have current : ∀ i : Fin 3, θ.bound ([3,4,6].get i) = χ.bound ([3,1,0].get i) :=
    Fin.cases (Subtype.ext hτ.symm) (Fin.cases (Subtype.ext hm.symm)
      (Fin.cases (Subtype.ext hu.symm) (fun i => Fin.elim0 i)))
  let σp : Env N 4 := ⟨fun i => [θ.bound 0,χ.bound 1,χ.bound 6,W₀].get i, χ.free⟩
  have pool' : Formula.satisfies σp (tt_pool_m (.bound 0) (.bound 1) (.bound 2) (.bound 3)) :=
    (fs.pool_sat_l (ZF.modelsKP hZF) nc σp (.bound 0) (.bound 1) (.bound 2) (.bound 3) rfl).mpr
      ⟨A, E, hA, hE, hm.symm ▸ names, seq, product⟩
  have finite' : M.mem (χ.bound 1).val ω := hm.symm ▸ finite
  obtain ⟨ν, bound, proof⟩ := tg_realize_assemble_l
    (context.kernel_mem_l source.transitive source.code fs.transitive nc) ρ χ θ W₀ old candidate sub prog prior current
    finite' pool'
  let ξ : Env N 9 := ⟨fun i => [ρ.bound 16,ρ.bound 18,ρ.bound 24,ρ.bound 29,χ.bound 1,χ.bound 6,W₀,χ.bound 0,ν].get i, ρ.free⟩
  let pr : Fin 9 → M.Domain := fun i => [ω,p 18,n,p 29,m,(χ.bound 6).val,W,u,ν.val].get i
  have same : ∀ i, pr i = (ξ.bound i).val := Fin.cases hw.symm (Fin.cases rfl (Fin.cases hn.symm
    (Fin.cases rfl (Fin.cases hm.symm (Fin.cases rfl (Fin.cases rfl (Fin.cases hu.symm
      (Fin.cases rfl (fun j => Fin.elim0 j)))))))))
  have members i : M.mem (pr i) C := Eq.mpr (congrArg (fun a => M.mem a C) (same i)) (ξ.bound i).property
  exact ⟨W, ν.val, pool, bound, members,
    (sc_relative_sat_l fs.transitive nc ts_at0_m ts_at0_closed_l ξ
      ((⟨pr, fun _ => ω⟩ : Env M 9).push C) .newest (fun i => .bound i.succ) rfl same).mpr proof⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 在实际目标反射层内恢复一张图

旧轮记录提供旧根、标签图和严格秩界；新查询行提供原节点规则。
低层实现保持任意排列，恢复的全部见证仍属于同一个目标反射层。
读取只要求所在原模型的 KP、实际有限反射闭包与已经实现的恢复核。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hK : M.Models KP)
variable {ω C : M.Domain} (nc : Nonempty {x // M.mem x C})
  (ρ : Env (rt_model_l C nc) 54) (ψ : Env (rt_model_l C nc) 12)
local notation "N" => rt_model_l C nc
local notation "p" => (fun i => Subtype.val (Env.bound ρ i))

include hK in
theorem tg_recover_read_l {U W u ν : M.Domain}
    (hω : M.IsOmega ω) (fs : Fs_read_d ω C) (kernel : Tg_kernel_d N)
    (old : Formula.satisfies ρ tg_round0_m) (queries : Formula.satisfies ψ tg_query_row0_m)
    (ωψ : (ψ.bound 0).val = ω) (eψ : (ψ.bound 1).val = p 17) (lψ : (ψ.bound 2).val = p 24)
    (hwU : M.mem ω U) (scope : M.mem (ψ.bound 4).val U ∧ M.mem (ψ.bound 5).val U ∧ M.mem (ψ.bound 6).val U)
    (qn : M.mem (ψ.bound 11).val u) (qm : M.mem (ψ.bound 8).val u)
    (realized : Tg_realized_in_d ω (p 18) (p 24) (p 29) (ψ.bound 3).val U W u ν C) :
    ∃ θ : Env N 29,
      (∀ i : Fin 22, (θ.bound i.succ.succ.succ.succ.succ.succ.succ).val =
        [ω, p 17, p 22, p 23, p 24, (ψ.bound 3).val, U, W, (ψ.bound 5).val, (ψ.bound 6).val,
          (ψ.bound 7).val, (ψ.bound 8).val, (ψ.bound 9).val, (ψ.bound 10).val, (ψ.bound 11).val,
          p 29, p 18, p 19, p 20, p 42, ν, u].get i) ∧ Formula.satisfies θ tc_recovered0_m := by
  let ρs := ρ.reindex (fun i : Fin 38 => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
  obtain ⟨seed, _⟩ := (Formula.satisfies_conj_iff ..).mp old
  simp only [tg_seed0_m, Formula.satisfies_rename, tg_seed_m, Formula.satisfies_conj_iff] at seed
  obtain ⟨omega, empty, heω, _, _, root, _, hk, hl, _, _, _, oldType, _, _, _, first, last, set, node, _, _, bound, _⟩ := seed
  have omega := (Formula.satisfies_isOmega_iff ..).mp omega
  let w₀ : (N).Domain := ⟨ω, fs.omega_mem⟩
  have actual := rt_omega_l fs.transitive nc hK.1 w₀ hω
  have eqω := (rt_model_ext_l hK.1 fs.transitive nc).eq_of_same_members (ρ.bound 16) w₀
    (fun x => ⟨omega.2 w₀ actual.1 x, actual.2 (ρ.bound 16) omega.1 x⟩)
  have hw : p 16 = ω := congrArg Subtype.val eqω
  have finite₀ := oldType
  simp only [tt_realized_m, Formula.satisfies_bind, tt_realized0_m, Formula.satisfies_conj_iff] at finite₀
  have hnω : M.mem (p 24) ω := hw ▸ finite₀.2.1
  have hk₀ := (rt_successor_l fs.transitive nc hK.1 (ρ.bound 23) (ρ.bound 22)).mp
    ((Formula.satisfies_isSuccessor_iff ..).mp hk)
  have hl₀ := (rt_successor_l fs.transitive nc hK.1 (ρ.bound 24) (ρ.bound 23)).mp
    ((Formula.satisfies_isSuccessor_iff ..).mp hl)
  have ok := (hω.members_areOrdinals hK _ hnω).mem hl₀.predecessor_mem
  have he : ∀ a, ¬ M.mem a (p 17) := by
    intro a ha
    exact (Formula.satisfies_isEmpty_iff ..).mp empty ⟨a, fs.transitive _ (ρ.bound 17).property a ha⟩ ha
  have hek : M.mem (p 17) (p 23) := by
    have heω : M.mem (p 17) (p 16) := heω
    have oe := hω.members_areOrdinals hK _ (hw ▸ heω)
    rcases oe.trichotomy hK.1 (ok.mem hk₀.predecessor_mem) (KP.difference_exists_d hK)
      (KP.intersection_exists_d hK (p 17) (p 22)) with eq | lt | gt
    · exact (hk₀ _).mpr (Or.inr eq)
    · exact (hk₀ _).mpr (Or.inl lt)
    · exact (he _ gt).elim
  have row := (Formula.satisfies_conj_iff ..).mp queries
  have sk := (rt_successor_l fs.transitive nc hK.1 (ψ.bound 2) (ψ.bound 4)).mp
    ((Formula.satisfies_isSuccessor_iff ..).mp row.2.1)
  have eqk : (ψ.bound 4).val = p 23 :=
    (hl₀.predecessor_eq hK.1 ok (Eq.mp (congrArg (fun a => M.SuccessorOf a (ψ.bound 4).val) lψ) sk)).symm
  let U₀ : (N).Domain := ⟨U, realized.1 5⟩
  let W₀ : (N).Domain := ⟨W, realized.1 6⟩
  let u₀ : (N).Domain := ⟨u, realized.1 7⟩
  let ν₀ : (N).Domain := ⟨ν, realized.1 8⟩
  let ξ : Env N 22 := ⟨fun i => [w₀, ρ.bound 17, ρ.bound 22, ρ.bound 23, ρ.bound 24, ψ.bound 3,
    U₀, W₀, ψ.bound 5, ψ.bound 6, ψ.bound 7, ψ.bound 8, ψ.bound 9, ψ.bound 10, ψ.bound 11,
    ρ.bound 29, ρ.bound 18, ρ.bound 19, ρ.bound 20, ρ.bound 42, ν₀, u₀].get i, fun _ => w₀⟩
  let f : Fin 9 → Term 22 := fun i => [.bound 0, .bound 16, .bound 4, .bound 15, .bound 5,
    .bound 6, .bound 7, .bound 21, .bound 20].get i
  let r : Fin 9 → M.Domain := fun i => [ω, p 18, p 24, p 29, (ψ.bound 3).val, U, W, u, ν].get i
  have witness : Formula.satisfies (Definitional.Env.substitute ξ f) ts_at0_m :=
    (sc_relative_sat_l fs.transitive nc ts_at0_m ts_at0_closed_l (Definitional.Env.substitute ξ f)
      ((⟨r, fun _ => ω⟩ : Env M 9).push C) .newest (fun i => .bound i.succ) rfl (by
        intro i
        exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
          (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))))) i)).mp realized.2
  have finite := witness
  simp only [ts_at0_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff] at finite
  obtain ⟨_, _, _, _, _, _, _, _, _, type, _⟩ := finite
  simp only [tt_realized_m, Formula.satisfies_bind, tt_realized0_m, Formula.satisfies_conj_iff] at type
  have hn : M.mem (ψ.bound 3).val ω := type.2.1
  have base : Formula.satisfies ξ (tg_query_base_m (.bound 0) (.bound 1) (.bound 4) (.bound 5) (.bound 3)
      (.bound 8) (.bound 9) (.bound 10) (.bound 11) (.bound 12) (.bound 13) (.bound 14)) := by
    let g : Fin 12 → Term 22 := fun i => [.bound 0, .bound 1, .bound 4, .bound 5, .bound 3, .bound 8,
      .bound 9, .bound 10, .bound 11, .bound 12, .bound 13, .bound 14].get i
    apply (Formula.satisfies_bind ξ g tg_query_base0_m).mpr
    apply (Formula.closed_env_l tg_query_base0_m tg_query_base0_closed_l ?_).mp row.1
    funext i
    exact Fin.cases (Subtype.ext ωψ) (Fin.cases (Subtype.ext eψ) (Fin.cases (Subtype.ext lψ)
      (Fin.cases rfl (Fin.cases (Subtype.ext eqk) (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))))) i
  have raw : Formula.satisfies ξ tc_recover_seed0_m := by
    simp only [tc_recover_seed0_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff]
    refine ⟨(Formula.satisfies_isOmega_iff ..).mpr actual, ?_, hn, hek, ?_, ?_, ?_, base,
      hwU, Eq.mp (congrArg (fun a => M.mem a U) eqk) scope.1, scope.2.1, scope.2.2, ?_, ?_, ?_, ?_, ?_, root, qn, qm,
      (Formula.satisfies_bind ξ f ts_at0_m).mpr witness⟩
    · exact (Formula.satisfies_isEmpty_iff ..).mpr (fun a => he a.val)
    · exact (Formula.satisfies_isSuccessor_iff ..).mpr ((rt_successor_l fs.transitive nc hK.1 ..).mpr hk₀)
    · exact (Formula.satisfies_isSuccessor_iff ..).mpr ((rt_successor_l fs.transitive nc hK.1 ..).mpr hl₀)
    · have succ := (Formula.satisfies_isSuccessor_iff ..).mp row.2.2
      exact (Formula.satisfies_isSuccessor_iff ..).mpr
        (Eq.mp (congrArg (fun a => (N).SuccessorOf (ψ.bound 3) a) (Subtype.ext lψ)) succ)
    · change Formula.satisfies ξ ((tg_bound_raw_m (.bound 0) (.bound 1) (.bound 2) : Formula 1 3).bind
        (fun i => [.bound 16, .bound 17, .bound 18].get i))
      have same : (Definitional.Env.substitute ρs (fun i : Fin 3 => [Term.bound 2, Term.bound 3, Term.bound 4].get i)).bound =
          (Definitional.Env.substitute ξ (fun i : Fin 3 => [Term.bound 16, Term.bound 17, Term.bound 18].get i)).bound := by
        funext i
        exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))) i
      apply (Formula.satisfies_bind ..).mpr
      apply (Formula.closed_env_l (tg_bound_raw_m (.bound 0) (.bound 1) (.bound 2) : Formula 1 3)
        (by simp -implicitDefEqProofs [tg_bound_raw_m, Definitional.Formula.FreeClosed]) same).mp
      exact (Formula.satisfies_bind ρs (fun i : Fin 3 => [Term.bound 2, Term.bound 3, Term.bound 4].get i)
        (tg_bound_raw_m (.bound 0) (.bound 1) (.bound 2))).mp bound
    · have first := ((rt_model_delta_l fs.transitive nc (rd_entry0_delta_l (.bound 1) (.bound 3) (.bound 13)) ρs).trans
        (rd_entry0_sat_l hK.1 ..)).mp first
      exact ((rt_model_delta_l fs.transitive nc (rd_entry0_delta_l (.bound 1) (.bound 17) (.bound 15)) ξ).trans
        (rd_entry0_sat_l hK.1 ..)).mpr first
    · have last := ((rt_model_delta_l fs.transitive nc (rd_entry0_delta_l (.bound 7) (.bound 4) (.bound 13)) ρs).trans
        (rd_entry0_sat_l hK.1 ..)).mp last
      exact ((rt_model_delta_l fs.transitive nc (rd_entry0_delta_l (.bound 3) (.bound 18) (.bound 15)) ξ).trans
        (rd_entry0_sat_l hK.1 ..)).mpr last
    · have graph := ((Formula.satisfies_conj_iff ..).mp ((Formula.satisfies_conj_iff ..).mp
        ((Formula.satisfies_conj_iff ..).mp node).2).2).1
      exact (tg_graph_source_l fs.transitive nc hK.1 (KP.exists_pair hK) ξ (.bound 2) (.bound 19)).mpr
        ((tg_graph_source_l fs.transitive nc hK.1 (KP.exists_pair hK) ρs (.bound 6) (.bound 26)).mp graph)
    · change Formula.satisfies ξ ((sg_set_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3) : Formula 1 4).bind
        (fun i => [.bound 1, .bound 3, .bound 15, .bound 19].get i))
      apply (Formula.satisfies_bind ..).mpr
      apply (Formula.closed_env_l (sg_set_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3) : Formula 1 4)
        (by simp -implicitDefEqProofs [sg_set_m, Definitional.Formula.FreeClosed]) ?_).mp ((Formula.satisfies_bind ρs
        (fun i : Fin 4 => [Term.bound 1, Term.bound 7, Term.bound 13, Term.bound 26].get i)
        (sg_set_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3))).mp set)
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))) i
  have recovered := kernel.recover_seed_l ξ raw
  simp only [tc_recover_result0_m, Formula.satisfies_exists_iff] at recovered
  obtain ⟨A, c, H, r', g, z, π, recovered⟩ := recovered
  let θ := ξ.push A |>.push c |>.push H |>.push r' |>.push g |>.push z |>.push π
  refine ⟨θ, ?_, ?_⟩
  · intro i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
          (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))))))))))))))) i
  · exact recovered

end YesMetaZFC.SetTheory.LargeCardinal
