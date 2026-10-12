import YesMetaZFC.SetTheory.LargeCardinal.TypeGameCandidate
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameSubtype
import YesMetaZFC.Model.SetTheory.Internal.SubtypeProgramTransfer

/-! # 继续树边目标中的真实低层实现

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
    (context : Tg_context_d ω X η C) (source : Ep_source_d hZF ω μ K X R)
    (old : Formula.satisfies ρ tg_round0_m) (candidate : Formula.satisfies χ tg_candidate0_m)
    (hn : p 24 = n) (hκ : p 15 = κ) (hU : p 13 = U) (ht : p 11 = t)
    (hτ : (χ.bound 3).val = τ) (hm : (χ.bound 1).val = m) (hu : (χ.bound 0).val = u)
    (finite : M.mem m ω) (program : Ts_program_in_d ω n b z σ C)
    (subtype : Tg_subtype_in_d ω n κ τ m U u b z t σ C) :
    ∃ W ν, Tt_pool_d I ω m (χ.bound 6).val W ∧ M.mem ν (p 10) ∧
      Tg_realized_in_d ω (p 18) n (p 29) m (χ.bound 6).val W u ν C := by
  have fs := (context.read_l hZF source).1
  obtain ⟨c, H, model⟩ := smdl_membership_l I hZF ⟨ω, context.omega⟩
  obtain ⟨seed, round⟩ := (Formula.satisfies_conj_iff ..).mp old
  simp only [tg_seed0_m, Formula.satisfies_rename, tg_seed_m, Formula.satisfies_conj_iff] at seed
  have omega : (N).IsOmega (ρ.bound 16) := (Formula.satisfies_isOmega_iff ..).mp seed.1
  let w₀ : (N).Domain := ⟨ω, context.omega⟩
  have actual := rt_omega_l fs.transitive nc hZF.1 w₀ source.omega
  have eqω := (rt_model_ext_l hZF.1 fs.transitive nc).eq_of_same_members (ρ.bound 16) w₀
    (fun x => ⟨omega.2 w₀ actual.1 x, actual.2 (ρ.bound 16) omega.1 x⟩)
  have hw : p 16 = ω := congrArg Subtype.val eqω
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff] at round
  obtain ⟨_, _, _, _, rank, code, language, type, _⟩ := round
  simp only [ee_language_m, Formula.satisfies_bind, ee_language0_m, Formula.satisfies_conj_iff] at language
  have newLanguage := (Formula.satisfies_conj_iff ..).mp candidate |>.1
  simp only [Formula.satisfies_rename, ee_language0_m, Formula.satisfies_conj_iff] at newLanguage
  obtain ⟨_, limit, base, constants, _⟩ := newLanguage
  obtain ⟨W, pool⟩ := tt_pool_exists_l I hZF source.omega m (χ.bound 6).val
  have hmC : M.mem m C := hm ▸ (χ.bound 1).property
  obtain ⟨hW, A, E, hA, hE, names, seq, product⟩ := source.pool_rank_l hZF context.member context.rank
    context.limit context.omega hmC (χ.bound 6).property pool
  let W₀ : (N).Domain := ⟨W, hW⟩
  let b₀ : (N).Domain := ⟨b, program.1 2⟩
  let z₀ : (N).Domain := ⟨z, program.1 3⟩
  have hs : ∀ i, M.mem (σ i) C := by
    intro i
    exact Fin.cases (program.1 4) (Fin.cases (program.1 5) (Fin.cases (program.1 6) (Fin.cases (program.1 7)
      (Fin.cases (program.1 8) (Fin.cases (program.1 9) (Fin.cases (program.1 10) (fun j => Fin.elim0 j))))))) i
  let s : Fin 7 → (N).Domain := fun i => ⟨σ i, hs i⟩
  let ψ : Env N 27 := ⟨fun i => [ρ.bound 16, ρ.bound 24, b₀, z₀, ρ.bound 10, ρ.bound 9, ρ.bound 8,
    ρ.bound 7, ρ.bound 29, ρ.bound 18, ρ.bound 13, ρ.bound 12, ρ.bound 11, ρ.bound 15,
    χ.bound 3, χ.bound 1, χ.bound 5, χ.bound 6, W₀, χ.bound 0, s 0, s 1, s 2, s 3, s 4, s 5, s 6].get i,
      fun _ => w₀⟩
  let fo : Fin 10 → Term 54 := fun i => [.bound 16, .bound 8, .bound 9, .bound 7, .bound 24,
    .bound 29, .bound 18, .bound 13, .bound 12, .bound 11].get i
  let ft : Fin 10 → Term 27 := fun i => [.bound 0, .bound 6, .bound 5, .bound 7, .bound 1,
    .bound 8, .bound 9, .bound 10, .bound 11, .bound 12].get i
  have type₀ := (Formula.satisfies_bind ρ fo tt_realized0_m).mp type
  have type' : Formula.satisfies ψ (tt_realized_m (.bound 0) (.bound 6) (.bound 5) (.bound 7) (.bound 1)
      (.bound 8) (.bound 9) (.bound 10) (.bound 11) (.bound 12)) := by
    apply (Formula.satisfies_bind ψ ft tt_realized0_m).mpr
    apply (Formula.closed_env_l tt_realized0_m tt_realized0_closed_l ?_).mp type₀
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))) i
  let fp : Fin 11 → Term 27 := fun i => [.bound 0, .bound 1, .bound 2, .bound 3,
    .bound 20, .bound 21, .bound 22, .bound 23, .bound 24, .bound 25, .bound 26].get i
  let pn : Fin 11 → M.Domain := fun i => [ω, n, b, z, σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6].get i
  have prog : Formula.satisfies ψ (ts_numeric_m (.bound 0) (.bound 1) (.bound 2) (.bound 3)
      (fun i => [Term.bound 20, Term.bound 21, Term.bound 22, Term.bound 23, Term.bound 24, Term.bound 25, Term.bound 26].get i)) := by
    apply (Formula.satisfies_bind ψ fp ts_numeric0_m).mpr
    apply (sc_relative_sat_l I model fs.transitive nc ts_numeric0_m ts_numeric0_closed_l
      (Definitional.Env.substitute ψ fp) ((⟨pn, fun _ => ω⟩ : Env M 11).push C)
      .newest (fun i => .bound i.succ) rfl ?_).mp program.2
    intro i
    exact Fin.cases hw.symm (Fin.cases hn.symm (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))))))) i
  let fq : Fin 17 → Term 27 := fun i => [.bound 0, .bound 1, .bound 13, .bound 14, .bound 15, .bound 10,
    .bound 19, .bound 2, .bound 3, .bound 12, .bound 20, .bound 21, .bound 22, .bound 23, .bound 24, .bound 25, .bound 26].get i
  let pq : Fin 17 → M.Domain := fun i => [ω, n, κ, τ, m, U, u, b, z, t, σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6].get i
  have sub : Formula.satisfies (Definitional.Env.substitute ψ fq) tg_subtype0_m := by
    apply (sc_relative_sat_l I model fs.transitive nc tg_subtype0_m tg_subtype0_closed_l
      (Definitional.Env.substitute ψ fq) ((⟨pq, fun _ => ω⟩ : Env M 17).push C)
      .newest (fun i => .bound i.succ) rfl ?_).mp subtype.2
    intro i
    exact Fin.cases hw.symm (Fin.cases hn.symm (Fin.cases hκ.symm (Fin.cases hτ.symm (Fin.cases hm.symm
      (Fin.cases hU.symm (Fin.cases hu.symm (Fin.cases rfl (Fin.cases rfl (Fin.cases ht.symm
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
          (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))))))))))))) i
  have raw : Formula.satisfies ψ tc_realize_seed0_m := by
    simp only [tc_realize_seed0_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff]
    refine ⟨(Formula.satisfies_isOmega_iff ..).mpr omega, prog, rank, code, type', language.2.1,
      limit, ?_, base, constants, ?_, ?_⟩
    · change M.mem (χ.bound 1).val (p 16)
      exact Eq.mpr ((congrArg (fun a => M.mem a (p 16)) hm).trans (congrArg (fun a => M.mem m a) hw)) finite
    · apply (fs.pool_sat_l (ZF.modelsKP hZF) nc ψ (.bound 0) (.bound 15) (.bound 17) (.bound 18) hw).mpr
      exact ⟨A, E, hA, hE, hm.symm ▸ names, seq, product⟩
    · exact (Formula.satisfies_bind ψ fq tg_subtype0_m).mpr sub
  have realized := context.realize_seed_l hZF source nc ψ raw
  simp only [tc_realize_result0_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff] at realized
  obtain ⟨ν, bound, realized⟩ := realized
  let ξ : Env N 9 := ⟨fun i => [ρ.bound 16, ρ.bound 18, ρ.bound 24, ρ.bound 29, χ.bound 1, χ.bound 6, W₀, χ.bound 0, ν].get i,
    fun _ => w₀⟩
  let pr : Fin 9 → M.Domain := fun i => [ω, p 18, n, p 29, m, (χ.bound 6).val, W, u, ν.val].get i
  have same : ∀ i, pr i = (ξ.bound i).val := Fin.cases hw.symm (Fin.cases rfl (Fin.cases hn.symm
    (Fin.cases rfl (Fin.cases hm.symm (Fin.cases rfl (Fin.cases rfl (Fin.cases hu.symm (Fin.cases rfl (fun j => Fin.elim0 j)))))))))
  have members i : M.mem (pr i) C := Eq.mpr (congrArg (fun a => M.mem a C) (same i)) (ξ.bound i).property
  let fa : Fin 9 → Term 28 := fun i =>
    [.bound 1, .bound 10, .bound 2, .bound 9, .bound 16, .bound 18, .bound 19, .bound 20, .bound 0].get i
  have proof : Formula.satisfies ξ ts_at0_m := by
    apply (Formula.closed_env_l ts_at0_m ts_at0_closed_l ?_).mp ((Formula.satisfies_bind (ψ.push ν) fa ts_at0_m).mp realized)
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))))) i
  exact ⟨W, ν.val, pool, bound, members,
    (sc_relative_sat_l I model fs.transitive nc ts_at0_m ts_at0_closed_l ξ
      ((⟨pr, fun _ => ω⟩ : Env M 9).push C) .newest (fun i => .bound i.succ) rfl same).mpr proof⟩

end YesMetaZFC.SetTheory.LargeCardinal
