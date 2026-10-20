import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRealization
import YesMetaZFC.Model.SetTheory.Internal.TypeGameNodeSource

/-! # 在实际目标反射层内恢复一张图

旧轮记录提供旧根、标签图和严格秩界；新查询行提供原节点规则。
低层实现保持任意排列，恢复的全部见证仍属于同一个目标反射层。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω X C η : M.Domain} (nc : Nonempty {x // M.mem x C})
  (ρ : Env (rt_model_l C nc) 54) (ψ : Env (rt_model_l C nc) 12)
local notation "N" => rt_model_l C nc
local notation "p" => (fun i => Subtype.val (Env.bound ρ i))

theorem Tg_context_d.recover_l {κ K R U W u ν : M.Domain}
    (context : Tg_context_d ω X η C) (source : Ep_source_d hZF ω κ K X R)
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
  have fs := (context.read_l hZF source).1
  let ρs := ρ.reindex (fun i : Fin 38 => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
  obtain ⟨seed, _⟩ := (Formula.satisfies_conj_iff ..).mp old
  simp only [tg_seed0_m, Formula.satisfies_rename, tg_seed_m, Formula.satisfies_conj_iff] at seed
  obtain ⟨omega, empty, heω, _, _, root, _, hk, hl, _, _, _, oldType, _, _, _, first, last, set, node, _, _, bound⟩ := seed
  have omega := (Formula.satisfies_isOmega_iff ..).mp omega
  let w₀ : (N).Domain := ⟨ω, context.omega⟩
  have actual := rt_omega_l fs.transitive nc hZF.1 w₀ source.omega
  have eqω := (rt_model_ext_l hZF.1 fs.transitive nc).eq_of_same_members (ρ.bound 16) w₀
    (fun x => ⟨omega.2 w₀ actual.1 x, actual.2 (ρ.bound 16) omega.1 x⟩)
  have hw : p 16 = ω := congrArg Subtype.val eqω
  have finite₀ := oldType
  simp only [tt_realized_m, Formula.satisfies_bind, tt_realized0_m, Formula.satisfies_conj_iff] at finite₀
  have hnω : M.mem (p 24) ω := hw ▸ finite₀.2.1
  have hk₀ := (rt_successor_l fs.transitive nc hZF.1 (ρ.bound 23) (ρ.bound 22)).mp
    ((Formula.satisfies_isSuccessor_iff ..).mp hk)
  have hl₀ := (rt_successor_l fs.transitive nc hZF.1 (ρ.bound 24) (ρ.bound 23)).mp
    ((Formula.satisfies_isSuccessor_iff ..).mp hl)
  have ok := (source.omega.members_areOrdinals hZF _ hnω).mem hl₀.predecessor_mem
  have he : ∀ a, ¬ M.mem a (p 17) := by
    intro a ha
    exact (Formula.satisfies_isEmpty_iff ..).mp empty ⟨a, fs.transitive _ (ρ.bound 17).property a ha⟩ ha
  have hek : M.mem (p 17) (p 23) := by
    have heω : M.mem (p 17) (p 16) := heω
    have oe := source.omega.members_areOrdinals hZF _ (hw ▸ heω)
    rcases oe.trichotomy hZF.1 (ok.mem hk₀.predecessor_mem) (KP.difference_exists_d (ZF.modelsKP hZF))
      (KP.intersection_exists_d (ZF.modelsKP hZF) (p 17) (p 22)) with eq | lt | gt
    · exact (hk₀ _).mpr (Or.inr eq)
    · exact (hk₀ _).mpr (Or.inl lt)
    · exact (he _ gt).elim
  have row := (Formula.satisfies_conj_iff ..).mp queries
  have sk := (rt_successor_l fs.transitive nc hZF.1 (ψ.bound 2) (ψ.bound 4)).mp
    ((Formula.satisfies_isSuccessor_iff ..).mp row.2.1)
  have eqk : (ψ.bound 4).val = p 23 :=
    (hl₀.predecessor_eq hZF.1 ok (Eq.mp (congrArg (fun a => M.SuccessorOf a (ψ.bound 4).val) lψ) sk)).symm
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
    · exact (Formula.satisfies_isSuccessor_iff ..).mpr ((rt_successor_l fs.transitive nc hZF.1 ..).mpr hk₀)
    · exact (Formula.satisfies_isSuccessor_iff ..).mpr ((rt_successor_l fs.transitive nc hZF.1 ..).mpr hl₀)
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
        (rd_entry0_sat_l hZF.1 ..)).mp first
      exact ((rt_model_delta_l fs.transitive nc (rd_entry0_delta_l (.bound 1) (.bound 17) (.bound 15)) ξ).trans
        (rd_entry0_sat_l hZF.1 ..)).mpr first
    · have last := ((rt_model_delta_l fs.transitive nc (rd_entry0_delta_l (.bound 7) (.bound 4) (.bound 13)) ρs).trans
        (rd_entry0_sat_l hZF.1 ..)).mp last
      exact ((rt_model_delta_l fs.transitive nc (rd_entry0_delta_l (.bound 3) (.bound 18) (.bound 15)) ξ).trans
        (rd_entry0_sat_l hZF.1 ..)).mpr last
    · have graph := ((Formula.satisfies_conj_iff ..).mp ((Formula.satisfies_conj_iff ..).mp
        ((Formula.satisfies_conj_iff ..).mp node).2).2).1
      exact (tg_graph_source_l fs.transitive nc hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ξ (.bound 2) (.bound 19)).mpr
        ((tg_graph_source_l fs.transitive nc hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ρs (.bound 6) (.bound 26)).mp graph)
    · change Formula.satisfies ξ ((sg_set_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3) : Formula 1 4).bind
        (fun i => [.bound 1, .bound 3, .bound 15, .bound 19].get i))
      apply (Formula.satisfies_bind ..).mpr
      apply (Formula.closed_env_l (sg_set_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3) : Formula 1 4)
        (by simp -implicitDefEqProofs [sg_set_m, Definitional.Formula.FreeClosed]) ?_).mp ((Formula.satisfies_bind ρs
        (fun i : Fin 4 => [Term.bound 1, Term.bound 7, Term.bound 13, Term.bound 26].get i)
        (sg_set_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3))).mp set)
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))) i
  have recovered := (context.kernel_l (context.read_l hZF source).1.transitive nc).recover_seed_l ξ raw
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
