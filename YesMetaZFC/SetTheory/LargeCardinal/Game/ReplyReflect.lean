import YesMetaZFC.SetTheory.LargeCardinal.Game.RawReply
import YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype
import YesMetaZFC.Model.SetTheory.Types.SubtypeReflect
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.RelativeRankSegment

/-! # 同一个规则 (7) 回到后继反射层

在源内实际分离出原 dcp，用唯一性识别回答中的 dcp。原名字域也在源中
构造，因而子类型证书的全部见证可回收；不要求反射层满足 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_reply_in_d (ω l n κ τ U D Q u w b z r q h : M.Domain) (σ : Fin 7 → M.Domain) (C : M.Domain) : Prop :=
  let p : Fin 22 → M.Domain := fun i => [ω, l, n, κ, τ, U, D, Q, u, w, b, z, r, q, h,
    σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6].get i
  Formula.satisfies ((⟨p, fun _ => ω⟩ : Env M 22).push C)
    (lr_rel_m tg_reply0_m .newest (fun i => .bound i.succ))

theorem tg_reply_reflect_l {ω c X R : M.Domain} (hω : M.IsOmega ω) (hX : M.TransitiveSet X)
    (model : Smem_d I c X R) (theory : Sc_theory_d I ω X R) (nx : Nonempty {x // M.mem x X})
    {d} (ρ : Env (rt_model_l X nx) d) (o l n κ τ U D W u w b z r q h : Term d) (σ : Fin 7 → Term d)
    (valid : Tg_reply_d I (o.eval ρ).val (l.eval ρ).val (n.eval ρ).val (κ.eval ρ).val (τ.eval ρ).val
      (U.eval ρ).val (D.eval ρ).val (W.eval ρ).val (u.eval ρ).val (w.eval ρ).val (b.eval ρ).val
      (fun i => (σ i).eval ρ |>.val) (z.eval ρ).val ⟨(r.eval ρ).val, (q.eval ρ).val, (h.eval ρ).val⟩) :
    Formula.satisfies ρ (tg_reply_m o l n κ τ U D W u w b z r q h σ) := by
  let N := rt_model_l X nx
  let ε := Definitional.Env.substitute ρ (fun i => [o, l, n, κ, τ, U, D, W, u, w, b, z, r, q, h,
    σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6].get i)
  let s : Fin 7 → Term 22 := Fin.cases (.bound 15) (Fin.cases (.bound 16) (Fin.cases (.bound 17)
    (Fin.cases (.bound 18) (Fin.cases (.bound 19) (Fin.cases (.bound 20) (fun _ => .bound 21))))))
  obtain ⟨subset, v, drop, subtype, root, bound, height⟩ := valid
  obtain ⟨v', hv, project⟩ := td_project_source_exists_l hX hZF hω model theory
    (l.eval ρ).property (n.eval ρ).property (D.eval ρ).property (u.eval ρ).property
  have eq := project.unique_l I hZF.1 drop.2
  subst v'
  obtain ⟨A, hA, names⟩ := tn_names_source_l hZF hω hX model theory (l.eval ρ).property (U.eval ρ).property
  let v₀ : (N).Domain := ⟨v, hv⟩
  have sub : Formula.satisfies ε (Formula.subset (.bound 9) (.bound 7)) := by
    apply (rt_model_delta_l hX nx (.atom ..) ε).mpr
    apply (Formula.satisfies_subset_iff ..).mpr
    exact subset
  simp only [tg_reply_m, Formula.satisfies_bind, tg_reply0_m,
    Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]
  refine ⟨sub, v₀, ?_, ?_, root, bound, height⟩
  · apply (td_dcp_source_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hX nx (theory.algebra_l _ (ZF.modelsKP hZF) hX model).pair ..).mpr
    simp only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
    exact drop
  · apply ts_subtype_reflect_l (ZF.modelsKP hZF) hX nx _ _ _ _ _ _ _ _ _ _ _ _ hA
      (by exact names)
    have eq : (fun i => (s i).eval ε |>.val) = (fun i => (σ i).eval ρ |>.val) := by
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
    have subtype : Ts_subtype_d (o.eval ρ).val (l.eval ρ).val (κ.eval ρ).val (τ.eval ρ).val
        (n.eval ρ).val (U.eval ρ).val (w.eval ρ).val (b.eval ρ).val (fun i => (s i).eval ε |>.val)
        (z.eval ρ).val v := eq.symm ▸ subtype
    simp only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
    exact subtype

theorem Tg_context_d.reply_l {ω κ K X R η C : M.Domain} (context : Tg_context_d I ω X R η C)
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (nc : Nonempty {x // M.mem x C})
    {d} (ρ : Env (rt_model_l C nc) d) (o l n a τ U D W u w b z r q h : Term d) (σ : Fin 7 → Term d)
    (valid : Tg_reply_d I (o.eval ρ).val (l.eval ρ).val (n.eval ρ).val (a.eval ρ).val (τ.eval ρ).val
      (U.eval ρ).val (D.eval ρ).val (W.eval ρ).val (u.eval ρ).val (w.eval ρ).val (b.eval ρ).val
      (fun i => (σ i).eval ρ |>.val) (z.eval ρ).val ⟨(r.eval ρ).val, (q.eval ρ).val, (h.eval ρ).val⟩) :
    Formula.satisfies ρ (tg_reply_m o l n a τ U D W u w b z r q h σ) := by
  obtain ⟨c, T, model⟩ := smdl_membership_l I hZF ⟨ω, (context.omega_l source.code)⟩
  exact tg_reply_reflect_l hZF source.omega (context.read_l hZF source).1.transitive model
    (source.rank_theory_l hZF context.member (context.rank_l (ZF.modelsKP hZF) source.transitive source.code) (context.limit_l (ZF.modelsKP hZF) source.transitive source.code) model) nc ρ o l n a τ U D W u w b z r q h σ valid

/-- 支撑秩段容纳新查询域；子类型查询自身回收回答和全部域参数。 -/
theorem Tg_context_d.support_reply_l {ω μ K X R η C l n κ τ U D Q u w b z r q h L W : M.Domain}
    {σ : Fin 7 → M.Domain} (context : Tg_context_d I ω X R η C) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K X R)
    (level : Er_level_d X L W) (hQW : M.mem Q W) (bound : M.MemberSubset L κ) (hκ : M.IsOrdinal κ)
    (hU : M.mem U C) (hD : M.mem D C) (hu : M.mem u C)
    (hb : M.mem b ω) (hz : M.mem z ω) (hσ : ∀ i, M.mem (σ i) ω)
    (reply : Tg_reply_d I ω l n κ τ U D Q u w b σ z ⟨r, q, h⟩) :
    Tg_reply_in_d ω l n κ τ U D Q u w b z r q h σ C := by
  have fs := (context.read_l hZF source).1
  have data := reply
  obtain ⟨_, t, _, ⟨_, _, p, query, _⟩, hr, hq, hh⟩ := data
  obtain ⟨hw, hn, hl, hτ, hk, _⟩ := query.1
  have member x (hx : M.mem x U) := fs.transitive U hU x hx
  have small x (hx : M.mem x ω) := fs.transitive ω (context.omega_l source.code) x hx
  have hκη := (context.rank_l (ZF.modelsKP hZF) source.transitive source.code).ordinal_height_l hZF source.transitive context.member hκ (member κ hk)
  have inside := ((context.rank_l (ZF.modelsKP hZF) source.transitive source.code).compare_l hZF source.transitive context.member level.member level.hierarchy
    (fun x hx => (context.limit_l (ZF.modelsKP hZF) source.transitive source.code).1.transitive κ hκη x (bound x hx))).1
  let p : Fin 22 → M.Domain := fun i => [ω, l, n, κ, τ, U, D, Q, u, w, b, z, r, q, h,
    σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6].get i
  have hp : ∀ i, M.mem (p i) C := by
    simp only [Fin.forall_fin_succ]
    exact ⟨(context.omega_l source.code), member l hl, member n hn, member κ hk, member τ hτ, hU, hD, inside Q hQW,
      hu, member w hw, small b hb, small z hz, fs.transitive w (member w hw) r hr,
      fs.transitive w (member w hw) q hq, fs.transitive w (member w hw) h hh,
      small (σ 0) (hσ 0), small (σ 1) (hσ 1), small (σ 2) (hσ 2), small (σ 3) (hσ 3),
      small (σ 4) (hσ 4), small (σ 5) (hσ 5), small (σ 6) (hσ 6), fun i => Fin.elim0 i⟩
  let nc : Nonempty {x // M.mem x C} := ⟨⟨ω, (context.omega_l source.code)⟩⟩
  let ρ : Env (rt_model_l C nc) 22 := ⟨fun i => ⟨p i, hp i⟩, fun _ => ⟨ω, (context.omega_l source.code)⟩⟩
  let f : Fin 7 → Term 22 := Fin.cases (.bound 15) (Fin.cases (.bound 16) (Fin.cases (.bound 17)
    (Fin.cases (.bound 18) (Fin.cases (.bound 19) (Fin.cases (.bound 20) (fun _ => .bound 21))))))
  have valid : Formula.satisfies ρ tg_reply0_m := by
    apply context.reply_l hZF source nc ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)
      (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) (.bound 10) (.bound 11) (.bound 12) (.bound 13)
      (.bound 14) f
    have eq : (fun i => (f i).eval ρ |>.val) = σ := by
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
    rw [eq]
    exact reply
  exact (sc_relative_sat_l fs.transitive nc tg_reply0_m tg_reply0_closed_l ρ
    ((⟨p, fun _ => ω⟩ : Env M 22).push C) .newest (fun i => .bound i.succ) rfl (fun _ => rfl)).mpr valid

end YesMetaZFC.SetTheory.LargeCardinal
