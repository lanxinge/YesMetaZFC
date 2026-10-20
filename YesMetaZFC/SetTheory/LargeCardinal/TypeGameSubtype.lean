import YesMetaZFC.SetTheory.LargeCardinal.TypeGameContext
import YesMetaZFC.Model.SetTheory.Internal.SubtypeReflect

/-! # 实际像上的原子类型证书返回反射层

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
    (context : Tg_context_d ω X η C) (source : Ep_source_d hZF ω μ K X R)
    (hU : M.mem U C) (hu : M.mem u C) (hb : M.mem b ω)
    (subtype : Ts_subtype_d ω n κ τ m U w b σ z u) : Tg_subtype_in_d ω n κ τ m U w b z u σ C := by
  have fs := (context.read_l hZF source).1
  obtain ⟨c, T, model⟩ := smdl_membership_l I hZF ⟨ω, context.omega⟩
  have theory := source.rank_theory_l hZF context.member context.rank context.limit model
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
    exact ⟨context.omega, member n hn, member κ hκ, member τ hτ, member m hm, hU, member w hw,
      fs.transitive ω context.omega b hb, zF.1, hu, hs 0, hs 1, hs 2, hs 3, hs 4, hs 5, hs 6, fun i => Fin.elim0 i⟩
  let nc : Nonempty {a // M.mem a C} := ⟨⟨ω, context.omega⟩⟩
  let ρ : Env (rt_model_l C nc) 17 := ⟨fun i => ⟨p i, hp i⟩, fun _ => ⟨ω, context.omega⟩⟩
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
