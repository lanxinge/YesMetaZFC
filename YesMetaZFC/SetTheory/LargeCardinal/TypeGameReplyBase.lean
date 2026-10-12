import YesMetaZFC.Model.SetTheory.Internal.TypeGameQueryScope

/-! # 回答查询只使用 ω 的共同基底

空根、严格秩界和末位加二三条原查询先在单一常量域 {ω} 中产生。
因此它们不随回答的较大 κ 型域改变，可沿固定低层搬运全部读取性质。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Tg_reply_base_d (ω e l n r b h : M.Domain) : Prop := ∃ U D,
  Pair_d M U ω ω ∧ Tt_pool_d I ω n U D ∧ Tg_root_query_d I ω e n U D r ∧
    Tg_bound_query_d I ω e l n U D b ∧ Tg_height_query_d I ω l n U D h

def tg_reply_base0_m : Formula 1 7 :=
  let p : Fin 7 → Term 7 := Term.bound
  set[7] ⟪∃ U D,
    ⌜pair0_m⌝ₚ(U, ⌜p 0⌝ₛ, ⌜p 0⌝ₛ) ∧ ⌜tt_pool_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 3⌝ₛ, U, D) ∧
    ⌜tg_root_query_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 1⌝ₛ, ⌜p 3⌝ₛ, U, D, ⌜p 4⌝ₛ) ∧
    ⌜tg_bound_query_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 1⌝ₛ, ⌜p 2⌝ₛ, ⌜p 3⌝ₛ, U, D, ⌜p 5⌝ₛ) ∧
    ⌜tg_height_query_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 2⌝ₛ, ⌜p 3⌝ₛ, U, D, ⌜p 6⌝ₛ)⟫

theorem tg_reply_base0_closed_l : tg_reply_base0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_reply_base0_m, Definitional.Formula.FreeClosed]

def tg_reply_base_m {d} (ω e l n r b h : Term d) : Formula 1 d :=
  tg_reply_base0_m.bind (fun i => [ω, e, l, n, r, b, h].get i)

@[simp] theorem tg_reply_base_closed_l {d} (ω e l n r b h : Term d)
    (hw : ω.freeSupport = []) (he : e.freeSupport = []) (hl : l.freeSupport = []) (hn : n.freeSupport = [])
    (hr : r.freeSupport = []) (hb : b.freeSupport = []) (hh : h.freeSupport = []) :
    (tg_reply_base_m ω e l n r b h).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tg_reply_base0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hw, he, hl, hn, hr, hb, hh, fun i => Fin.elim0 i⟩

theorem tg_reply_base_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω e l n r b h : Term d) :
    Formula.satisfies ρ (tg_reply_base_m ω e l n r b h) ↔
      Tg_reply_base_d I (ω.eval ρ) (e.eval ρ) (l.eval ρ) (n.eval ρ) (r.eval ρ) (b.eval ρ) (h.eval ρ) := by
  simp only [tg_reply_base_m, Formula.satisfies_bind, tg_reply_base0_m, Tg_reply_base_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    pair0_sat_l hKP.1, tt_pool_sat_l I hKP, tg_root_query_sat_l I hKP, tg_bound_query_sat_l I hKP,
    tg_height_query_sat_l I hKP, Definitional.Term.eval_weaken]
  rfl

theorem Tg_reply_base_d.scope_l (hKP : M.Models KP) {ω e l n r b h V W : M.Domain}
    (base : Tg_reply_base_d I ω e l n r b h) (pool : Tt_pool_d I ω n V W) (hw : M.mem ω V) :
    Tg_root_query_d I ω e n V W r ∧ Tg_bound_query_d I ω e l n V W b ∧ Tg_height_query_d I ω l n V W h := by
  obtain ⟨U, D, pair, small, root, bound, height⟩ := base
  have sub : M.MemberSubset U V := fun x hx => ((pair x).mp hx).elim
    (fun eq => eq.symm ▸ hw) (fun eq => eq.symm ▸ hw)
  exact ⟨root.scope_l I hKP small pool sub, bound.scope_l I hKP small pool sub, height.scope_l I hKP small pool sub⟩

theorem tg_reply_base_l (hZF : M.Models ZF) {ω e l n : M.Domain} (hω : M.IsOmega ω)
    (he : ∀ x, ¬ M.mem x e) (hen : M.mem e n) (hl : M.mem l n) :
    ∃ r b h, Tg_reply_base_d (kp_pair_l (ZF.modelsKP hZF)) ω e l n r b h := by
  let J := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨U, pair⟩ := KP.exists_pair (ZF.modelsKP hZF) ω ω
  obtain ⟨D, pool⟩ := tt_pool_exists_l J hZF hω n U
  obtain ⟨r, root⟩ := tt_root_query_l hZF hω he hen pool
  obtain ⟨b, bound⟩ := tt_bound_query_l hZF hω hen hl ((pair ω).mpr (Or.inl rfl)) pool
  obtain ⟨h, height⟩ := tt_height_query_l hZF hω hl pool
  exact ⟨r, b, h, U, D, pair, pool, root, bound, height⟩

end YesMetaZFC.SetTheory.LargeCardinal
