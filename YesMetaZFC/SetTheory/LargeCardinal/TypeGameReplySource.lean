import YesMetaZFC.SetTheory.LargeCardinal.TypeGameAnswer
import YesMetaZFC.Model.SetTheory.Internal.SubtypeSource
import YesMetaZFC.Model.SetTheory.Internal.TypeDropSource

/-! # 规则 (7) 从证书层读取为实际回答

原 dcp 由传递性和配对闭包绝对读取，子类型沿原存在见证向上读取。
所得回答仍是相同类型集合和相同查询码的字面成员判断。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hKP : M.Models KP) {X : M.Domain} (hX : M.TransitiveSet X)
  (nx : Nonempty {x // M.mem x X})
  (pair : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b)
local notation "N" => rt_model_l X nx
include hX pair

theorem tg_reply_source_l {d} (ρ : Env N d) (ω l n κ τ U D W u w b z r q h : Term d) (σ : Fin 7 → Term d)
    (valid : Formula.satisfies ρ (tg_reply_m ω l n κ τ U D W u w b z r q h σ)) :
    Tg_reply_d (kp_pair_l hKP) (ω.eval ρ).val (l.eval ρ).val (n.eval ρ).val (κ.eval ρ).val (τ.eval ρ).val
      (U.eval ρ).val (D.eval ρ).val (W.eval ρ).val (u.eval ρ).val (w.eval ρ).val (b.eval ρ).val
      (fun i => (σ i).eval ρ |>.val) (z.eval ρ).val ⟨(r.eval ρ).val, (q.eval ρ).val, (h.eval ρ).val⟩ := by
  let ε := Definitional.Env.substitute ρ (fun i => [ω, l, n, κ, τ, U, D, W, u, w, b, z, r, q, h,
    σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6].get i)
  let s : Fin 7 → Term 22 := Fin.cases (.bound 15) (Fin.cases (.bound 16) (Fin.cases (.bound 17)
    (Fin.cases (.bound 18) (Fin.cases (.bound 19) (Fin.cases (.bound 20) (fun _ => .bound 21))))))
  simp only [tg_reply_m, Formula.satisfies_bind, tg_reply0_m, Formula.satisfies_conj_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_mem_iff, Definitional.Term.eval_weaken] at valid
  obtain ⟨sub, v, drop, code, root, bound, height⟩ := valid
  have subset : M.MemberSubset (w.eval ρ).val (W.eval ρ).val :=
    fun x hx => sub ⟨x, hX (w.eval ρ).val (w.eval ρ).property x hx⟩ hx
  have drop := (td_dcp_source_l hKP.1 (KP.exists_pair hKP) hX nx pair _ _ _ _ _ _).mp drop
  have code := ts_subtype_source_l hKP hX nx _ _ _ _ _ _ _ _ _ _ _ _ code
  simp only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest] at drop code
  have eq : (fun i => (s i).eval ε |>.val) = (fun i => (σ i).eval ρ |>.val) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  have code : Ts_subtype_d (ω.eval ρ).val (l.eval ρ).val (κ.eval ρ).val (τ.eval ρ).val
      (n.eval ρ).val (U.eval ρ).val (w.eval ρ).val (b.eval ρ).val (fun i => (s i).eval ε |>.val)
      (z.eval ρ).val v.val := code
  exact ⟨subset, v.val, drop, eq ▸ code, root, bound, height⟩

end YesMetaZFC.SetTheory.LargeCardinal
