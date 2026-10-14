import YesMetaZFC.SetTheory.LargeCardinal.TypeGameOddLimit

/-! # 原返回节点的一阶公式

公式只量化原保存码的固定元数坐标。内部轮号、结点、有限长度及两层
嵌入条目保持原值，供替代和内部归纳直接使用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

private def tg_return_body_m : Formula 1 79 := .conj
  (tg_past_at_m (.bound 69) (.bound 72) (.bound 73) (.bound 0) (.bound 1) (.bound 2)
    (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8)) (.conj
  (rt_tuple_m (Fin.cases (.bound 68) (Fin.cases (.bound 7)
    (fun i : Fin 54 => .bound (Fin.natAdd 14 (i.castAdd 11))))) (.bound 8))
  (set[79] ⟪⌜(.bound 74 : Term 79)⌝ₛ = ⌜(.bound 36 : Term 79)⌝ₛ ∧
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 9 : Term 79)⌝ₛ, ⌜(.bound 33 : Term 79)⌝ₛ, ⌜(.bound 70 : Term 79)⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 10 : Term 79)⌝ₛ, ⌜(.bound 54 : Term 79)⌝ₛ, ⌜(.bound 70 : Term 79)⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 11 : Term 79)⌝ₛ, ⌜(.bound 55 : Term 79)⌝ₛ, ⌜(.bound 70 : Term 79)⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 12 : Term 79)⌝ₛ, ⌜(.bound 56 : Term 79)⌝ₛ, ⌜(.bound 70 : Term 79)⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 73 : Term 79)⌝ₛ, ⌜(.bound 13 : Term 79)⌝ₛ, ⌜(.bound 71 : Term 79)⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 9 : Term 79)⌝ₛ, ⌜(.bound 75 : Term 79)⌝ₛ, ⌜(.bound 13 : Term 79)⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 10 : Term 79)⌝ₛ, ⌜(.bound 76 : Term 79)⌝ₛ, ⌜(.bound 13 : Term 79)⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 11 : Term 79)⌝ₛ, ⌜(.bound 77 : Term 79)⌝ₛ, ⌜(.bound 13 : Term 79)⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 12 : Term 79)⌝ₛ, ⌜(.bound 78 : Term 79)⌝ₛ, ⌜(.bound 13 : Term 79)⌝ₛ)⟫))

def tg_return_node0_m : Formula 1 11 := rt_exists_m 54 (rt_exists_m 14 tg_return_body_m)

theorem tg_return_node0_closed_l : tg_return_node0_m.FreeClosed := by
  apply (rt_exists_closed_l _).mpr
  apply (rt_exists_closed_l _).mpr
  refine ⟨by simp -implicitDefEqProofs, ?_⟩
  exact ⟨rt_tuple_closed_l _ _ (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) rfl,
    by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]⟩

set_option maxRecDepth 4096 in
theorem tg_return_node0_sat_l (hE : Extensional M) (ρ : Env M 11) :
    Formula.satisfies ρ tg_return_node0_m ↔ Tg_return_node_d (ρ.bound 0) (ρ.bound 1) (ρ.bound 2)
      (ρ.bound 3) (ρ.bound 4) (ρ.bound 5) (ρ.bound 6) (ρ.bound 7) (ρ.bound 8) (ρ.bound 9) (ρ.bound 10) := by
  have read (v : Fin 54 → M.Domain) (u : Fin 14 → M.Domain) :
      Formula.satisfies (rt_push_d (rt_push_d ρ 54 v) 14 u) tg_return_body_m ↔
        Tg_past_at_d (ρ.bound 1) (ρ.bound 4) (ρ.bound 5) (u 0) (u 1) (u 2) (u 3) (u 4) (u 5) (u 6) (u 7) (u 8) ∧
        Tg_saved_code_d (ρ.bound 0) (u 7) (u 8) v ∧ ρ.bound 6 = v 22 ∧
        Rd_entry_d (u 9) (v 19) (ρ.bound 2) ∧ Rd_entry_d (u 10) (v 40) (ρ.bound 2) ∧
        Rd_entry_d (u 11) (v 41) (ρ.bound 2) ∧ Rd_entry_d (u 12) (v 42) (ρ.bound 2) ∧
        Rd_entry_d (ρ.bound 5) (u 13) (ρ.bound 3) ∧ Rd_entry_d (u 9) (ρ.bound 7) (u 13) ∧
        Rd_entry_d (u 10) (ρ.bound 8) (u 13) ∧ Rd_entry_d (u 11) (ρ.bound 9) (u 13) ∧ Rd_entry_d (u 12) (ρ.bound 10) (u 13) := by
    simp only [tg_return_body_m, Formula.satisfies_conj_iff, tg_past_at_sat_l hE, rt_tuple_sat_l hE,
      Formula.satisfies_extensionalEq_iff_eq hE, rd_entry0_sat_l hE, Term.eval_bound]
    rfl
  rw [tg_return_node0_m, rt_exists_sat_l]
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨u, hu⟩ := (rt_exists_sat_l ..).mp hv
    obtain ⟨row, code, num, facts⟩ := (read v u).mp hu
    exact ⟨u 0, u 1, u 2, u 3, u 4, u 5, u 6, u 7, u 8, v, row, code, num, u 9, u 10, u 11, u 12, u 13, facts⟩
  · rintro ⟨Y, R, μ, K, η, C, L, V, q, v, row, code, num, a, b, c, d, j, facts⟩
    let u : Fin 14 → M.Domain := fun i => [Y, R, μ, K, η, C, L, V, q, a, b, c, d, j].get i
    exact ⟨v, (rt_exists_sat_l ..).mpr ⟨u, (read v u).mpr ⟨row, code, num, facts⟩⟩⟩

def tg_return_node_m {d} (ω H π P m i n S s t g : Term d) : Formula 1 d :=
  tg_return_node0_m.bind (fun j => [ω,H,π,P,m,i,n,S,s,t,g].get j)

@[simp] theorem tg_return_node_closed_l {d} (v : Fin 11 → Term d) (hv : ∀ i, (v i).freeSupport = []) :
    (tg_return_node0_m.bind v).FreeClosed := (Definitional.Formula.freeClosed_bind_iff_of_closed _ hv _).mpr tg_return_node0_closed_l

theorem tg_return_node_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω H π P m i n S s t g : Term d) :
    Formula.satisfies ρ (tg_return_node_m ω H π P m i n S s t g) ↔
      Tg_return_node_d (ω.eval ρ) (H.eval ρ) (π.eval ρ) (P.eval ρ) (m.eval ρ) (i.eval ρ)
        (n.eval ρ) (S.eval ρ) (s.eval ρ) (t.eval ρ) (g.eval ρ) := by
  rw [tg_return_node_m, Formula.satisfies_bind, tg_return_node0_sat_l hE]; rfl

end YesMetaZFC.SetTheory.LargeCardinal
