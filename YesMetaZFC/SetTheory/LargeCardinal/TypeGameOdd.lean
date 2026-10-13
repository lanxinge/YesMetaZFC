import YesMetaZFC.SetTheory.LargeCardinal.TypeGamePast

/-! # 同一存档的树、长度及恢复图

奇数边必须连接原请求选中的历史行。三个坐标都从同一完整记录读取；
恢复图是旧图的实际嵌入像再添一个点，重置则保留真实的空图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_saved_branch_d (ω V q S n g : M.Domain) : Prop :=
  ∃ v : Fin 54 → M.Domain, Tg_saved_code_d ω V q v ∧ v 19 = S ∧ v 22 = n ∧ v 42 = g

def tg_saved_branch0_m : Formula 1 6 := rt_exists_m 54 (.conj
  (rt_tuple_m (Fin.cases (.bound 54) (Fin.cases (.bound 55) (fun i : Fin 54 => .bound (i.castAdd 6)))) (.bound 56))
  (set[60] ⟪⌜(.bound 19 : Term 60)⌝ₛ = ⌜(.bound 57 : Term 60)⌝ₛ ∧
    ⌜(.bound 22 : Term 60)⌝ₛ = ⌜(.bound 58 : Term 60)⌝ₛ ∧ ⌜(.bound 42 : Term 60)⌝ₛ = ⌜(.bound 59 : Term 60)⌝ₛ⟫))

theorem tg_saved_branch0_closed_l : tg_saved_branch0_m.FreeClosed := by
  apply (rt_exists_closed_l _).mpr
  refine ⟨rt_tuple_closed_l _ _ (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) rfl, ?_⟩
  simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]

theorem tg_saved_branch0_sat_l (hE : Extensional M) (ρ : Env M 6) :
    Formula.satisfies ρ tg_saved_branch0_m ↔
      Tg_saved_branch_d (ρ.bound 0) (ρ.bound 1) (ρ.bound 2) (ρ.bound 3) (ρ.bound 4) (ρ.bound 5) := by
  rw [tg_saved_branch0_m, rt_exists_sat_l]
  apply exists_congr
  intro v
  simp only [Formula.satisfies_conj_iff, rt_tuple_sat_l hE, Formula.satisfies_extensionalEq_iff_eq hE]
  have new (i : Fin 54) : (rt_push_d ρ 54 v).bound (i.castAdd 6) = v i := rt_push_new_l ρ v i
  have old (i : Fin 6) : (rt_push_d ρ 54 v).bound (Fin.natAdd 54 i) = ρ.bound i := rt_push_old_l ρ v i
  have tuple : (fun i : Fin 56 =>
      ((Fin.cases (.bound 54) (Fin.cases (.bound 55) (fun j : Fin 54 => .bound (j.castAdd 6))) i : Term 60).eval
        (rt_push_d ρ 54 v))) = Fin.cases (ρ.bound 0) (Fin.cases (ρ.bound 1) v) := by
    funext i
    exact Fin.cases (old 0) (Fin.cases (old 1) new) i
  rw [tuple]
  change (Tg_saved_code_d (ρ.bound 0) (ρ.bound 1) ((rt_push_d ρ 54 v).bound 56) v ∧
    (rt_push_d ρ 54 v).bound 19 = (rt_push_d ρ 54 v).bound 57 ∧
    (rt_push_d ρ 54 v).bound 22 = (rt_push_d ρ 54 v).bound 58 ∧
    (rt_push_d ρ 54 v).bound 42 = (rt_push_d ρ 54 v).bound 59) ↔ _
  rw [show (rt_push_d ρ 54 v).bound 56 = ρ.bound 2 from old 2,
    show (rt_push_d ρ 54 v).bound 57 = ρ.bound 3 from old 3,
    show (rt_push_d ρ 54 v).bound 58 = ρ.bound 4 from old 4,
    show (rt_push_d ρ 54 v).bound 59 = ρ.bound 5 from old 5,
    show (rt_push_d ρ 54 v).bound 19 = v 19 from new 19,
    show (rt_push_d ρ 54 v).bound 22 = v 22 from new 22,
    show (rt_push_d ρ 54 v).bound 42 = v 42 from new 42]

def tg_saved_branch_m {d} (ω V q S n g : Term d) : Formula 1 d :=
  tg_saved_branch0_m.bind (fun i => [ω,V,q,S,n,g].get i)

@[simp] theorem tg_saved_branch_closed_l {d} (ω V q S n g : Term d)
    (hw : ω.freeSupport = []) (hV : V.freeSupport = []) (hq : q.freeSupport = [])
    (hS : S.freeSupport = []) (hn : n.freeSupport = []) (hg : g.freeSupport = []) :
    (tg_saved_branch_m ω V q S n g).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _
    (Fin.cases hw (Fin.cases hV (Fin.cases hq (Fin.cases hS (Fin.cases hn (Fin.cases hg (fun i => Fin.elim0 i))))))) _).mpr
    tg_saved_branch0_closed_l

theorem tg_saved_branch_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω V q S n g : Term d) :
    Formula.satisfies ρ (tg_saved_branch_m ω V q S n g) ↔
      Tg_saved_branch_d (ω.eval ρ) (V.eval ρ) (q.eval ρ) (S.eval ρ) (n.eval ρ) (g.eval ρ) := by
  rw [tg_saved_branch_m, Formula.satisfies_bind, tg_saved_branch0_sat_l hE]
  rfl

def Tg_odd_d (ω H ξ α k G e t ℓ S n g : M.Domain) : Prop :=
  (t = e ∧ k = ξ ∧ g = e) ∨
  (t ≠ e ∧ ∃ Y R μ K η C L V q S₀ n₀ g₀ j a b z,
    Tg_past_at_d H ℓ k Y R μ K η C L V q ∧ Tg_saved_branch_d ω V q S₀ n₀ g₀ ∧
    It_map_d G k α j ∧ Rd_entry_d S₀ S j ∧ Rd_entry_d n₀ b j ∧ Rd_entry_d g₀ a j ∧
    M.SuccessorOf n b ∧ Rd_entry_d b z g ∧ ∀ p, M.mem p g ↔ M.mem p a ∨ KPair_d M p b z)

def tg_odd_m {d} (ω H ξ α k G e t ℓ S n g : Term d) : Formula 1 d := set[d] ⟪
  (⌜t⌝ₛ = ⌜e⌝ₛ ∧ ⌜k⌝ₛ = ⌜ξ⌝ₛ ∧ ⌜g⌝ₛ = ⌜e⌝ₛ) ∨
  (¬ (⌜t⌝ₛ = ⌜e⌝ₛ) ∧ (∃ Y R μ K η C L V q S₀ n₀ g₀ j a b z,
    ⌜tg_past_at_m⌝ₚ(⌜H⌝ₛ, ⌜ℓ⌝ₛ, ⌜k⌝ₛ, Y, R, μ, K, η, C, L, V, q) ∧
    ⌜tg_saved_branch_m⌝ₚ(⌜ω⌝ₛ, V, q, S₀, n₀, g₀) ∧ ⌜it_map_m⌝ₚ(⌜G⌝ₛ, ⌜k⌝ₛ, ⌜α⌝ₛ, j) ∧
    ⌜rd_entry0_m⌝ₚ(S₀, ⌜S⌝ₛ, j) ∧ ⌜rd_entry0_m⌝ₚ(n₀, b, j) ∧ ⌜rd_entry0_m⌝ₚ(g₀, a, j) ∧
    ⌜KP.succ0_m⌝ₚ(⌜n⌝ₛ, b) ∧ ⌜rd_entry0_m⌝ₚ(b, z, ⌜g⌝ₛ) ∧
    (∀ p, p ∈ ⌜g⌝ₛ ↔ p ∈ a ∨ ⌜kpair0_m⌝ₚ(p, b, z))))⟫
derive_free_closed tg_odd_m

theorem tg_odd_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω H ξ α k G e t ℓ S n g : Term d) :
    Formula.satisfies ρ (tg_odd_m ω H ξ α k G e t ℓ S n g) ↔
      Tg_odd_d (ω.eval ρ) (H.eval ρ) (ξ.eval ρ) (α.eval ρ) (k.eval ρ) (G.eval ρ)
        (e.eval ρ) (t.eval ρ) (ℓ.eval ρ) (S.eval ρ) (n.eval ρ) (g.eval ρ) := by
  simp only [tg_odd_m, Tg_odd_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_exists_iff,
    tg_past_at_sat_l hE, tg_saved_branch_sat_l hE, it_map_sat_l hE, rd_entry0_sat_l hE,
    KP.succ0_sat_l hE, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, kpair0_sat_l hE, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal
