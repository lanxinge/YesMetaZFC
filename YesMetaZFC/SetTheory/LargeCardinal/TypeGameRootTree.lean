import YesMetaZFC.SetTheory.LargeCardinal.TypeGameOdd

/-! # 各存档中的树都是同一原树的根嵌入像

树名沿真实根图保存。重置使用恒等边上的实际条目，继续使用被选旧行的
原树像；两种情形都由图表复合律给出新行的树名。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_root_tree_d (ω H G o S₀ : M.Domain) : Prop := ∀ m i Y R μ K η C L V q S n s t g,
  Tg_past_at_d H m i Y R μ K η C L V q → Tg_saved_branch_d ω V q S n s t g →
    ∃ j, It_map_d G o i j ∧ Rd_entry_d S₀ S j

def tg_root_tree_m {d} (ω H G o S₀ : Term d) : Formula 1 d := set[d] ⟪∀ m i Y R μ K η C L V q S n s t g,
  ⌜tg_past_at_m⌝ₚ(⌜H⌝ₛ, m, i, Y, R, μ, K, η, C, L, V, q) →
  ⌜tg_saved_branch_m⌝ₚ(⌜ω⌝ₛ, V, q, S, n, s, t, g) →
  (∃ j, ⌜it_map_m⌝ₚ(⌜G⌝ₛ, ⌜o⌝ₛ, i, j) ∧ ⌜rd_entry0_m⌝ₚ(⌜S₀⌝ₛ, S, j))⟫
derive_free_closed tg_root_tree_m

theorem tg_root_tree_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω H G o S₀ : Term d) :
    Formula.satisfies ρ (tg_root_tree_m ω H G o S₀) ↔
      Tg_root_tree_d (ω.eval ρ) (H.eval ρ) (G.eval ρ) (o.eval ρ) (S₀.eval ρ) := by
  simp only [tg_root_tree_m, Tg_root_tree_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, tg_past_at_sat_l hE,
    tg_saved_branch_sat_l hE, it_map_sat_l hE, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]; rfl

def Tg_common_tree_d (ω H G o π S : M.Domain) : Prop :=
  ∃ S₀, Rd_entry_d S₀ S π ∧ Tg_root_tree_d ω H G o S₀

def tg_common_tree_m {d} (ω H G o π S : Term d) : Formula 1 d := set[d] ⟪∃ S₀,
  ⌜rd_entry0_m⌝ₚ(S₀, ⌜S⌝ₛ, ⌜π⌝ₛ) ∧ ⌜tg_root_tree_m⌝ₚ(⌜ω⌝ₛ, ⌜H⌝ₛ, ⌜G⌝ₛ, ⌜o⌝ₛ, S₀)⟫
derive_free_closed tg_common_tree_m

theorem tg_common_tree_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω H G o π S : Term d) :
    Formula.satisfies ρ (tg_common_tree_m ω H G o π S) ↔
      Tg_common_tree_d (ω.eval ρ) (H.eval ρ) (G.eval ρ) (o.eval ρ) (π.eval ρ) (S.eval ρ) := by
  simp only [tg_common_tree_m, Tg_common_tree_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE, tg_root_tree_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem Tg_saved_branch_d.tree_unique_l {ω V q S n s t g S' n' s' t' g' : M.Domain}
    (h : Tg_saved_branch_d ω V q S n s t g) (h' : Tg_saved_branch_d ω V q S' n' s' t' g') : S = S' := by
  obtain ⟨v, code, hs, _⟩ := h
  obtain ⟨w, pack, hs', _⟩ := h'
  exact hs.symm.trans ((congrFun (rt_tuple_inj_l code pack) 21).trans hs')

theorem tg_root_tree_empty_l {ω H G o S : M.Domain} (empty : ∀ x, ¬ M.mem x H) : Tg_root_tree_d ω H G o S :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨_, ⟨p, _, hp⟩, _⟩ _ => (empty p hp).elim

theorem Tg_root_tree_d.extend_l {ω H G G' o S : M.Domain} (h : Tg_root_tree_d ω H G o S)
    (keep : ∀ i j, It_map_d G o i j → It_map_d G' o i j) : Tg_root_tree_d ω H G' o S := by
  intro m i Y R μ K η C L V q S' n a b g row br
  obtain ⟨j, hj, image⟩ := h m i Y R μ K η C L V q S' n a b g row br
  exact ⟨j, keep i j hj, image⟩

variable (hZF : M.Models ZF)

theorem Tg_root_tree_d.push_l {ω n H n' H' X b G o S₀ i Y R μ K η C L V q S k s t g j : M.Domain}
    (past : Tg_past_d hZF ω n' H' X b) (succ : M.SuccessorOf n' n)
    (newest : Tg_past_at_d H' n i Y R μ K η C L V q)
    (entries : ∀ m r, M.mem m n → (Rd_entry_d m r H' ↔ Rd_entry_d m r H))
    (old : Tg_root_tree_d ω H G o S₀) (br : Tg_saved_branch_d ω V q S k s t g)
    (root : It_map_d G o i j) (image : Rd_entry_d S₀ S j) : Tg_root_tree_d ω H' G o S₀ := by
  intro m i' Y' R' μ' K' η' C' L' V' q' S' k' a' b' g' row branch
  obtain ⟨r, hr, cell⟩ := row
  rcases (succ m).mp ((past.sequence.2.2 m).mpr ⟨r, hr⟩) with lt | eq
  · exact old m i' Y' R' μ' K' η' C' L' V' q' S' k' a' b' g' ⟨r, (entries m r lt).mp hr, cell⟩ branch
  · have eq := hZF.1.eq_of_same_members m n eq
    subst m
    obtain ⟨s, hs, pack⟩ := newest
    have eq := past.sequence.2.1.2 n s r hs hr
    subst s
    have eq := rt_tuple_inj_l cell pack
    have ei : i' = i := congrFun eq 0
    have eV : V' = V := congrFun eq 8
    have eq : q' = q := congrFun eq 9
    subst i' V' q'
    exact ⟨j, root, (branch.tree_unique_l br).symm ▸ image⟩

theorem Tg_root_tree_d.odd_l {ω H G G' o S₀ Sₑ S n s g ξ α k e t ℓ π π' β T Q : M.Domain}
    (h : Tg_root_tree_d ω H G o S₀) (keep : ∀ i j, It_map_d G o i j → It_map_d G' o i j)
    (diagram : It_diagram_d hZF ω β T Q G') (old : It_map_d G' o ξ π) (image : Rd_entry_d S₀ Sₑ π)
    (root : It_map_d G' o α π') (odd : Tg_odd_d ω H ξ α k G' e t ℓ Sₑ S n s g) : Rd_entry_d S₀ S π' := by
  rcases odd with ⟨_, _, _, j, edge, value⟩ | ⟨_, Y, R, μ, K, η, C, L, V, q, S', n', s', t', g', j, _, _, _, row, br, edge, value, _⟩
  · exact diagram.comp o ξ α π j π' old edge root S₀ Sₑ S image value
  · obtain ⟨r, hr, hs⟩ := h ℓ k Y R μ K η C L V q S' n' s' t' g' row br
    exact diagram.comp o k α r j π' (keep k r hr) edge root S₀ S' S hs value

end YesMetaZFC.SetTheory.LargeCardinal
