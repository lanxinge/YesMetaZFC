import YesMetaZFC.SetTheory.LargeCardinal.TypeGamePast
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameAnchor

/-! # 历史行的共同根图与固定低层

每行保留其反射层来自同一根的实际图，并记录旧回答域高于固定锚点。
旧根图随树的真正扩张保留；新行使用产生该行的奇数结点根图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_saved_high_d (ω V q γ : M.Domain) : Prop :=
  ∃ v : Fin 54 → M.Domain, Tg_saved_code_d ω V q v ∧ M.MemberSubset γ (v 15)

def tg_saved_high0_m : Formula 1 4 := rt_exists_m 54 (.conj
  (rt_tuple_m (Fin.cases (.bound 54) (Fin.cases (.bound 55) (fun i : Fin 54 => .bound (i.castAdd 4)))) (.bound 56))
  (Formula.subset (.bound 57) (.bound 15)))

theorem tg_saved_high0_closed_l : tg_saved_high0_m.FreeClosed := by
  apply (rt_exists_closed_l _).mpr
  exact ⟨rt_tuple_closed_l _ _ (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) rfl,
    Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))⟩

def tg_saved_high_m {d} (ω V q γ : Term d) : Formula 1 d :=
  tg_saved_high0_m.bind (fun i => [ω, V, q, γ].get i)

@[simp] theorem tg_saved_high_closed_l {d} (ω V q γ : Term d)
    (hw : ω.freeSupport = []) (hV : V.freeSupport = []) (hq : q.freeSupport = []) (hγ : γ.freeSupport = []) :
    (tg_saved_high_m ω V q γ).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _
    (Fin.cases hw (Fin.cases hV (Fin.cases hq (Fin.cases hγ (fun i => Fin.elim0 i))))) _).mpr tg_saved_high0_closed_l

theorem tg_saved_high0_sat_l (hE : Extensional M) (ρ : Env M 4) :
    Formula.satisfies ρ tg_saved_high0_m ↔ Tg_saved_high_d (ρ.bound 0) (ρ.bound 1) (ρ.bound 2) (ρ.bound 3) := by
  rw [tg_saved_high0_m, rt_exists_sat_l]
  apply exists_congr
  intro v
  rw [Formula.satisfies_conj_iff, rt_tuple_sat_l hE, Formula.satisfies_subset_iff]
  have tuple : (fun i : Fin 56 =>
      ((Fin.cases (.bound 54) (Fin.cases (.bound 55) (fun j : Fin 54 => .bound (j.castAdd 4))) i : Term 58).eval
        (rt_push_d ρ 54 v))) = Fin.cases (ρ.bound 0) (Fin.cases (ρ.bound 1) v) := by
    funext i
    exact Fin.cases (rt_push_old_l ρ v 0) (Fin.cases (rt_push_old_l ρ v 1) (rt_push_new_l ρ v)) i
  have eq : (rt_push_d ρ 54 v).bound 56 = ρ.bound 2 := rt_push_old_l ρ v 2
  have eg : (rt_push_d ρ 54 v).bound 57 = ρ.bound 3 := rt_push_old_l ρ v 3
  have et : (rt_push_d ρ 54 v).bound 15 = v 15 := rt_push_new_l ρ v 15
  rw [tuple]
  change (Tg_saved_code_d (ρ.bound 0) (ρ.bound 1) ((rt_push_d ρ 54 v).bound 56) v ∧
    M.MemberSubset ((rt_push_d ρ 54 v).bound 57) ((rt_push_d ρ 54 v).bound 15)) ↔ _
  rw [eq, eg, et]

theorem tg_saved_high_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω V q γ : Term d) :
    Formula.satisfies ρ (tg_saved_high_m ω V q γ) ↔ Tg_saved_high_d (ω.eval ρ) (V.eval ρ) (q.eval ρ) (γ.eval ρ) := by
  rw [tg_saved_high_m, Formula.satisfies_bind, tg_saved_high0_sat_l hE]
  rfl

def tg_anchor_m {d} (γ Z Y π : Term d) : Formula 1 d := set[d] ⟪
  ⌜γ⌝ₛ ∈ ⌜Y⌝ₛ ∧ ⌜Z⌝ₛ ∈ ⌜Y⌝ₛ ∧ ⌜pn_rank_m⌝ₚ(⌜Y⌝ₛ, ⌜γ⌝ₛ, ⌜Z⌝ₛ) ∧
  (∀ x ∈ ⌜Z⌝ₛ, ⌜rd_entry0_m⌝ₚ(x, x, ⌜π⌝ₛ))⟫
derive_free_closed tg_anchor_m

theorem tg_anchor_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (γ Z Y π : Term d) :
    Formula.satisfies ρ (tg_anchor_m γ Z Y π) ↔ Tg_anchor_d (γ.eval ρ) (Z.eval ρ) (Y.eval ρ) (π.eval ρ) := by
  simp only [tg_anchor_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, pn_rank_sat_l hKP,
    Formula.satisfies_forallMem_iff, rd_entry0_sat_l hKP.1, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun h => ⟨h.height, h.member, h.rank, h.fixed⟩⟩

def Tg_past_roots_d (ω H G o Cᵣ γ Z : M.Domain) : Prop := ∀ m i Y R μ K η C L V q,
  Tg_past_at_d H m i Y R μ K η C L V q →
    (∃ π, It_map_d G o i π ∧ Rd_entry_d Cᵣ C π ∧ Tg_anchor_d γ Z Y π) ∧ Tg_saved_high_d ω V q γ

def tg_past_roots_m {d} (ω H G o Cᵣ γ Z : Term d) : Formula 1 d := set[d] ⟪
  ∀ m i Y R μ K η C L V q, ⌜tg_past_at_m⌝ₚ(⌜H⌝ₛ, m, i, Y, R, μ, K, η, C, L, V, q) →
    (∃ π, ⌜it_map_m⌝ₚ(⌜G⌝ₛ, ⌜o⌝ₛ, i, π) ∧ ⌜rd_entry0_m⌝ₚ(⌜Cᵣ⌝ₛ, C, π) ∧
      ⌜tg_anchor_m⌝ₚ(⌜γ⌝ₛ, ⌜Z⌝ₛ, Y, π)) ∧ ⌜tg_saved_high_m⌝ₚ(⌜ω⌝ₛ, V, q, ⌜γ⌝ₛ)⟫
derive_free_closed tg_past_roots_m

theorem tg_past_roots_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω H G o Cᵣ γ Z : Term d) :
    Formula.satisfies ρ (tg_past_roots_m ω H G o Cᵣ γ Z) ↔
      Tg_past_roots_d (ω.eval ρ) (H.eval ρ) (G.eval ρ) (o.eval ρ) (Cᵣ.eval ρ) (γ.eval ρ) (Z.eval ρ) := by
  simp only [tg_past_roots_m, Tg_past_roots_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, tg_past_at_sat_l hKP.1, it_map_sat_l hKP.1,
    rd_entry0_sat_l hKP.1, tg_anchor_sat_l hKP, tg_saved_high_sat_l hKP.1, Definitional.Term.eval_weaken]
  rfl

theorem tg_past_roots_empty_l {ω H G o Cᵣ γ Z : M.Domain} (empty : ∀ x, ¬ M.mem x H) :
    Tg_past_roots_d ω H G o Cᵣ γ Z :=
  fun _ _ _ _ _ _ _ _ _ _ _ ⟨_, ⟨p, _, hp⟩, _⟩ => (empty p hp).elim

theorem Tg_past_roots_d.extend_l {ω H G G' o Cᵣ γ Z : M.Domain} (roots : Tg_past_roots_d ω H G o Cᵣ γ Z)
    (keep : ∀ i π, It_map_d G o i π → It_map_d G' o i π) : Tg_past_roots_d ω H G' o Cᵣ γ Z := by
  intro m i Y R μ K η C L V q row
  obtain ⟨⟨π, edge, image, anchor⟩, high⟩ := roots m i Y R μ K η C L V q row
  exact ⟨⟨π, keep i π edge, image, anchor⟩, high⟩

variable (hZF : M.Models ZF)

/-- 实际追加的同一行保存它的根图和回答域下界。 -/
theorem Tg_past_roots_d.push_l {ω n H n' H' X b G o Cᵣ γ Z i Y R μ K η C L V q π : M.Domain}
    (updated : Tg_past_d hZF ω n' H' X b) (succ : M.SuccessorOf n' n)
    (newest : Tg_past_at_d H' n i Y R μ K η C L V q)
    (entries : ∀ m r, M.mem m n → (Rd_entry_d m r H' ↔ Rd_entry_d m r H))
    (roots : Tg_past_roots_d ω H G o Cᵣ γ Z)
    (edge : It_map_d G o i π) (image : Rd_entry_d Cᵣ C π) (anchor : Tg_anchor_d γ Z Y π)
    (high : Tg_saved_high_d ω V q γ) : Tg_past_roots_d ω H' G o Cᵣ γ Z := by
  intro m i₀ Y₀ R₀ μ₀ K₀ η₀ C₀ L₀ V₀ q₀ row
  obtain ⟨r, hr, cell⟩ := row
  rcases (succ m).mp ((updated.sequence.2.2 m).mpr ⟨r, hr⟩) with lt | eq
  · exact roots m i₀ Y₀ R₀ μ₀ K₀ η₀ C₀ L₀ V₀ q₀ ⟨r, (entries m r lt).mp hr, cell⟩
  · have eq := hZF.1.eq_of_same_members m n eq
    subst m
    obtain ⟨s, hs, cell'⟩ := newest
    have eq := updated.sequence.2.1.2 n r s hr hs
    subst s
    have eq := rt_tuple_inj_l cell cell'
    have ei : i₀ = i := congrFun eq 0; have eY : Y₀ = Y := congrFun eq 1
    have eC : C₀ = C := congrFun eq 6; have eV : V₀ = V := congrFun eq 8; have eq' : q₀ = q := congrFun eq 9
    subst i₀ Y₀ C₀ V₀ q₀
    exact ⟨⟨π, edge, image, anchor⟩, high⟩

end YesMetaZFC.SetTheory.LargeCardinal
