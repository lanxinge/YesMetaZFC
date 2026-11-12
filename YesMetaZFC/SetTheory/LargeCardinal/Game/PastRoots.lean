import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedNode
import YesMetaZFC.SetTheory.LargeCardinal.Game.Basis

/-! # 历史行的共同根图与固定低层

每行保留其反射层来自同一根的实际图，并记录旧回答域高于固定锚点。
旧根图随树的真正扩张保留；新行使用产生该行的奇数结点根图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_saved_high_d (Y R ω V q γ : M.Domain) : Prop :=
  ∃ v : Fin 54 → M.Domain, Tg_saved_code_d Y R ω V q v ∧ M.MemberSubset γ (v 15)

def tg_saved_high0_m : Formula 1 6 := rt_exists_m 54 (.conj
  (tg_saved_code_m (.bound 54) (.bound 55) (.bound 56) (.bound 57) (.bound 58)
    (fun i : Fin 54 => .bound (i.castAdd 6)))
  (Formula.subset (.bound 59) (.bound 15)))

theorem tg_saved_high0_closed_l : tg_saved_high0_m.FreeClosed := by
  apply (rt_exists_closed_l _).mpr
  refine ⟨tg_saved_code_closed_l _ _ _ _ _ _ rfl rfl rfl rfl rfl (fun _ => rfl), ?_⟩
  exact Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))

theorem tg_saved_high0_sat_l (ρ : Env M 6) :
    Formula.satisfies ρ tg_saved_high0_m ↔ Tg_saved_high_d (ρ.bound 0) (ρ.bound 1) (ρ.bound 2) (ρ.bound 3) (ρ.bound 4) (ρ.bound 5) := by
  rw [tg_saved_high0_m, rt_exists_sat_l]
  apply exists_congr
  intro v
  simp only [Formula.satisfies_conj_iff, tg_saved_code_sat_l, Formula.satisfies_subset_iff, Term.eval_bound]
  have tuple : (fun i : Fin 54 => (rt_push_d ρ 54 v).bound (i.castAdd 6)) = v := funext (rt_push_new_l ρ v)
  rw [tuple]
  have o0 : (rt_push_d ρ 54 v).bound 54 = ρ.bound 0 := rt_push_old_l ρ v 0
  have o1 : (rt_push_d ρ 54 v).bound 55 = ρ.bound 1 := rt_push_old_l ρ v 1
  have o2 : (rt_push_d ρ 54 v).bound 56 = ρ.bound 2 := rt_push_old_l ρ v 2
  have o3 : (rt_push_d ρ 54 v).bound 57 = ρ.bound 3 := rt_push_old_l ρ v 3
  have o4 : (rt_push_d ρ 54 v).bound 58 = ρ.bound 4 := rt_push_old_l ρ v 4
  have o5 : (rt_push_d ρ 54 v).bound 59 = ρ.bound 5 := rt_push_old_l ρ v 5
  have n15 : (rt_push_d ρ 54 v).bound 15 = v 15 := rt_push_new_l ρ v 15
  simp only [o0, o1, o2, o3, o4, o5, n15]
  rfl

def tg_saved_high_m {d} (Y R ω V q γ : Term d) : Formula 1 d :=
  tg_saved_high0_m.bind (fun i => [Y,R,ω,V,q,γ].get i)

@[simp] theorem tg_saved_high_closed_l {d} (Y R ω V q γ : Term d)
    (hY : Y.freeSupport = []) (hR : R.freeSupport = []) (hω : ω.freeSupport = []) (hV : V.freeSupport = []) (hq : q.freeSupport = []) (hγ : γ.freeSupport = []) : (tg_saved_high_m Y R ω V q γ).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _ (Fin.cases hY (Fin.cases hR (Fin.cases hω (Fin.cases hV (Fin.cases hq (Fin.cases hγ (fun i => Fin.elim0 i))))))) _).mpr tg_saved_high0_closed_l

theorem tg_saved_high_sat_l {d} (ρ : Env M d) (Y R ω V q γ : Term d) :
    Formula.satisfies ρ (tg_saved_high_m Y R ω V q γ) ↔ Tg_saved_high_d (Y.eval ρ) (R.eval ρ) (ω.eval ρ) (V.eval ρ) (q.eval ρ) (γ.eval ρ) := by
  rw [tg_saved_high_m, Formula.satisfies_bind, tg_saved_high0_sat_l]
  rfl

variable (I : kpair_convention_l.Interpretation M)

def Tg_past_roots_d (ω H G o Cᵣ γ Z : M.Domain) : Prop := ∀ m i Y R μ K η C L V q,
  Tg_past_at_d H m i Y R μ K η C L V q →
    (∃ π, It_map_d G o i π ∧ Rd_entry_d Cᵣ C π ∧ Tg_anchor_d I γ Z Y R π) ∧ Tg_saved_high_d Y R ω V q γ

def tg_past_roots_m {d} (ω H G o Cᵣ γ Z : Term d) : Formula 1 d := set[d] ⟪
  ∀ m i Y R μ K η C L V q, ⌜tg_past_at_m⌝ₚ(⌜H⌝ₛ, m, i, Y, R, μ, K, η, C, L, V, q) →
    (∃ π, ⌜it_map_m⌝ₚ(⌜G⌝ₛ, ⌜o⌝ₛ, i, π) ∧ ⌜rd_entry0_m⌝ₚ(⌜Cᵣ⌝ₛ, C, π) ∧
      ⌜tg_anchor_m⌝ₚ(⌜γ⌝ₛ, ⌜Z⌝ₛ, Y, R, π)) ∧ ⌜tg_saved_high_m⌝ₚ(Y, R, ⌜ω⌝ₛ, V, q, ⌜γ⌝ₛ)⟫
derive_free_closed tg_past_roots_m

theorem tg_past_roots_sat_l (ext : Extensional M) {d} (ρ : Env M d) (ω H G o Cᵣ γ Z : Term d) :
    Formula.satisfies ρ (tg_past_roots_m ω H G o Cᵣ γ Z) ↔
      Tg_past_roots_d I (ω.eval ρ) (H.eval ρ) (G.eval ρ) (o.eval ρ) (Cᵣ.eval ρ) (γ.eval ρ) (Z.eval ρ) := by
  simp only [tg_past_roots_m, Tg_past_roots_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, tg_past_at_sat_l ext, it_map_sat_l ext,
    rd_entry0_sat_l ext, tg_anchor_sat_l I ext, tg_saved_high_sat_l, Definitional.Term.eval_weaken]
  rfl

theorem tg_past_roots_empty_l {ω H G o Cᵣ γ Z : M.Domain} (empty : ∀ x, ¬ M.mem x H) :
    Tg_past_roots_d I ω H G o Cᵣ γ Z :=
  fun _ _ _ _ _ _ _ _ _ _ _ ⟨_, ⟨p, _, hp⟩, _⟩ => (empty p hp).elim

theorem Tg_past_roots_d.extend_l {ω H G G' o Cᵣ γ Z : M.Domain} (roots : Tg_past_roots_d I ω H G o Cᵣ γ Z)
    (keep : ∀ i π, It_map_d G o i π → It_map_d G' o i π) : Tg_past_roots_d I ω H G' o Cᵣ γ Z := by
  intro m i Y R μ K η C L V q row
  obtain ⟨⟨π, edge, image, anchor⟩, high⟩ := roots m i Y R μ K η C L V q row
  exact ⟨⟨π, keep i π edge, image, anchor⟩, high⟩

variable (hZF : M.Models ZF)

/-- 实际追加的同一行保存它的根图和回答域下界。 -/
theorem Tg_past_roots_d.push_l {ω n H n' H' X b G o Cᵣ γ Z i Y R μ K η C L V q π : M.Domain}
    (updated : Tg_past_d hZF ω n' H' X b) (succ : M.SuccessorOf n' n)
    (newest : Tg_past_at_d H' n i Y R μ K η C L V q)
    (entries : ∀ m r, M.mem m n → (Rd_entry_d m r H' ↔ Rd_entry_d m r H))
    (roots : Tg_past_roots_d I ω H G o Cᵣ γ Z)
    (edge : It_map_d G o i π) (image : Rd_entry_d Cᵣ C π) (anchor : Tg_anchor_d I γ Z Y R π)
    (high : Tg_saved_high_d Y R ω V q γ) : Tg_past_roots_d I ω H' G o Cᵣ γ Z := by
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
    have eR : R₀ = R := congrFun eq 2
    have eC : C₀ = C := congrFun eq 6; have eV : V₀ = V := congrFun eq 8; have eq' : q₀ = q := congrFun eq 9
    subst i₀ Y₀ R₀ C₀ V₀ q₀
    exact ⟨⟨π, edge, image, anchor⟩, high⟩

end YesMetaZFC.SetTheory.LargeCardinal
