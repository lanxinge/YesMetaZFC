import YesMetaZFC.SetTheory.LargeCardinal.TypeGameGenericDense

/-! # 泛型稠密要求的原公式

请求保留实际实现高度与标签图，并对后续局面给出原规则的合法性。全部要求
均为原语言公式，因而可在地模型内分离，不把外部谓词冒充模型内稠密集。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_generic_target_d (p : Tg_params_d M.Domain) (ℓ s t k N β g a₀ b₀ κ C a u : M.Domain) : Prop :=
  M.mem κ p.δ ∧ V_d I κ C ∧ Tg_aux_data_d a ℓ t κ u ∧
  (∃ μ A d H m V P r, M.SuccessorOf μ β ∧ V_d I μ A ∧ Smem_d I d A H ∧ M.SuccessorOf m N ∧
    (∀ x, M.mem x V ↔ M.mem x C ∨ x = κ) ∧
    Tt_realized_d I p.ω d A H m r p.δ V P u ∧ Rd_entry_d p.e p.S r ∧ Rd_entry_d N β r ∧ Sg_set_d I p.e N r g) ∧
  ∀ n h z, Tg_digits_d hZF p.c p.b n p.A h z → M.IsRestrictionOf I s z k → M.mem ℓ n →
    Tg_event_d I p.c ℓ p.e h a₀ → Tg_event_d I p.c ℓ p.a h b₀ →
    Tg_growth_d hZF p.e p.c p.A n h κ C → Tg_aux_d hZF p n h a

def tg_generic_target0_m : Formula 1 25 :=
  let p : Tg_params_d (Term 25) := ⟨.bound 0, .bound 1, .bound 2, .bound 3, .bound 4, .bound 5,
    .bound 6, .bound 7, .bound 8, .bound 9, .bound 10, .bound 11⟩
  let v : Fin 25 → Term 25 := Term.bound
  let aux {d} (ω e a b c δ A S ν E P Q n h v : Term d) := tg_aux_m ⟨ω, e, a, b, c, δ, A, S, ν, E, P, Q⟩ n h v
  set[25] ⟪⌜v 21⌝ₛ ∈ ⌜p.δ⌝ₛ ∧ ⌜v_m kpair_convention_l⌝ₚ(⌜v 21⌝ₛ, ⌜v 22⌝ₛ) ∧
    ⌜tg_aux_data_m⌝ₚ(⌜v 23⌝ₛ, ⌜v 12⌝ₛ, ⌜v 14⌝ₛ, ⌜v 21⌝ₛ, ⌜v 24⌝ₛ) ∧
    (∃ μ A d H m V P r, ⌜Formula.isSuccessor⌝ₚ(μ, ⌜v 17⌝ₛ) ∧ ⌜v_m kpair_convention_l⌝ₚ(μ, A) ∧
      ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(d, A, H) ∧ ⌜Formula.isSuccessor⌝ₚ(m, ⌜v 16⌝ₛ) ∧
      ⌜tt_constants0_m⌝ₚ(⌜v 21⌝ₛ, ⌜v 22⌝ₛ, V) ∧ ⌜tt_realized_m⌝ₚ(⌜p.ω⌝ₛ, d, A, H, m, r, ⌜p.δ⌝ₛ, V, P, ⌜v 24⌝ₛ) ∧
      ⌜rd_entry0_m⌝ₚ(⌜p.e⌝ₛ, ⌜p.S⌝ₛ, r) ∧ ⌜rd_entry0_m⌝ₚ(⌜v 16⌝ₛ, ⌜v 17⌝ₛ, r) ∧
      ⌜sg_set_m (𝒞 := kpair_convention_l)⌝ₚ(⌜p.e⌝ₛ, ⌜v 16⌝ₛ, r, ⌜v 18⌝ₛ)) ∧
    (∀ n h z, ⌜tg_digits_m⌝ₚ(⌜p.c⌝ₛ, ⌜p.b⌝ₛ, n, ⌜p.A⌝ₛ, h, z) →
      ⌜Formula.isRestriction kpair_convention_l⌝ₚ(⌜v 13⌝ₛ, z, ⌜v 15⌝ₛ) → ⌜v 12⌝ₛ ∈ n →
      ⌜tg_event_m⌝ₚ(⌜p.c⌝ₛ, ⌜v 12⌝ₛ, ⌜p.e⌝ₛ, h, ⌜v 19⌝ₛ) →
      ⌜tg_event_m⌝ₚ(⌜p.c⌝ₛ, ⌜v 12⌝ₛ, ⌜p.a⌝ₛ, h, ⌜v 20⌝ₛ) →
      ⌜tg_growth_m⌝ₚ(⌜p.e⌝ₛ, ⌜p.c⌝ₛ, ⌜p.A⌝ₛ, n, h, ⌜v 21⌝ₛ, ⌜v 22⌝ₛ) →
      ⌜aux⌝ₚ(⌜p.ω⌝ₛ, ⌜p.e⌝ₛ, ⌜p.a⌝ₛ, ⌜p.b⌝ₛ, ⌜p.c⌝ₛ, ⌜p.δ⌝ₛ,
        ⌜p.A⌝ₛ, ⌜p.S⌝ₛ, ⌜p.ν⌝ₛ, ⌜p.E⌝ₛ, ⌜p.P⌝ₛ, ⌜p.Q⌝ₛ, n, h, ⌜v 23⌝ₛ))⟫

theorem tg_generic_target0_closed_l : tg_generic_target0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_generic_target0_m, Definitional.Formula.FreeClosed]
  exact tg_aux_closed_l _ _ _ _ (by simp -implicitDefEqProofs [Tg_params_d.closed_l]) rfl rfl rfl

def tg_generic_target_m {d} (p : Tg_params_d (Term d)) (ℓ s t k N β g a₀ b₀ κ C a u : Term d) : Formula 1 d :=
  tg_generic_target0_m.bind (fun i => [p.ω, p.e, p.a, p.b, p.c, p.δ, p.A, p.S, p.ν, p.E, p.P, p.Q,
    ℓ, s, t, k, N, β, g, a₀, b₀, κ, C, a, u].get i)

@[simp] theorem tg_generic_target_closed_l {d} (p : Tg_params_d (Term d)) (ℓ s t k N β g a₀ b₀ κ C a u : Term d)
    (hp : p.closed_l) (hℓ : ℓ.freeSupport = []) (hs : s.freeSupport = []) (ht : t.freeSupport = [])
    (hk : k.freeSupport = []) (hN : N.freeSupport = []) (hβ : β.freeSupport = []) (hg : g.freeSupport = [])
    (h₀ : a₀.freeSupport = []) (h₁ : b₀.freeSupport = []) (hκ : κ.freeSupport = []) (hC : C.freeSupport = [])
    (ha : a.freeSupport = []) (hu : u.freeSupport = []) : (tg_generic_target_m p ℓ s t k N β g a₀ b₀ κ C a u).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tg_generic_target0_closed_l
  rcases hp with ⟨hω, he, ha', hb, hc, hd, hA, hS, hν, hE, hP, hQ⟩
  simp only [Fin.forall_fin_succ]
  exact ⟨hω, he, ha', hb, hc, hd, hA, hS, hν, hE, hP, hQ,
    hℓ, hs, ht, hk, hN, hβ, hg, h₀, h₁, hκ, hC, ha, hu, fun i => Fin.elim0 i⟩

theorem tg_generic_target_sat_l {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (ℓ s t k N β g a₀ b₀ κ C a u : Term d) :
    Formula.satisfies ρ (tg_generic_target_m p ℓ s t k N β g a₀ b₀ κ C a u) ↔
      Tg_generic_target_d hZF (p.map_l (fun t => t.eval ρ)) (ℓ.eval ρ) (s.eval ρ) (t.eval ρ) (k.eval ρ)
        (N.eval ρ) (β.eval ρ) (g.eval ρ) (a₀.eval ρ) (b₀.eval ρ) (κ.eval ρ) (C.eval ρ) (a.eval ρ) (u.eval ρ) := by
  simp only [tg_generic_target_m, Formula.satisfies_bind, tg_generic_target0_m, Tg_generic_target_d,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, v_sat_l I hZF.1, tg_aux_data_sat_l hZF.1,
    Formula.satisfies_exists_iff, Formula.satisfies_isSuccessor_iff, smem_sat_l I, tt_constants0_sat_l hZF.1, tt_realized_sat_l I (ZF.modelsKP hZF),
    rd_entry0_sat_l hZF.1, sg_set_sat_l I hZF.1, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    tg_digits_sat_l hZF, Formula.satisfies_isRestriction_iff I, tg_event_sat_l I hZF.1, tg_growth_sat_l hZF,
    tg_aux_sat_l hZF, Definitional.Term.eval_weaken, Tg_params_d.map_l]
  rfl

def Tg_dense_hit_d (p : Tg_params_d M.Domain) (ℓ s t k N β g a₀ b₀ E q : M.Domain) : Prop :=
  ∃ κ C a u i, Tg_generic_target_d hZF p ℓ s t k N β g a₀ b₀ κ C a u ∧
    M.mem E i ∧ M.mem i p.ω ∧ Rd_entry_d i a q ∧ ∀ j y, M.mem j i → Rd_entry_d j y q → M.mem y C

def tg_dense_hit_m {d} (p : Tg_params_d (Term d)) (ℓ s t k N β g a₀ b₀ E q : Term d) : Formula 1 d :=
  .existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (tg_generic_target_m (p.map_l (fun t => t.weaken.weaken.weaken.weaken.weaken))
      ℓ.weaken.weaken.weaken.weaken.weaken s.weaken.weaken.weaken.weaken.weaken t.weaken.weaken.weaken.weaken.weaken
      k.weaken.weaken.weaken.weaken.weaken N.weaken.weaken.weaken.weaken.weaken β.weaken.weaken.weaken.weaken.weaken
      g.weaken.weaken.weaken.weaken.weaken a₀.weaken.weaken.weaken.weaken.weaken b₀.weaken.weaken.weaken.weaken.weaken
      (.bound 4) (.bound 3) (.bound 2) (.bound 1))
    (set[d+5] ⟪⌜E.weaken.weaken.weaken.weaken.weaken⌝ₛ ∈ ⌜(.bound 0 : Term (d+5))⌝ₛ ∧
      ⌜(.bound 0 : Term (d+5))⌝ₛ ∈ ⌜p.ω.weaken.weaken.weaken.weaken.weaken⌝ₛ ∧
      ⌜rd_entry0_m⌝ₚ(⌜(.bound 0 : Term (d+5))⌝ₛ, ⌜(.bound 2 : Term (d+5))⌝ₛ, ⌜q.weaken.weaken.weaken.weaken.weaken⌝ₛ) ∧
      (∀ j y, j ∈ ⌜(.bound 0 : Term (d+5))⌝ₛ →
        ⌜rd_entry0_m⌝ₚ(j, y, ⌜q.weaken.weaken.weaken.weaken.weaken⌝ₛ) → y ∈ ⌜(.bound 3 : Term (d+5))⌝ₛ)⟫))))))

theorem tg_dense_hit_sat_l {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (ℓ s t k N β g a₀ b₀ E q : Term d) :
    Formula.satisfies ρ (tg_dense_hit_m p ℓ s t k N β g a₀ b₀ E q) ↔
      Tg_dense_hit_d hZF (p.map_l (fun t => t.eval ρ)) (ℓ.eval ρ) (s.eval ρ) (t.eval ρ) (k.eval ρ)
        (N.eval ρ) (β.eval ρ) (g.eval ρ) (a₀.eval ρ) (b₀.eval ρ) (E.eval ρ) (q.eval ρ) := by
  simp only [tg_dense_hit_m, Tg_dense_hit_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    tg_generic_target_sat_l hZF, Formula.satisfies_mem_iff, rd_entry0_sat_l hZF.1,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Definitional.Term.eval_weaken, Tg_params_d.map_l]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal
