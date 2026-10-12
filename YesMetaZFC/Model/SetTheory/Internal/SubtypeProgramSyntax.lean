import YesMetaZFC.Model.SetTheory.Internal.SubtypeProgramMatrix

/-! # 子类型程序与固定槽位表的原公式

编译矩阵之外，原变量前缀、全部参数槽覆盖和实际名字列构造也写入证书。
因此从内部表取出的程序直接满足原 `Ts_program_d`，无须补交列生成器。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tt_eval_cases_l {d k} (ρ : Env M d) (a : Term d) (b : Fin k → Term d) :
    (fun j : Fin (k + 1) => (Fin.cases a b j : Term d).eval ρ) =
      (fun j => Fin.cases (a.eval ρ) (fun j => (b j).eval ρ) j) := by
  funext j
  exact Fin.cases rfl (fun _ => rfl) j

def ts_columns_m {d} (n b : Term d) (σ : Fin 7 → Term d) : Formula 1 d := set[d] ⟪∀ U N v₀ v₁ v₂ v₃ v₄ v₅ v₆,
  ⌜tn_names0_m⌝ₚ(⌜n⌝ₛ, U, N) → v₀ ∈ N → v₁ ∈ N → v₂ ∈ N → v₃ ∈ N → v₄ ∈ N → v₅ ∈ N → v₆ ∈ N →
    ∃ C, ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(C, ⌜b⌝ₛ, N) ∧
    (∀ i ∈ ⌜n⌝ₛ, ⌜rd_entry0_m⌝ₚ(i, i, C)) ∧
    ⌜rd_entry0_m⌝ₚ(⌜σ 0⌝ₛ, v₀, C) ∧ ⌜rd_entry0_m⌝ₚ(⌜σ 1⌝ₛ, v₁, C) ∧
    ⌜rd_entry0_m⌝ₚ(⌜σ 2⌝ₛ, v₂, C) ∧ ⌜rd_entry0_m⌝ₚ(⌜σ 3⌝ₛ, v₃, C) ∧
    ⌜rd_entry0_m⌝ₚ(⌜σ 4⌝ₛ, v₄, C) ∧ ⌜rd_entry0_m⌝ₚ(⌜σ 5⌝ₛ, v₅, C) ∧ ⌜rd_entry0_m⌝ₚ(⌜σ 6⌝ₛ, v₆, C)⟫

@[simp] theorem ts_columns_closed_l {d} (n b : Term d) (σ : Fin 7 → Term d)
    (hn : n.freeSupport = []) (hb : b.freeSupport = []) (hσ : ∀ j, (σ j).freeSupport = []) :
    (ts_columns_m n b σ).FreeClosed := by
  simp -implicitDefEqProofs [ts_columns_m, Definitional.Formula.FreeClosed, hn, hb, hσ]

theorem ts_columns_sat_l {d} (ρ : Env M d) (n b : Term d) (σ : Fin 7 → Term d) :
    Formula.satisfies ρ (ts_columns_m n b σ) ↔
      ∀ U N, Tn_names_d (n.eval ρ) U N → ∀ v : Fin 7 → M.Domain, (∀ j, M.mem (v j) N) →
        ∃ C, M.IsSetFunctionFromTo I C (b.eval ρ) N ∧
          (∀ j, M.mem j (n.eval ρ) → Rd_entry_d j j C) ∧ ∀ j, Rd_entry_d ((σ j).eval ρ) (v j) C := by
  simp only [ts_columns_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    tn_names0_sat_l (ZF.modelsKP hZF), Formula.satisfies_mem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_isFunctionFromTo_iff I hZF.1,
    rd_entry0_sat_l hZF.1, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · intro h U N names v valid
    obtain ⟨C, fn, old, h₀, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h U N (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)
      names (valid 0) (valid 1) (valid 2) (valid 3) (valid 4) (valid 5) (valid 6)
    exact ⟨C, fn, old, Fin.cases h₀ (Fin.cases h₁ (Fin.cases h₂ (Fin.cases h₃ (Fin.cases h₄
      (Fin.cases h₅ (Fin.cases h₆ (fun j => Fin.elim0 j)))))))⟩
  · intro h U N v₀ v₁ v₂ v₃ v₄ v₅ v₆ names h₀ h₁ h₂ h₃ h₄ h₅ h₆
    obtain ⟨C, fn, old, values⟩ := h U N names (Fin.cases v₀ (Fin.cases v₁ (Fin.cases v₂
      (Fin.cases v₃ (Fin.cases v₄ (Fin.cases v₅ (fun _ => v₆)))))))
      (Fin.cases h₀ (Fin.cases h₁ (Fin.cases h₂ (Fin.cases h₃ (Fin.cases h₄ (Fin.cases h₅ (fun _ => h₆)))))))
    exact ⟨C, fn, old, values 0, values 1, values 2, values 3, values 4, values 5, values 6⟩

def ts_program0_m : Formula 1 12 :=
  let p : Fin 12 → Term 12 := Term.bound
  let σ : Fin 7 → Term 12 := fun i => [p 5, p 6, p 7, p 8, p 9, p 10, p 11].get i
  set[12] ⟪⌜p 1⌝ₛ ∈ ⌜p 0⌝ₛ ∧ ⌜p 2⌝ₛ ∈ ⌜p 0⌝ₛ ∧ ⌜p 4⌝ₛ ∈ ⌜p 0⌝ₛ ∧ ⌜p 1⌝ₛ ⊆ ⌜p 2⌝ₛ ∧
    ⌜p 5⌝ₛ ∈ ⌜p 2⌝ₛ ∧ ⌜p 6⌝ₛ ∈ ⌜p 2⌝ₛ ∧ ⌜p 7⌝ₛ ∈ ⌜p 2⌝ₛ ∧ ⌜p 8⌝ₛ ∈ ⌜p 2⌝ₛ ∧
    ⌜p 9⌝ₛ ∈ ⌜p 2⌝ₛ ∧ ⌜p 10⌝ₛ ∈ ⌜p 2⌝ₛ ∧ ⌜p 11⌝ₛ ∈ ⌜p 2⌝ₛ ∧
    (∀ j ∈ ⌜p 2⌝ₛ, j ∈ ⌜p 1⌝ₛ ∨ j = ⌜p 5⌝ₛ ∨ j = ⌜p 6⌝ₛ ∨ j = ⌜p 7⌝ₛ ∨ j = ⌜p 8⌝ₛ ∨
      j = ⌜p 9⌝ₛ ∨ j = ⌜p 10⌝ₛ ∨ j = ⌜p 11⌝ₛ) ∧
    ⌜ts_columns_m⌝ₚ(⌜p 1⌝ₛ, ⌜p 2⌝ₛ, ⌜σ⌝ₛ) ∧ ⌜sc_num_m (𝒞 := kpair_convention_l)⌝ₚ(⌜p 0⌝ₛ, ⌜p 3⌝ₛ, ⌜p 4⌝ₛ) ∧
    ⌜ts_compile_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 1⌝ₛ, ⌜p 3⌝ₛ, ⌜σ⌝ₛ)⟫

theorem ts_program0_closed_l : ts_program0_m.FreeClosed := by
  simp -implicitDefEqProofs [ts_program0_m, Definitional.Formula.FreeClosed]
  have hs : ∀ i : Fin 7, ([Term.bound 5, Term.bound 6, Term.bound 7, Term.bound 8,
      Term.bound 9, Term.bound 10, Term.bound 11].get i : Term 12).freeSupport = [] := by
    intro i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  exact ⟨ts_columns_closed_l _ _ _ rfl rfl hs, ts_compile_closed_l _ _ _ _ rfl rfl rfl hs⟩

def ts_program_m {d} (ω n b a z : Term d) (σ : Fin 7 → Term d) : Formula 1 d :=
  ts_program0_m.bind (fun i => [ω, n, b, a, z, σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6].get i)

@[simp] theorem ts_program_closed_l {d} (ω n b a z : Term d) (σ : Fin 7 → Term d)
    (hw : ω.freeSupport = []) (hn : n.freeSupport = []) (hb : b.freeSupport = [])
    (ha : a.freeSupport = []) (hz : z.freeSupport = []) (hσ : ∀ j, (σ j).freeSupport = []) :
    (ts_program_m ω n b a z σ).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr ts_program0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hw, hn, hb, ha, hz, hσ 0, hσ 1, hσ 2, hσ 3, hσ 4, hσ 5, hσ 6, fun i => Fin.elim0 i⟩

theorem ts_program_sat_l {d} (ρ : Env M d) (ω n b a z : Term d) (σ : Fin 7 → Term d) :
    Formula.satisfies ρ (ts_program_m ω n b a z σ) ↔
      Ts_program_d hZF (ω.eval ρ) (n.eval ρ) (b.eval ρ) (fun j => (σ j).eval ρ) (a.eval ρ) (z.eval ρ) := by
  have eta (j : Fin 7) :
      ([Term.bound 5, Term.bound 6, Term.bound 7, Term.bound 8, Term.bound 9, Term.bound 10, Term.bound 11].get j : Term 12).eval
        (Definitional.Env.substitute ρ (fun i => [ω, n, b, a, z, σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6].get i)) =
      (σ j).eval ρ := by
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))) j
  simp only [ts_program_m, Formula.satisfies_bind, ts_program0_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1,
    ts_columns_sat_l hZF, sc_num_sat_l I hZF.1, ts_compile_sat_l hZF,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, eta]
  constructor
  · rintro ⟨hn, hb, hz, nb, h₀, h₁, h₂, h₃, h₄, h₅, h₆, cover, columns, code, compile⟩
    refine ⟨hn, hb, hz, nb, Fin.cases h₀ (Fin.cases h₁ (Fin.cases h₂ (Fin.cases h₃ (Fin.cases h₄
      (Fin.cases h₅ (Fin.cases h₆ (fun j => Fin.elim0 j))))))), ?_, columns, code, compile⟩
    intro j hj
    simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false]
    exact cover j hj
  · intro p
    refine ⟨p.finite, p.length, p.natural, p.prefix_bound, p.slots 0, p.slots 1, p.slots 2, p.slots 3,
      p.slots 4, p.slots 5, p.slots 6, ?_, p.columns, p.code, p.compile⟩
    intro j hj
    have h := p.cover j hj
    simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at h
    exact h

/-- 程序文本由原自然数码约束；向外只暴露 ω 及十个自然数参数。 -/
def ts_numeric0_m : Formula 1 11 := .existsE (ts_program_m
  (.bound 1) (.bound 2) (.bound 3) .newest (.bound 4)
  (fun i => [Term.bound 5, Term.bound 6, Term.bound 7, Term.bound 8, Term.bound 9, Term.bound 10, Term.bound 11].get i))

theorem ts_numeric0_closed_l : ts_numeric0_m.FreeClosed := by
  simp -implicitDefEqProofs [ts_numeric0_m, Definitional.Formula.FreeClosed]
  apply ts_program_closed_l <;> try rfl
  intro i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i

theorem ts_numeric0_sat_l (ρ : Env M 11) : Formula.satisfies ρ ts_numeric0_m ↔
    ∃ a, Ts_program_d hZF (ρ.bound 0) (ρ.bound 1) (ρ.bound 2)
      (fun i => [ρ.bound 4, ρ.bound 5, ρ.bound 6, ρ.bound 7, ρ.bound 8, ρ.bound 9, ρ.bound 10].get i) a (ρ.bound 3) := by
  simp only [ts_numeric0_m, Formula.satisfies_exists_iff, ts_program_sat_l hZF]
  refine exists_congr fun a => ?_
  have eq : (fun i : Fin 7 =>
      ([Term.bound 5, Term.bound 6, Term.bound 7, Term.bound 8, Term.bound 9, Term.bound 10, Term.bound 11].get i : Term 12).eval (ρ.push a)) =
      (fun i => [ρ.bound 4, ρ.bound 5, ρ.bound 6, ρ.bound 7, ρ.bound 8, ρ.bound 9, ρ.bound 10].get i) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  rw [eq]
  rfl

def ts_numeric_m {d} (ω n b z : Term d) (σ : Fin 7 → Term d) : Formula 1 d :=
  ts_numeric0_m.bind (fun i => [ω, n, b, z, σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6].get i)

@[simp] theorem ts_numeric_closed_l {d} (ω n b z : Term d) (σ : Fin 7 → Term d)
    (hw : ω.freeSupport = []) (hn : n.freeSupport = []) (hb : b.freeSupport = []) (hz : z.freeSupport = [])
    (hσ : ∀ i, (σ i).freeSupport = []) : (ts_numeric_m ω n b z σ).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr ts_numeric0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hw, hn, hb, hz, hσ 0, hσ 1, hσ 2, hσ 3, hσ 4, hσ 5, hσ 6, fun i => Fin.elim0 i⟩

theorem ts_numeric_sat_l {d} (ρ : Env M d) (ω n b z : Term d) (σ : Fin 7 → Term d) :
    Formula.satisfies ρ (ts_numeric_m ω n b z σ) ↔
      ∃ a, Ts_program_d hZF (ω.eval ρ) (n.eval ρ) (b.eval ρ) (fun i => (σ i).eval ρ) a (z.eval ρ) := by
  simp only [ts_numeric_m, Formula.satisfies_bind, ts_numeric0_sat_l hZF]
  have eq : (fun i : Fin 7 => [(σ 0).eval ρ, (σ 1).eval ρ, (σ 2).eval ρ, (σ 3).eval ρ,
      (σ 4).eval ρ, (σ 5).eval ρ, (σ 6).eval ρ].get i) = (fun i => (σ i).eval ρ) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  exact exists_congr fun a => by rw [← eq]; rfl

end YesMetaZFC.SetTheory.Internal
