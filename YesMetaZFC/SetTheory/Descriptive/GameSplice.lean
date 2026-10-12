import YesMetaZFC.SetTheory.Descriptive.GameContinuation

/-! # 按第一步落子拼接实际策略

K 给每个字母指定一个策略图。在尚无第 n 项的历史上取 a，
已有第 n 项时转交给 K 指定的策略。这里只用 ZF 的函数图替换。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Cg_splice_d (n a K h v : M.Domain) : Prop :=
  ((¬ ∃ x, Rd_entry_d n x h) ∧ v = a) ∨
    ∃ x σ, Rd_entry_d n x h ∧ Rd_entry_d x σ K ∧ Rd_entry_d h v σ

def cg_splice_m {d} (n a K h v : Term d) : Formula 1 d := set[d] ⟪
  (¬ (∃ x, ⌜rd_entry0_m⌝ₚ(⌜n⌝ₛ, x, ⌜h⌝ₛ)) ∧ ⌜v⌝ₛ = ⌜a⌝ₛ) ∨
  (∃ x, ∃ σ, ⌜rd_entry0_m⌝ₚ(⌜n⌝ₛ, x, ⌜h⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(x, σ, ⌜K⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜h⌝ₛ, ⌜v⌝ₛ, σ))⟫
derive_free_closed cg_splice_m

theorem cg_splice_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n a K h v : Term d) :
    Formula.satisfies ρ (cg_splice_m n a K h v) ↔
      Cg_splice_d (n.eval ρ) (a.eval ρ) (K.eval ρ) (h.eval ρ) (v.eval ρ) := by
  simp only [cg_splice_m, Cg_splice_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_exists_iff, rd_entry0_sat_l hE,
    Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken]
  rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem cg_splice_l {ω X F Z n a K : M.Domain} (space : Fseq_space_d I ω X F)
    (strategies : M.IsFunctionSpace I Z F X) (ha : M.mem a X) (table : M.IsSetFunctionFromTo I K X Z) :
    ∃ σ, M.IsSetFunctionFromTo I σ F X ∧
      ∀ h v, Rd_entry_d h v σ ↔ M.mem h F ∧ Cg_splice_d n a K h v := by
  classical
  let ρ : Env M 3 := ((⟨fun _ => n, fun _ => n⟩ : Env M 1).push a).push K
  let φ : BinarySchema 3 := { body := cg_splice_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat h v : φ.denote ρ h v ↔ Cg_splice_d n a K h v := cg_splice_sat_l hZF.1 _ _ _ _ _ _
  have total h (hh : M.mem h F) : ∃ v, Cg_splice_d n a K h v := by
    by_cases read : ∃ x, Rd_entry_d n x h
    · obtain ⟨x, hx⟩ := read
      obtain ⟨_, _, fn⟩ := (space h).mp hh
      obtain ⟨τ, hτ, ht⟩ := table.2.2 x (fn.output_mem_of_pairMember hx)
      obtain ⟨v, _, hv⟩ := ((strategies τ).mp hτ).2.2 h hh
      exact ⟨v, Or.inr ⟨x, τ, hx, ht, hv⟩⟩
    · exact ⟨a, Or.inl ⟨read, rfl⟩⟩
  have unique h (hh : M.mem h F) v w (hv : Cg_splice_d n a K h v) (hw : Cg_splice_d n a K h w) : v = w := by
    rcases hv with ⟨no, rfl⟩ | ⟨x, σ, hx, hσ, hv⟩
    · exact hw.elim (fun h => h.2.symm) (fun ⟨x, _, hx, _⟩ => (no ⟨x, hx⟩).elim)
    · rcases hw with ⟨no, _⟩ | ⟨y, τ, hy, hτ, hw⟩
      · exact (no ⟨x, hx⟩).elim
      · obtain ⟨_, _, fn⟩ := (space h).mp hh
        have e := fn.1.2 n x y hx hy
        subst y
        have e := table.1.2 x σ τ hσ hτ
        subst τ
        exact ((strategies σ).mp (table.output_mem_of_pairMember hσ)).1.2 h v w hv hw
  obtain ⟨σ, fn, read⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ
    (fun h hh => (total h hh).imp fun v hv => (sat h v).mpr hv)
    (fun h hh v w hv hw => unique h hh v w ((sat h v).mp hv) ((sat h w).mp hw)) (by
      intro h v _ hv
      rcases (sat h v).mp hv with ⟨_, rfl⟩ | ⟨_, τ, _, hτ, hv⟩
      · exact ha
      · exact ((strategies τ).mp (table.output_mem_of_pairMember hτ)).output_mem_of_pairMember hv)
  exact ⟨σ, fn, fun h v => (read h v).trans (and_congr Iff.rfl (sat h v))⟩

end YesMetaZFC.SetTheory.Descriptive
