import YesMetaZFC.Model.Forcing.Iteration.Closed.Interval
import YesMetaZFC.Model.Forcing.Iteration.Recursion.Basic

/-! # 原公式后继规则的实际可数闭名称证书

规则提供真实后继名称、旧 ω 名称及闭性力迫。相邻闭区间由已有下界构造证明，
不把相邻闭区间或整个迭代的闭性当作规则输入。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def Row_cl_next_d (ω α B R b D V : M.Domain) : Prop := ∃ A T t w,
  Row_next_d M α B R b A T t D V ∧ Name_d M B T ∧ Check_d M b ω w ∧
  Forces_d M B R B (closed_m (.bound 1) .newest (.bound 1) (.bound 2))
    (((⟨fun _ => w, fun _ => w⟩ : Env M 1).push A).push T) b

def Row_cl_rule_d (I : kpair_convention_l.Interpretation M) (ω : M.Domain) {n}
    (φ : BinarySchema (n+4)) (ρ : Env M n) : Prop :=
  ∀ δ F G b D V, Row_system_d I δ F G b → (∃ α, M.SuccessorOf δ α) →
    φ.denote (row_rule_env_l ρ δ F G b) D V →
      ∃ α B R, M.SuccessorOf δ α ∧ Entry_d M α B F ∧ Entry_d M α R G ∧ Row_cl_next_d ω α B R b D V

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem row_iteration_cl_next_l {n} {φ : BinarySchema (n+4)} {ρ : Env M n} {ω δ F G b α β B R D V}
    (hω : M.IsOmega ω) (hRule : Row_rule_d I true ω φ ρ) (hCl : Row_cl_rule_d I ω φ ρ)
    (h : Row_iteration_d I true ω b φ ρ δ F G) (hβ : M.SuccessorOf β α)
    (hB : Entry_d M α B F) (hR : Entry_d M α R G) (hD : Entry_d M β D F) (hV : Entry_d M β V G) :
    Row_cl_d I ω α B R D V := by
  obtain ⟨F', G', hF, hG, hi, ha⟩ := row_iteration_step_l hZF hω hRule h hD hV
  have hα := hi.1.conditions.1.mem hβ.predecessor_mem
  rcases ha with ⟨hSucc, ha⟩ | hl
  · obtain ⟨α', B', R', hβ', hB', hR', A, T, t, w, hNext, hT, hw, hc⟩ :=
      hCl β F' G' b D V hi.1 hSucc ha
    have he := Structure.SuccessorOf.predecessor_eq hZFC.1 hα hβ hβ'
    subst α'
    have heB := h.1.conditions.2.1.2 α B' B ((hF.2 α B').mp hB').2 hB
    have heR := h.1.relations.2.1.2 α R' R ((hG.2 α R').mp hR').2 hR
    subst B' R'
    exact row_cl_next_l hZFC (h.1.stages α B R hB hR) hNext (h.1.stages β D V hD hV).order hT hω hw hc
  · exact (successor_not_union_l hα hβ hl.sup).elim

end YesMetaZFC.Model.Forcing.Internal
