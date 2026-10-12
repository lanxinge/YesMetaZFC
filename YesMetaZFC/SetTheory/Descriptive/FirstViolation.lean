import YesMetaZFC.SetTheory.Descriptive.Tree
import YesMetaZFC.SetTheory.Descriptive.Game

/-! # 首次违规者输的闭收益集合

L 是逐步检查通过的实际有限历史集合，J 是玩家 I 负责的内部时刻集合。
先构造玩家 I 首次违规的有限证据，再排除所有含有这些证据的前缀。
玩家 II 先违规后继续落子的记录因此仍被判给 I。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Cg_first_d (ω A S L i p : M.Domain) : Prop :=
  ∃ j, M.mem j ω ∧ Fn0_d j A p ∧ M.SuccessorOf j i ∧ ¬ M.mem p L ∧
    ∀ q, M.mem q S → M.MemberSubset q p → ¬ M.MemberSubset p q → M.mem q L

def cg_first_m {d} (ω A S L i p : Term d) : Formula 1 d := set[d] ⟪∃ j ∈ ⌜ω⌝ₛ,
  ⌜fn0_m⌝ₚ(j, ⌜A⌝ₛ, ⌜p⌝ₛ) ∧ ⌜Formula.isSuccessor⌝ₚ(j, ⌜i⌝ₛ) ∧ ¬ (⌜p⌝ₛ ∈ ⌜L⌝ₛ) ∧
  (∀ q ∈ ⌜S⌝ₛ, q ⊆ ⌜p⌝ₛ → ¬ (⌜p⌝ₛ ⊆ q) → q ∈ ⌜L⌝ₛ)⟫
derive_free_closed cg_first_m

theorem cg_first_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A S L i p : Term d) :
    Formula.satisfies ρ (cg_first_m ω A S L i p) ↔ Cg_first_d
      (ω.eval ρ) (A.eval ρ) (S.eval ρ) (L.eval ρ) (i.eval ρ) (p.eval ρ) := by
  simp only [cg_first_m, Cg_first_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    fn0_sat_l hE, Formula.satisfies_isSuccessor_iff, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]
  rfl

def Cg_bad_d (ω A S L J D : M.Domain) : Prop :=
  ∀ p, M.mem p D ↔ M.mem p S ∧ ∃ i, M.mem i J ∧ Cg_first_d ω A S L i p

def Cg_safe_d (S D T : M.Domain) : Prop :=
  ∀ p, M.mem p T ↔ M.mem p S ∧ ∀ q, M.mem q D → ¬ M.MemberSubset q p

def Cg_payoff_d (ω A S L J B W : M.Domain) : Prop :=
  ∃ D T, Cg_bad_d ω A S L J D ∧ Cg_safe_d S D T ∧ Body_d S B T W

/-- 收益集和其开补集都由对象模型的分离构造，参数不含外部历史列表。 -/
theorem cg_payoff_l (hZF : M.Models ZF) (ω A S L J B : M.Domain) :
    ∃ W O, Cg_payoff_d ω A S L J B W ∧
      (∀ f, M.mem f O ↔ M.mem f B ∧ ¬ M.mem f W) ∧ Open_d S B O := by
  let ρ : Env M 5 := (((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push S).push L).push J)
  let φ : UnarySchema 5 := { body := set[6] ⟪∃ i ∈ ⌜(.bound 1 : Term 6)⌝ₛ,
    ⌜cg_first_m⌝ₚ(⌜(.bound 5 : Term 6)⌝ₛ, ⌜(.bound 4 : Term 6)⌝ₛ, ⌜(.bound 3 : Term 6)⌝ₛ,
      ⌜(.bound 2 : Term 6)⌝ₛ, i, ⌜(.newest : Term 6)⌝ₛ)⟫ }
  obtain ⟨D, sep⟩ := ZF.separation_exists_d hZF φ ρ S
  have bad : Cg_bad_d ω A S L J D := by
    intro p
    refine (sep p).trans (and_congr Iff.rfl ?_)
    simp only [φ, Formula.satisfies_existsMem_iff, cg_first_sat_l hZF.1, Definitional.Term.eval_weaken]
    rfl
  let η : Env M 1 := ⟨fun _ => D, fun _ => D⟩
  let ψ : UnarySchema 1 := { body := set[2] ⟪∀ q ∈ ⌜(.bound 1 : Term 2)⌝ₛ, ¬ (q ⊆ ⌜(.newest : Term 2)⌝ₛ)⟫ }
  obtain ⟨T, cut⟩ := ZF.separation_exists_d hZF ψ η S
  have safe : Cg_safe_d S D T := by
    intro p
    refine (cut p).trans (and_congr Iff.rfl ?_)
    simp only [ψ, Formula.satisfies_forallMem_iff, Formula.satisfies_neg_iff,
      Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]
    rfl
  obtain ⟨W, body⟩ := tree_body_exists_l (ZF.modelsKP hZF) S B T
  obtain ⟨O, complement, opened⟩ := tree_body_closed_l (ZF.modelsKP hZF) body
  exact ⟨W, O, ⟨D, T, bad, safe, body⟩, complement, opened⟩

theorem Cg_safe_d.tree_l {S D T : M.Domain} (safe : Cg_safe_d (M := M) S D T) : Tree_d S T := by
  refine ⟨fun p hp => ((safe p).mp hp).1, fun p hp q hq sub => ?_⟩
  exact (safe q).mpr ⟨hq, fun b hb bs => ((safe p).mp hp).2 b hb (fun x hx => sub x (bs x hx))⟩

/-- 玩家 I 的败局恰由有限的首次违规证据见证；否则对局属于闭收益集。 -/
theorem Cg_payoff_d.read_l {ω A S L J B W f : M.Domain}
    (payoff : Cg_payoff_d (M := M) ω A S L J B W) (hf : M.mem f B) :
    ¬ M.mem f W ↔ ∃ p i, M.mem p S ∧ M.MemberSubset p f ∧ M.mem i J ∧ Cg_first_d ω A S L i p := by
  classical
  obtain ⟨D, T, bad, safe, body⟩ := payoff
  constructor
  · intro lose
    have witness : ∃ p, M.mem p S ∧ M.MemberSubset p f ∧ ¬ M.mem p T := by
      apply Classical.byContradiction
      intro h
      exact lose ((body f).mpr ⟨hf, fun p hp sub => Classical.byContradiction (fun no => h ⟨p, hp, sub, no⟩)⟩)
    obtain ⟨p, hp, sub, no⟩ := witness
    have witness : ∃ q, M.mem q D ∧ M.MemberSubset q p := by
      apply Classical.byContradiction
      intro h
      exact no ((safe p).mpr ⟨hp, fun q hq qp => h ⟨q, hq, qp⟩⟩)
    obtain ⟨q, hq, qp⟩ := witness
    obtain ⟨hqS, i, hi, first⟩ := (bad q).mp hq
    exact ⟨q, i, hqS, fun x hx => sub x (qp x hx), hi, first⟩
  · rintro ⟨p, i, hp, sub, hi, first⟩ win
    have pt := ((body f).mp win).2 p hp sub
    exact ((safe p).mp pt).2 p ((bad p).mpr ⟨hp, i, hi, first⟩) (fun _ h => h)

theorem Cg_payoff_d.all_legal_l {ω A S L J B W f : M.Domain}
    (payoff : Cg_payoff_d (M := M) ω A S L J B W) (hf : M.mem f B)
    (legal : ∀ p, M.mem p S → M.MemberSubset p f → M.mem p L) : M.mem f W := by
  apply Classical.byContradiction
  intro no
  obtain ⟨p, _, hp, sub, _, _, _, _, _, bad, _⟩ := (payoff.read_l hf).mp no
  exact bad (legal p hp sub)

end YesMetaZFC.SetTheory.Descriptive
