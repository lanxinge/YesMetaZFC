import YesMetaZFC.Model.Henkin.SyntaxNatCoding
import YesMetaZFC.SetTheory.Language

/-! # 纯集合论公式查询的共同可数编码

查询保留原绑定、自由上下文与有限参数编码。壳构造和力迫调度共享同一编码，
枚举函数只在存在证明中选取。
-/

namespace YesMetaZFC.SetTheory
open Logic Logic.FirstOrder Automation.SyntaxNatCoding FirstOrder.Completeness.Henkin
universe u

def pure_symbols_l : SymbolCoding ℒ where
  sort := ⟨fun _ => 0, fun a b _ => by cases a; cases b; rfl⟩
  function := ⟨(fun a => nomatch a), (fun a => nomatch a)⟩
  relation := ⟨fun _ => 0, fun a b _ => by cases a; cases b; rfl⟩

structure Query_code_l where
  bound : SortContext ℒ
  free : SortContext ℒ
  formula : Formula ℒ bound free
  parameter : Nat

def query_coding_l : NatCoding Query_code_l where
  encode q := NatPairing.pair ((NatCoding.list pure_symbols_l.sort).encode q.bound)
    (NatPairing.pair ((NatCoding.list pure_symbols_l.sort).encode q.free)
      (NatPairing.pair (formula_encode pure_symbols_l q.formula) q.parameter))
  injective := by
    rintro ⟨b, f, φ, n⟩ ⟨c, g, ψ, m⟩ h
    obtain ⟨hb, h⟩ := NatPairing.pair_eq_pair_iff.mp h
    obtain ⟨hf, h⟩ := NatPairing.pair_eq_pair_iff.mp h
    obtain ⟨hφ, hn⟩ := NatPairing.pair_eq_pair_iff.mp h
    have hb := (NatCoding.list pure_symbols_l.sort).injective hb
    have hf := (NatCoding.list pure_symbols_l.sort).injective hf
    dsimp only at hb hf hφ hn
    subst c; subst g; subst m
    have hφ := formula_encode_injective pure_symbols_l hφ
    subst ψ
    rfl

theorem enum_exists_l {A : Type u} (c : NatCoding A) (a : A) : ∃ e : Nat → A, Function.Surjective e := by
  classical
  have h n : ∃ x, ∀ y, c.encode y = n → x = y := by
    by_cases h : ∃ x, c.encode x = n
    · obtain ⟨x, hx⟩ := h
      exact ⟨x, fun y hy => c.injective (hx.trans hy.symm)⟩
    · exact ⟨a, fun y hy => (h ⟨y, hy⟩).elim⟩
  obtain ⟨e, he⟩ := Classical.axiomOfChoice h
  exact ⟨e, fun x => ⟨c.encode x, he _ x rfl⟩⟩

end YesMetaZFC.SetTheory
