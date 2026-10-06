import YesMetaZFC.Model.Zermelo.Semantics

/-! # 有限顺序依赖下的共享候选池
每层谓词只依赖此前的池，检验对象可以依赖最终的整个环境。
前缀改变后重建后续层；失败的否定见证在所属层的重建中保留。
本层只处理有限需求，不包含一般收集模式的验证。
-/

namespace YesMetaZFC.Model.Zermelo
open Logic Logic.FirstOrder SetTheory
universe u

/-- 按前缀绑定的有限需求块。 -/
inductive Ft_ctx : Nat → Type (u+1) where
  | nil : Ft_ctx 0
  | cons {n} (l : List Nat) (p : Nat → V.{u} → Prop)
      (k : V.{u} → Ft_ctx n) : Ft_ctx (n+1)
def Ft_vals : Nat → Type (u+1)
  | 0 => PUnit.{u+2}
  | n+1 => V.{u} × Ft_vals n
def Ft_tests : Nat → Type (u+1)
  | 0 => PUnit.{u+2}
  | n+1 => (Nat → V.{u}) × Ft_tests n
-- 直接使用递归子，避免依赖匹配引入命题外延性。
def Ft_sat {n} (d : Ft_ctx.{u} n) : Ft_vals.{u} n → Ft_tests.{u} n → Prop :=
  Ft_ctx.rec (motive := fun n _ => Ft_vals.{u} n → Ft_tests.{u} n → Prop)
    (fun _ _ => True)
    (fun {_} l p _ ih s t =>
      (∀ i, i ∈ l → ¬¬∃ y, y ∈ s.1 ∧ (p i y → p i (t.1 i))) ∧ ih s.1 s.2 t.2) d

/-- 在稳定存在下同时满足各层需求；查询函数可读取全部最终池。 -/
theorem ft_run {n} (d : Ft_ctx.{u} n) : ∀ q : Ft_vals.{u} n → Ft_tests.{u} n,
    ¬¬∃ s, Ft_sat d s (q s) := by
  induction d with
  | nil => intro q; exact nn_in ⟨⟨⟩, trivial⟩
  | cons l p k ih =>
    intro q
    -- 外归纳沿后续绑定下降；内归纳沿当前池的剩余需求下降。
    have h : ∀ j : List Nat, ∀ a : V.{u}, ¬¬∃ b s, V.sub a b ∧
        (¬¬∃ x, x ∈ b) ∧
        (∀ i, i ∈ j → ¬¬∃ y, y ∈ b ∧ (p i y → p i ((q (b, s)).1 i))) ∧
        Ft_sat (k b) s ((q (b, s)).2) := by
      intro j
      induction j with
      | nil =>
        intro a
        let b := V.succ a
        apply st_use (ih b (fun s => (q (b, s)).2))
        intro ⟨s, hs⟩
        exact nn_in ⟨b, s,
          (fun x hx => st_use hx (fun ⟨i, e⟩ => nn_in ⟨.inl i, e⟩)),
          nn_in ⟨a, nn_in ⟨.inr ⟨⟩, V.eq_refl _⟩⟩,
          (fun _ h => nomatch h), hs⟩
      | cons i j hj =>
        intro a
        apply st_use (hj a)
        intro ⟨b, s, hab, hn, hb, hs⟩
        let t := (q (b, s)).1 i
        apply st_cases (p i t)
        · intro hi
          refine nn_in ⟨b, s, hab, hn, fun r hr => ?_, hs⟩
          cases hr with
          | head => exact st_use hn (fun ⟨y, hy⟩ => nn_in ⟨y, hy, fun _ => hi⟩)
          | tail _ hr => exact hb r hr
        · intro hi
          let c : V.{u} := .sup (Sum b.idx PUnit)
            (fun r => match r with | .inl r => b.elem r | .inr _ => t)
          have ht : t ∈ c := nn_in ⟨.inr ⟨⟩, V.eq_refl _⟩
          have hc : V.sub b c := fun x hx => st_use hx (fun ⟨r, e⟩ => nn_in ⟨.inl r, e⟩)
          apply st_use (hj c)
          intro ⟨d, v, hcd, hn, hd, hv⟩
          refine nn_in ⟨d, v, fun x hx => hcd x (hc x (hab x hx)), hn, fun r hr => ?_, hv⟩
          cases hr with
          | head => exact nn_in ⟨t, hcd t ht, fun h => (hi h).elim⟩
          | tail _ hr => exact hd r hr
    exact st_use (h l V.empty) (fun ⟨b, s, _, _, hb, hs⟩ => nn_in ⟨(b, s), hb, hs⟩)

/-- 原始 AST 上两个依赖的共享池；第二池同时用于检验两层。 -/
theorem ft_two {b f} (φ : Nat → Formula ℒ b (SetSort.set :: f))
    (ψ : Nat → Formula ℒ b (SetSort.set :: SetSort.set :: f))
    (ρ : Env.{u} b f) (l m : List Nat) : ¬¬∃ a c,
      (∀ i, i ∈ l → ¬¬∃ y, y ∈ a ∧ (sat (φ i) (ρ.pushFree y) → sat (φ i) (ρ.pushFree c))) ∧
      (∀ i, i ∈ m → ¬¬∃ y, y ∈ c ∧ (sat (ψ i) ((ρ.pushFree a).pushFree y) →
        sat (ψ i) ((ρ.pushFree a).pushFree c))) := by
  let d : Ft_ctx.{u} 2 := .cons l (fun i y => sat (φ i) (ρ.pushFree y)) (fun a =>
    .cons m (fun i y => sat (ψ i) ((ρ.pushFree a).pushFree y)) (fun _ => .nil))
  have h := ft_run d (fun v => (fun _ => v.2.1, (fun _ => v.2.1, ⟨⟩)))
  exact st_use h (fun ⟨(a, (c, _)), ha, hc, _⟩ => nn_in ⟨a, c, ha, hc⟩)

/-- info: 'YesMetaZFC.Model.Zermelo.ft_two' does not depend on any axioms -/
#guard_msgs in
#print axioms ft_two
end YesMetaZFC.Model.Zermelo
