import YesMetaZFC.Model.Closure
import YesMetaZFC.Model.FirstOrder.Substructure
import YesMetaZFC.Model.FirstOrder.Valuation

/-! # 任意多排序结构的 Skolem 壳

见证函数作为显式数据给定，仅在存在公式成立时调用。不从 `Nonempty` 或存在命题
选择 Type 数据，不假定语言或模型可数，也不专门使用集合论语言。
空生成集也允许：各排序的非空性由真公式的指定见证得到。
壳是对这套指定规则的最小闭包，而非所有初等子模型之交。
-/

namespace YesMetaZFC.Logic.FirstOrder
open Model Automation.RelationalTranslation
universe u v w x y z
variable {σ : Signature.{u, v, w}} {ℳ : Structure.{u, v, w, x} σ}

/-- 部分 Skolem 函数及其见证证书；不给虚假存在公式选择默认值。 -/
structure Skolem_m (ℳ : Structure.{u, v, w, x} σ) where
  witness : ∀ {b f s} (φ : Formula σ (s :: b) f) (ρ : Env ℳ b f),
    (∃ a, Formula.satisfies (ρ.pushBound a) φ) → ℳ.Carrier s
  satisfies : ∀ {b f s} (φ : Formula σ (s :: b) f) (ρ : Env ℳ b f)
    (h : ∃ a, Formula.satisfies (ρ.pushBound a) φ),
    Formula.satisfies (ρ.pushBound (witness φ ρ h)) φ

/-- 规则指标包含原函数应用与带任意有限参数的存在公式。 -/
inductive SkolemIndex_m (ℳ : Structure.{u, v, w, x} σ) : Type (max u v w x) where
  | func (r : σ.FuncSymbol) (ts : Values ℳ.Carrier (σ.funcDomain r))
  | witness {b f s} (φ : Formula σ (s :: b) f) (ρ : Env ℳ b f)
      (h : ∃ a, Formula.satisfies (ρ.pushBound a) φ)

namespace Skolem_m

/-- 把具体函数应用装配成独立于语言的多排序闭包规则。 -/
def rules_m (F : Skolem_m ℳ) : RuleFamily_l ℳ.Carrier (SkolemIndex_m ℳ) where
  Arity
    | .func r _ => Σ s, Variable (σ.funcDomain r) s
    | @SkolemIndex_m.witness _ _ b f _ _ _ _ =>
        (Σ s, Variable b s) ⊕ (Σ s, Variable f s)
  sort
    | .func _ _, i => i.1
    | .witness _ _ _, .inl i => i.1
    | .witness _ _ _, .inr i => i.1
  arg
    | .func _ ts, i => valuesAssignment ts i.2
    | .witness _ ρ _, .inl i => ρ.boundVal i.2
    | .witness _ ρ _, .inr i => ρ.freeVal i.2
  target
    | .func r _ => σ.funcCodomain r
    | @SkolemIndex_m.witness _ _ _ _ s _ _ _ => s
  value
    | .func r ts => ℳ.funcInterp r ts
    | .witness φ ρ h => F.witness φ ρ h

def Closed_m (F : Skolem_m ℳ) (A : ∀ s, ℳ.Carrier s → Prop) : Prop :=
  F.rules_m.Closed_l A

private theorem values_mem_m {A : ∀ s, ℳ.Carrier s → Prop} {ss}
    (ts : Values (fun s => {a // A s a}) ss) {s} (i : Variable ss s) :
    A s (valuesAssignment (M := ℳ) (ts.map (fun _ a => a.val)) i) := by
  induction i with
  | here => cases ts with | cons a _ => exact a.property
  | there i ih => cases ts with | cons _ ts => exact ih ts

theorem witness_mem_m (F : Skolem_m ℳ) {A : ∀ s, ℳ.Carrier s → Prop}
    (hA : F.Closed_m A) {b f s} (φ : Formula σ (s :: b) f) (ρ : Env ℳ b f)
    (hρ : (∀ {t} (i : Variable b t), A t (ρ.boundVal i)) ∧
      (∀ {t} (i : Variable f t), A t (ρ.freeVal i)))
    (h : ∃ a, Formula.satisfies (ρ.pushBound a) φ) : A s (F.witness φ ρ h) :=
  hA (.witness φ ρ h) (fun | .inl i => hρ.1 i.2 | .inr i => hρ.2 i.2)

/-- 真公式的指定见证使每个排序非空；只在 Prop 中消去原结构的非空证书。 -/
theorem nonempty_m (F : Skolem_m ℳ) {A : ∀ s, ℳ.Carrier s → Prop}
    (hA : F.Closed_m A) (s : σ.SortSymbol) : ∃ a, A s a := by
  have h : ∃ a : ℳ.Carrier s, Formula.satisfies (Env.empty.pushBound a)
      (Formula.truth : Formula σ [s] []) := by
    obtain ⟨a⟩ := ℳ.nonempty s
    exact ⟨a, True.intro⟩
  refine ⟨F.witness .truth Env.empty h, F.witness_mem_m hA .truth Env.empty ?_ h⟩
  exact ⟨(fun i => nomatch i), (fun i => nomatch i)⟩

/-- 任意 Skolem 封闭子集的同层子结构；不额外选择基点。 -/
def substructure_m (F : Skolem_m ℳ) (A : ∀ s, ℳ.Carrier s → Prop)
    (hA : F.Closed_m A) : Substructure_m ℳ where
  carrier := A
  nonempty := F.nonempty_m hA
  closed r ts := by
    apply hA (.func r (ts.map (fun s (a : {a // A s a}) => a.val)))
    intro i
    exact values_mem_m ts i.2

theorem witness_closed_m (F : Skolem_m ℳ) (A : ∀ s, ℳ.Carrier s → Prop)
    (hA : F.Closed_m A) : (F.substructure_m A hA).WitnessClosed_m :=
  fun φ ρ hρ h => ⟨F.witness φ ρ h, F.witness_mem_m hA φ ρ hρ h, F.satisfies φ ρ h⟩

theorem elementary_m (F : Skolem_m ℳ) (A : ∀ s, ℳ.Carrier s → Prop)
    (hA : F.Closed_m A) : (F.substructure_m A hA).Elementary_m :=
  (F.substructure_m A hA).tarski_vaught_m.mpr (F.witness_closed_m A hA)

/-- 对任意生成子集构造实际 Skolem 壳，包含空生成集。 -/
def hull_m (F : Skolem_m ℳ) (A : ∀ s, ℳ.Carrier s → Prop) : Substructure_m ℳ :=
  F.substructure_m (F.rules_m.Closure_l A) (F.rules_m.closed_l A)

theorem seed_mem_m (F : Skolem_m ℳ) {A : ∀ s, ℳ.Carrier s → Prop} {s a}
    (h : A s a) : (F.hull_m A).carrier s a := .seed h

theorem hull_closed_m (F : Skolem_m ℳ) (A : ∀ s, ℳ.Carrier s → Prop) :
    F.Closed_m (F.hull_m A).carrier := F.rules_m.closed_l A

theorem hull_le_m (F : Skolem_m ℳ) {A B : ∀ s, ℳ.Carrier s → Prop}
    (h : ∀ s a, A s a → B s a) (hB : F.Closed_m B) {s a}
    (ha : (F.hull_m A).carrier s a) : B s a := F.rules_m.least_l h hB ha

theorem hull_mono_m (F : Skolem_m ℳ) {A B : ∀ s, ℳ.Carrier s → Prop}
    (h : ∀ s a, A s a → B s a) {s a}
    (ha : (F.hull_m A).carrier s a) : (F.hull_m B).carrier s a := F.rules_m.mono_l h ha

theorem hull_idem_m (F : Skolem_m ℳ) (A : ∀ s, ℳ.Carrier s → Prop) {s a} :
    (F.hull_m (F.hull_m A).carrier).carrier s a ↔ (F.hull_m A).carrier s a :=
  F.rules_m.idempotent_l A

theorem hull_elementary_m (F : Skolem_m ℳ) (A : ∀ s, ℳ.Carrier s → Prop) :
    (F.hull_m A).Elementary_m := F.elementary_m _ (F.rules_m.closed_l A)

theorem hull_models_iff_m (F : Skolem_m ℳ) (A : ∀ s, ℳ.Carrier s → Prop) (T : Theory σ) :
    Theory.Models (F.hull_m A).structure_m T ↔ Theory.Models ℳ T :=
  (F.hull_m A).models_iff_m (F.hull_elementary_m A) T

/-- 生成集包含诱导实际初等包含映射，不需为满射选择右逆。 -/
theorem hull_inclusion_m (F : Skolem_m ℳ) {A B : ∀ s, ℳ.Carrier s → Prop}
    (h : ∀ s a, A s a → B s a) :
    ((F.hull_m A).inclusion_m (F.hull_m B) (fun _ _ => F.hull_mono_m h)).Elementary_m :=
  (F.hull_m A).elementary_inclusion_m (F.hull_m B) _
    (F.hull_elementary_m A) (F.hull_elementary_m B)

/-- 任意指标的生成族；不要求指标可数、非空或具有可判定相等。 -/
theorem hull_union_iff_m (F : Skolem_m ℳ) {I : Type y}
    (A : I → ∀ s, ℳ.Carrier s → Prop) {s a} :
    (F.hull_m (fun s a => ∃ i, (F.hull_m (A i)).carrier s a)).carrier s a ↔
      (F.hull_m (fun s a => ∃ i, A i s a)).carrier s a := F.rules_m.closure_union_iff_l A

/-- 同时对任意额外指标族封闭的 Skolem 壳；额外运算可以不属于原语言。 -/
def hull_with_m (F : Skolem_m ℳ) {I : Type y}
    (G : RuleFamily_l.{u, max u x, y, z} ℳ.Carrier I)
    (A : ∀ s, ℳ.Carrier s → Prop) : Substructure_m ℳ :=
  F.substructure_m ((F.rules_m.sum_l G).Closure_l A)
    ((F.rules_m.sum_closed_iff_l G _).mp ((F.rules_m.sum_l G).closed_l A)).1

theorem hull_with_closed_m (F : Skolem_m ℳ) {I : Type y}
    (G : RuleFamily_l.{u, max u x, y, z} ℳ.Carrier I) (A : ∀ s, ℳ.Carrier s → Prop) :
    F.Closed_m (F.hull_with_m G A).carrier ∧ G.Closed_l (F.hull_with_m G A).carrier :=
  (F.rules_m.sum_closed_iff_l G _).mp ((F.rules_m.sum_l G).closed_l A)

theorem hull_with_le_m (F : Skolem_m ℳ) {I : Type y}
    (G : RuleFamily_l.{u, max u x, y, z} ℳ.Carrier I) {A B : ∀ s, ℳ.Carrier s → Prop}
    (h : ∀ s a, A s a → B s a) (hF : F.Closed_m B) (hG : G.Closed_l B) {s a}
    (ha : (F.hull_with_m G A).carrier s a) : B s a :=
  (F.rules_m.sum_l G).least_l h ((F.rules_m.sum_closed_iff_l G B).mpr ⟨hF, hG⟩) ha

theorem hull_with_elementary_m (F : Skolem_m ℳ) {I : Type y}
    (G : RuleFamily_l.{u, max u x, y, z} ℳ.Carrier I) (A : ∀ s, ℳ.Carrier s → Prop) :
    (F.hull_with_m G A).Elementary_m := F.elementary_m _ (F.hull_with_closed_m G A).1

end Skolem_m
end YesMetaZFC.Logic.FirstOrder
