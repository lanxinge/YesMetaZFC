import YesMetaZFC.Model.FirstOrder.SubstitutionSemantics

/-! # 原生结构映射与公式保持

载体映射、函数保持、关系嵌入与同构数据逐层分开。
项求值不要求单射、关系保持或有界见证回拉；完整公式保持只另要求满射。
-/

namespace YesMetaZFC.Logic.FirstOrder
universe u v w x y z
variable {σ : Signature.{u, v, w}}

namespace Env
variable {ℳ : Structure.{u, v, w, x} σ} {𝒩 : Structure.{u, v, w, y} σ}

/-- 任意载体映射逐点作用于环境，不要求它是结构同态。 -/
def map (e : ∀ s, ℳ.Carrier s → 𝒩.Carrier s) {b f} (ρ : Env ℳ b f) : Env 𝒩 b f where
  boundVal i := e _ (ρ.boundVal i)
  freeVal i := e _ (ρ.freeVal i)

theorem map_pushBound (e : ∀ s, ℳ.Carrier s → 𝒩.Carrier s) {b f s}
    (ρ : Env ℳ b f) (a : ℳ.Carrier s) :
    (ρ.pushBound a).map e = (ρ.map e).pushBound (e s a) := by
  apply Env.ext
  · intro s i; cases i <;> rfl
  · intro s i; rfl

theorem map_empty (e : ∀ s, ℳ.Carrier s → 𝒩.Carrier s) :
    (Env.empty : Env ℳ [] []).map e = Env.empty := by
  apply Env.ext <;> intro s i <;> cases i

end Env

/-- 只保持函数解释的排序映射。 -/
structure Fn_map (ℳ : Structure.{u, v, w, x} σ) (𝒩 : Structure.{u, v, w, y} σ) where
  map : ∀ s, ℳ.Carrier s → 𝒩.Carrier s
  function_eq : ∀ a ts,
    map (σ.funcCodomain a) (ℳ.funcInterp a ts) = 𝒩.funcInterp a (ts.map map)

namespace Fn_map
variable {ℳ : Structure.{u, v, w, x} σ} {𝒩 : Structure.{u, v, w, y} σ}

mutual
/-- 项解释的保持仅使用函数保持。 -/
theorem term_eval_eq (e : Fn_map ℳ 𝒩) {b f} (ρ : Env ℳ b f) :
    {s : σ.SortSymbol} → (t : Term σ b f s) →
      e.map s (t.eval ρ) = t.eval (ρ.map e.map)
  | _, .bvar _ => rfl
  | _, .fvar _ => rfl
  | _, .app a ts => by
      rw [Term.eval, e.function_eq]
      exact congrArg (𝒩.funcInterp a) (e.arguments_eval_eq ρ ts)

/-- 异质参数列沿函数保持映射逐项传输。 -/
theorem arguments_eval_eq (e : Fn_map ℳ 𝒩) {b f} (ρ : Env ℳ b f) :
    {ss : List σ.SortSymbol} → (ts : Arguments σ b f ss) →
      (ts.eval ρ).map e.map = ts.eval (ρ.map e.map)
  | _, .nil => rfl
  | _, .cons t ts => by
      change Values.cons (e.map _ (t.eval ρ)) ((ts.eval ρ).map e.map) =
        Values.cons (t.eval (ρ.map e.map)) (ts.eval (ρ.map e.map))
      rw [e.term_eval_eq, e.arguments_eval_eq]
end

def refl (ℳ : Structure.{u, v, w, x} σ) : Fn_map ℳ ℳ where
  map _ := id
  function_eq a ts := congrArg (ℳ.funcInterp a) (Values.map_id ts).symm

def comp {𝒱 : Structure.{u, v, w, z} σ} (g : Fn_map 𝒩 𝒱) (e : Fn_map ℳ 𝒩) :
    Fn_map ℳ 𝒱 where
  map s a := g.map s (e.map s a)
  function_eq a ts := by rw [e.function_eq, g.function_eq, Values.map_comp]

end Fn_map

/-- 原生结构嵌入另要求单射与原子关系的双向保持。 -/
structure Str_emb (ℳ : Structure.{u, v, w, x} σ) (𝒩 : Structure.{u, v, w, y} σ)
    extends Fn_map ℳ 𝒩 where
  map_injective : ∀ s, Function.Injective (map s)
  relation_iff : ∀ r ts, ℳ.relInterp r ts ↔ 𝒩.relInterp r (ts.map map)

namespace Str_emb
variable {ℳ : Structure.{u, v, w, x} σ} {𝒩 : Structure.{u, v, w, y} σ}

def refl (ℳ : Structure.{u, v, w, x} σ) : Str_emb ℳ ℳ where
  toFn_map := Fn_map.refl ℳ
  map_injective _ _ _ h := h
  relation_iff r ts := by change _ ↔ ℳ.relInterp r (ts.map (fun _ a => a)); rw [Values.map_id]

def comp {𝒱 : Structure.{u, v, w, z} σ} (g : Str_emb 𝒩 𝒱) (e : Str_emb ℳ 𝒩) :
    Str_emb ℳ 𝒱 where
  toFn_map := g.toFn_map.comp e.toFn_map
  map_injective s _ _ h := e.map_injective s (g.map_injective s h)
  relation_iff r ts := by
    simpa only [Fn_map.comp, Values.map_comp] using (e.relation_iff r ts).trans (g.relation_iff r _)

/-- 满嵌入保持全部一阶公式；量词步骤只在需要回拉见证时消费满射。 -/
theorem formula_iff (e : Str_emb ℳ 𝒩) (h : ∀ s, Function.Surjective (e.map s))
    {b f} (φ : Formula σ b f) (ρ : Env ℳ b f) :
    Formula.satisfies ρ φ ↔ Formula.satisfies (ρ.map e.map) φ := by
  induction φ with
  | falsum | truth => rfl
  | rel r ts =>
      change ℳ.relInterp r (ts.eval ρ) ↔ 𝒩.relInterp r (ts.eval (ρ.map e.map))
      rw [← e.toFn_map.arguments_eval_eq]
      exact e.relation_iff r _
  | equal t t' =>
      change t.eval ρ = t'.eval ρ ↔ t.eval (ρ.map e.map) = t'.eval (ρ.map e.map)
      rw [← e.toFn_map.term_eval_eq, ← e.toFn_map.term_eval_eq]
      exact ⟨congrArg (e.map _), fun h => e.map_injective _ h⟩
  | neg φ ih => exact not_congr (ih _)
  | conj φ ψ ih jh => exact and_congr (ih _) (jh _)
  | disj φ ψ ih jh => exact or_congr (ih _) (jh _)
  | imp φ ψ ih jh => exact imp_congr (ih _) (jh _)
  | iff φ ψ ih jh => exact iff_congr (ih _) (jh _)
  | forallE s φ ih =>
      constructor
      · intro hp a
        obtain ⟨a, rfl⟩ := h s a
        simpa only [Env.map_pushBound] using (ih (ρ.pushBound a)).mp (hp a)
      · intro hp a
        apply (ih (ρ.pushBound a)).mpr
        simpa only [Env.map_pushBound] using hp (e.map s a)
  | existsE s φ ih =>
      constructor
      · rintro ⟨a, hp⟩
        exact ⟨e.map s a, by simpa only [Env.map_pushBound] using (ih (ρ.pushBound a)).mp hp⟩
      · rintro ⟨a, hp⟩
        obtain ⟨a, rfl⟩ := h s a
        exact ⟨a, (ih (ρ.pushBound a)).mpr (by simpa only [Env.map_pushBound] using hp)⟩

/-- 理论模型性在满嵌入两侧一致。 -/
theorem models_iff (e : Str_emb ℳ 𝒩) (h : ∀ s, Function.Surjective (e.map s))
    (T : Theory σ) : Theory.Models ℳ T ↔ Theory.Models 𝒩 T := by
  have k (φ : Sentence σ) : φ.TrueIn ℳ ↔ φ.TrueIn 𝒩 := by
    simpa only [Formula.TrueIn, Env.map_empty] using e.formula_iff h φ Env.empty
  exact ⟨fun hT φ hφ => (k φ).mp (hT φ hφ), fun hT φ hφ => (k φ).mpr (hT φ hφ)⟩

end Str_emb

/-- 带显式逆映射的同构数据，避免从满射证明中作不可计算选择。 -/
structure Str_iso (ℳ : Structure.{u, v, w, x} σ) (𝒩 : Structure.{u, v, w, y} σ)
    extends Str_emb ℳ 𝒩 where
  inverse : ∀ s, 𝒩.Carrier s → ℳ.Carrier s
  left_inv : ∀ s a, inverse s (map s a) = a
  right_inv : ∀ s a, map s (inverse s a) = a

namespace Str_iso

def refl (ℳ : Structure.{u, v, w, x} σ) : Str_iso ℳ ℳ where
  toStr_emb := Str_emb.refl ℳ
  inverse _ := id
  left_inv _ _ := rfl
  right_inv _ _ := rfl

theorem surjective {ℳ : Structure.{u, v, w, x} σ} {𝒩 : Structure.{u, v, w, y} σ}
    (e : Str_iso ℳ 𝒩) (s : σ.SortSymbol) : Function.Surjective (e.map s) :=
  fun a => ⟨e.inverse s a, e.right_inv s a⟩

end Str_iso
end YesMetaZFC.Logic.FirstOrder
