import YesMetaZFC.Model.FirstOrder.Morphism

/-! # 初等嵌入与 Tarski–Vaught 判据

复用原多排序结构、完整一阶公式及普通嵌入。判据只要求存在公式在像中有见证，
不要求嵌入满射，不选取见证函数；全称量词步骤的经典推理留在 Prop 中。
这里的初等性针对原 AST 与默认 Tarski 语义，不声称非标准内部公式码的初等性。
-/

namespace YesMetaZFC.Logic.FirstOrder
universe u v w x y z
variable {σ : Signature.{u, v, w}}
variable {ℳ : Structure.{u, v, w, x} σ} {𝒩 : Structure.{u, v, w, y} σ}

namespace Str_emb

/-- 对任意有限参数环境，保持并反映全部一阶公式。 -/
def Elementary_m (e : Str_emb ℳ 𝒩) : Prop :=
  ∀ {b f} (φ : Formula σ b f) (ρ : Env ℳ b f),
    Formula.satisfies ρ φ ↔ Formula.satisfies (ρ.map e.map) φ

/-- 目标中的存在公式有来自源结构的见证；矩阵仍在目标中解释。 -/
def WitnessClosed_m (e : Str_emb ℳ 𝒩) : Prop :=
  ∀ {b f s} (φ : Formula σ (s :: b) f) (ρ : Env ℳ b f),
    (∃ a, Formula.satisfies ((ρ.map e.map).pushBound a) φ) →
      ∃ a, Formula.satisfies ((ρ.map e.map).pushBound (e.map s a)) φ

theorem witness_of_elementary_m (e : Str_emb ℳ 𝒩) (h : e.Elementary_m) :
    e.WitnessClosed_m := by
  intro b f s φ ρ hφ
  obtain ⟨a, ha⟩ := (h (.existsE s φ) ρ).mpr hφ
  exact ⟨a, by simpa only [Env.map_pushBound] using (h φ (ρ.pushBound a)).mp ha⟩

/-- 真子结构也可使用的见证判据；原子公式只消费已有嵌入条件。 -/
theorem elementary_of_witness_m (e : Str_emb ℳ 𝒩) (h : e.WitnessClosed_m) :
    e.Elementary_m := by
  intro b f φ ρ
  induction φ with
  | falsum | truth => rfl
  | rel r ts =>
      change ℳ.relInterp r (ts.eval ρ) ↔ 𝒩.relInterp r (ts.eval (ρ.map e.map))
      rw [← e.toFn_map.arguments_eval_eq]
      exact e.relation_iff r _
  | equal t t' =>
      change t.eval ρ = t'.eval ρ ↔ t.eval (ρ.map e.map) = t'.eval (ρ.map e.map)
      rw [← e.toFn_map.term_eval_eq, ← e.toFn_map.term_eval_eq]
      exact ⟨congrArg (e.map _), fun k => e.map_injective _ k⟩
  | neg φ ih => exact not_congr (ih _)
  | conj φ ψ ih jh => exact and_congr (ih _) (jh _)
  | disj φ ψ ih jh => exact or_congr (ih _) (jh _)
  | imp φ ψ ih jh => exact imp_congr (ih _) (jh _)
  | iff φ ψ ih jh => exact iff_congr (ih _) (jh _)
  | forallE s φ ih =>
      constructor
      · intro hφ a
        apply Classical.byContradiction
        intro ha
        obtain ⟨c, hc⟩ := h (.neg φ) ρ ⟨a, ha⟩
        apply hc
        simpa only [Env.map_pushBound] using (ih (ρ.pushBound c)).mp (hφ c)
      · intro hφ a
        apply (ih (ρ.pushBound a)).mpr
        simpa only [Env.map_pushBound] using hφ (e.map s a)
  | existsE s φ ih =>
      constructor
      · rintro ⟨a, ha⟩
        exact ⟨e.map s a, by simpa only [Env.map_pushBound] using (ih (ρ.pushBound a)).mp ha⟩
      · intro hφ
        obtain ⟨a, ha⟩ := h φ ρ hφ
        exact ⟨a, (ih (ρ.pushBound a)).mpr (by simpa only [Env.map_pushBound] using ha)⟩

/-- Tarski–Vaught：普通结构嵌入初等，当且仅当目标见证可取在其像中。 -/
theorem tarski_vaught_m (e : Str_emb ℳ 𝒩) : e.Elementary_m ↔ e.WitnessClosed_m :=
  ⟨e.witness_of_elementary_m, e.elementary_of_witness_m⟩

theorem elementary_of_surjective_m (e : Str_emb ℳ 𝒩)
    (h : ∀ s, Function.Surjective (e.map s)) : e.Elementary_m := e.formula_iff h

theorem elementary_refl_m (ℳ : Structure.{u, v, w, x} σ) :
    (Str_emb.refl ℳ).Elementary_m :=
  (Str_emb.refl ℳ).elementary_of_surjective_m (fun _ a => ⟨a, rfl⟩)

theorem elementary_comp_m {𝒱 : Structure.{u, v, w, z} σ}
    (g : Str_emb 𝒩 𝒱) (e : Str_emb ℳ 𝒩)
    (hg : g.Elementary_m) (he : e.Elementary_m) : (g.comp e).Elementary_m :=
  fun φ ρ => (he φ ρ).trans (hg φ (ρ.map e.map))

/-- 用于子模型链：已知复合及第二段初等，可消去第二段。 -/
theorem elementary_cancel_m {𝒱 : Structure.{u, v, w, z} σ}
    (g : Str_emb 𝒩 𝒱) (e : Str_emb ℳ 𝒩)
    (hg : g.Elementary_m) (h : (g.comp e).Elementary_m) : e.Elementary_m :=
  fun φ ρ => (h φ ρ).trans (hg φ (ρ.map e.map)).symm

theorem elementary_models_iff_m (e : Str_emb ℳ 𝒩) (h : e.Elementary_m)
    (T : Theory σ) : Theory.Models ℳ T ↔ Theory.Models 𝒩 T := by
  have k (φ : Sentence σ) : φ.TrueIn ℳ ↔ φ.TrueIn 𝒩 := by
    simpa only [Formula.TrueIn, Env.map_empty] using h φ Env.empty
  exact ⟨fun hT φ hφ => (k φ).mp (hT φ hφ), fun hT φ hφ => (k φ).mpr (hT φ hφ)⟩

end Str_emb
end YesMetaZFC.Logic.FirstOrder
