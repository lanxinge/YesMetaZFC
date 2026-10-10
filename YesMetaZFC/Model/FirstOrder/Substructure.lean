import YesMetaZFC.Model.FirstOrder.Elementary

/-! # 子结构与内部见证判据

每个排序给出非空子集，并只要求对原语言函数封闭。限制结构的载体仍在原 universe，
函数值直接由原结构计算；非空性留作命题，不选择基点。存在公式使用原模型中的
任意有限参数环境，适合后续验证 Skolem hull 的见证封闭性。
-/

namespace YesMetaZFC.Logic.FirstOrder
universe u v w x
variable {σ : Signature.{u, v, w}} {ℳ : Structure.{u, v, w, x} σ}

/-- 原生多排序子结构；零元函数的封闭性也包含在 `closed` 中。 -/
structure Substructure_m (ℳ : Structure.{u, v, w, x} σ) where
  carrier : ∀ s, ℳ.Carrier s → Prop
  nonempty : ∀ s, ∃ a, carrier s a
  closed : ∀ r (ts : Values (fun s => {a // carrier s a}) (σ.funcDomain r)),
    carrier (σ.funcCodomain r) (ℳ.funcInterp r (ts.map (fun _ a => a.val)))

namespace Substructure_m

/-- 子类型与限制解释组成实际结构，不从存在性证书选取数据。 -/
@[implicit_reducible] def structure_m (A : Substructure_m ℳ) : Structure.{u, v, w, x} σ where
  Carrier s := {a // A.carrier s a}
  nonempty s := by
    obtain ⟨a, ha⟩ := A.nonempty s
    exact ⟨⟨a, ha⟩⟩
  funcInterp r ts := ⟨ℳ.funcInterp r (ts.map (fun _ a => a.val)), A.closed r ts⟩
  relInterp r ts := ℳ.relInterp r (ts.map (fun _ a => a.val))

def incl_m (A : Substructure_m ℳ) : Str_emb A.structure_m ℳ where
  map _ a := a.val
  function_eq _ _ := rfl
  map_injective _ _ _ h := Subtype.ext h
  relation_iff _ _ := Iff.rfl

/-- 环境的全部自由及绑定参数都在子结构中。 -/
def Params_m (A : Substructure_m ℳ) {b f} (ρ : Env ℳ b f) : Prop :=
  (∀ {s} (i : Variable b s), A.carrier s (ρ.boundVal i)) ∧
  (∀ {s} (i : Variable f s), A.carrier s (ρ.freeVal i))

def restrict_m (A : Substructure_m ℳ) {b f} (ρ : Env ℳ b f) (h : A.Params_m ρ) :
    Env A.structure_m b f where
  boundVal i := ⟨ρ.boundVal i, h.1 i⟩
  freeVal i := ⟨ρ.freeVal i, h.2 i⟩

theorem map_restrict_m (A : Substructure_m ℳ) {b f} (ρ : Env ℳ b f)
    (h : A.Params_m ρ) : (A.restrict_m ρ h).map A.incl_m.map = ρ := rfl

theorem params_map_m (A : Substructure_m ℳ) {b f} (ρ : Env A.structure_m b f) :
    A.Params_m (ρ.map A.incl_m.map) :=
  ⟨fun i => (ρ.boundVal i).property, fun i => (ρ.freeVal i).property⟩

/-- 函数封闭自动延伸到任意项，供 hull 的项闭包消费者复用。 -/
theorem term_mem_m (A : Substructure_m ℳ) {b f s} (ρ : Env ℳ b f)
    (h : A.Params_m ρ) (t : Term σ b f s) : A.carrier s (t.eval ρ) := by
  have k := A.incl_m.toFn_map.term_eval_eq (A.restrict_m ρ h) t
  rw [A.map_restrict_m] at k
  exact k ▸ (t.eval (A.restrict_m ρ h)).property

def Elementary_m (A : Substructure_m ℳ) : Prop := A.incl_m.Elementary_m

/-- 带子结构参数的存在公式若在原模型成立，则在该子集中有原模型见证。 -/
def WitnessClosed_m (A : Substructure_m ℳ) : Prop :=
  ∀ {b f s} (φ : Formula σ (s :: b) f) (ρ : Env ℳ b f), A.Params_m ρ →
    (∃ a, Formula.satisfies (ρ.pushBound a) φ) →
      ∃ a, A.carrier s a ∧ Formula.satisfies (ρ.pushBound a) φ

/-- 初等子模型的 Tarski–Vaught 等价定义，右侧不预设任何子模型真值保持。 -/
theorem tarski_vaught_m (A : Substructure_m ℳ) : A.Elementary_m ↔ A.WitnessClosed_m := by
  constructor
  · intro h b f s φ ρ hρ hφ
    have k : ∃ a, Formula.satisfies
        (((A.restrict_m ρ hρ).map A.incl_m.map).pushBound a) φ := by
      simpa only [A.map_restrict_m] using hφ
    obtain ⟨a, ha⟩ := A.incl_m.witness_of_elementary_m h φ (A.restrict_m ρ hρ) k
    exact ⟨a.val, a.property, by simpa only [A.map_restrict_m] using! ha⟩
  · intro h
    apply A.incl_m.elementary_of_witness_m
    intro b f s φ ρ hφ
    obtain ⟨a, ha, hφ⟩ := h φ (ρ.map A.incl_m.map) (A.params_map_m ρ) hφ
    exact ⟨⟨a, ha⟩, hφ⟩

theorem models_iff_m (A : Substructure_m ℳ) (h : A.Elementary_m) (T : Theory σ) :
    Theory.Models A.structure_m T ↔ Theory.Models ℳ T :=
  A.incl_m.elementary_models_iff_m h T

/-- 嵌套子结构的实际包含映射；只消耗逐点包含证明。 -/
def inclusion_m (A B : Substructure_m ℳ) (h : ∀ s a, A.carrier s a → B.carrier s a) :
    Str_emb A.structure_m B.structure_m where
  map s a := ⟨a.val, h s a.val a.property⟩
  function_eq r ts := by
    apply Subtype.ext
    change ℳ.funcInterp r _ = ℳ.funcInterp r _
    rw [Values.map_comp]
    rfl
  map_injective s _ _ k := Subtype.ext (congrArg (fun a : B.structure_m.Carrier s => a.val) k)
  relation_iff r ts := by
    change ℳ.relInterp r _ ↔ ℳ.relInterp r _
    rw [Values.map_comp]
    rfl

/-- 同一模型的两个嵌套初等子模型之间的包含仍是初等嵌入。 -/
theorem elementary_inclusion_m (A B : Substructure_m ℳ)
    (h : ∀ s a, A.carrier s a → B.carrier s a)
    (hA : A.Elementary_m) (hB : B.Elementary_m) : (A.inclusion_m B h).Elementary_m :=
  fun φ ρ => (hA φ ρ).trans (hB φ (ρ.map (A.inclusion_m B h).map)).symm

end Substructure_m
end YesMetaZFC.Logic.FirstOrder
