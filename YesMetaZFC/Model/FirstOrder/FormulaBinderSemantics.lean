import YesMetaZFC.Model.FirstOrder.SubstitutionSemantics

/-! # 公式穿过绑定变量后的通用语义

通过环境回拉复用重命名可靠性，不重新遍历联结词和量词。
-/
namespace YesMetaZFC.Logic.FirstOrder.Formula
set_option autoImplicit false
universe u v w x

theorem satisfies_weakenBound_m {σ : Signature.{u,v,w}} {ℳ : Structure.{u,v,w,x} σ}
    {bound free : SortContext σ} {introduced : σ.SortSymbol}
    (env : Env ℳ bound free) (value : ℳ.Carrier introduced) (φ : Formula σ bound free) :
    (φ.weakenBound introduced).satisfies (env.pushBound value) ↔ φ.satisfies env := by
  have h := satisfies_rename (env.pushBound value) (Renaming.weakenBound introduced) φ
  have he : (env.pushBound value).pullbackRenaming (Renaming.weakenBound introduced) = env := by
    apply Env.ext
    · intro s entry; rfl
    · intro s entry; rfl
  rwa [he] at h

/-- 大公式的语义外壳在抽象参数上核验，避免内核展开具体正文。 -/
theorem satisfies_exists_m {σ : Signature.{u,v,w}} {ℳ : Structure.{u,v,w,x} σ}
    {bound free : SortContext σ} {s : σ.SortSymbol} (env : Env ℳ bound free)
    (p : Formula σ (s :: bound) free) :
    (Formula.existsE s p).satisfies env ↔ ∃ a, p.satisfies (env.pushBound a) := Iff.rfl

theorem satisfies_conj_m {σ : Signature.{u,v,w}} {ℳ : Structure.{u,v,w,x} σ}
    {bound free : SortContext σ} (env : Env ℳ bound free) (p q : Formula σ bound free) :
    (Formula.conj p q).satisfies env ↔ p.satisfies env ∧ q.satisfies env := Iff.rfl

theorem satisfies_neg_m {σ : Signature.{u,v,w}} {ℳ : Structure.{u,v,w,x} σ}
    {bound free : SortContext σ} (env : Env ℳ bound free) (p : Formula σ bound free) :
    (Formula.neg p).satisfies env ↔ ¬ p.satisfies env := Iff.rfl

theorem satisfies_iff_m {σ : Signature.{u,v,w}} {ℳ : Structure.{u,v,w,x} σ}
    {bound free : SortContext σ} (env : Env ℳ bound free) (p q : Formula σ bound free) :
    (Formula.iff p q).satisfies env ↔ (p.satisfies env ↔ q.satisfies env) := Iff.rfl

end YesMetaZFC.Logic.FirstOrder.Formula
