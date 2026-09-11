import YesMetaZFC.Logic.FirstOrder.LevyHierarchy
import YesMetaZFC.Model.FirstOrder.Morphism
import YesMetaZFC.Logic.FirstOrder.FormulaComplexity

/-!
# 内在类型 Lévy 层级的绝对性

结构嵌入按排序直接映射载体。`Delta0` 双向绝对、`Sigma1` 向上绝对和 `Pi1` 向下
绝对的证明只处理真正的语义内容；排序、arity、bound 作用域和界项独立性已经由
类型保证。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Formula

universe u v w x y

namespace LevyBound

/-- 一个模型中有界关系的语义。 -/
def Holds {σ : Signature.{u, v, w}} (ℬ : LevyBound σ)
    (M : Structure.{u, v, w, x} σ)
    (element set : M.Carrier ℬ.sort) : Prop :=
  M.relInterp ℬ.relation
    (ℬ.domains.symm ▸ Values.cons element (Values.cons set .nil))

private theorem eval_pair_cast
    {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} (env : Env M bound free)
    {sort : σ.SortSymbol} {domains : List σ.SortSymbol}
    (hDomains : domains = [sort, sort])
    (element set : Term σ bound free sort) :
    Arguments.eval env
        (hDomains.symm ▸ Arguments.cons element (Arguments.cons set .nil)) =
      hDomains.symm ▸ Values.cons (element.eval env)
        (Values.cons (set.eval env) .nil) := by
  cases hDomains
  rfl

private theorem map_pair_cast
    {σ : Signature.{u, v, w}}
    {source : Structure.{u, v, w, x} σ}
    {target : Structure.{u, v, w, y} σ}
    (f : ∀ sort, source.Carrier sort → target.Carrier sort)
    {sort : σ.SortSymbol} {domains : List σ.SortSymbol}
    (hDomains : domains = [sort, sort])
    (element set : source.Carrier sort) :
    Values.map f
        (hDomains.symm ▸ Values.cons element (Values.cons set .nil)) =
      hDomains.symm ▸ Values.cons (f sort element)
        (Values.cons (f sort set) .nil) := by
  cases hDomains
  rfl

@[simp] theorem satisfies_membership
    {σ : Signature.{u, v, w}} (ℬ : LevyBound σ)
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} (env : Env M bound free)
    (element set : Term σ bound free ℬ.sort) :
    Formula.satisfies env (ℬ.membership element set) ↔
      ℬ.Holds M (element.eval env) (set.eval env) := by
  simp only [membership, Formula.satisfies, Holds]
  rw [eval_pair_cast env ℬ.domains element set]

@[simp] theorem satisfies_boundedForall
    {σ : Signature.{u, v, w}} (ℬ : LevyBound σ)
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} (env : Env M bound free)
    (set : Term σ bound free ℬ.sort)
    (body : Formula σ (ℬ.sort :: bound) free) :
    Formula.satisfies env (ℬ.boundedForall set body) ↔
      ∀ value : M.Carrier ℬ.sort,
        ℬ.Holds M value (set.eval env) →
          Formula.satisfies (env.pushBound value) body := by
  simp [boundedForall, Formula.satisfies,
    Term.eval_weakenBound, Term.eval]

@[simp] theorem satisfies_boundedExists
    {σ : Signature.{u, v, w}} (ℬ : LevyBound σ)
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} (env : Env M bound free)
    (set : Term σ bound free ℬ.sort)
    (body : Formula σ (ℬ.sort :: bound) free) :
    Formula.satisfies env (ℬ.boundedExists set body) ↔
      ∃ value : M.Carrier ℬ.sort,
        ℬ.Holds M value (set.eval env) ∧
          Formula.satisfies (env.pushBound value) body := by
  simp [boundedExists, Formula.satisfies,
    Term.eval_weakenBound, Term.eval]

end LevyBound

/-- 保持相对 Lévy 语义的多排序结构嵌入。 -/
structure LevyEmbedding {σ : Signature.{u, v, w}}
    (ℬ : LevyBound σ)
    (source : Structure.{u, v, w, x} σ)
    (target : Structure.{u, v, w, y} σ) extends Str_emb source target where
  bounded_preimage :
    ∀ (set : source.Carrier ℬ.sort) (element : target.Carrier ℬ.sort),
      ℬ.Holds target element (map ℬ.sort set) →
        ∃ sourceElement : source.Carrier ℬ.sort,
          map ℬ.sort sourceElement = element

namespace LevyEmbedding

/-- 恒等嵌入的有界见证就是该对象本身。 -/
def refl {σ : Signature.{u, v, w}} (ℬ : LevyBound σ)
    (ℳ : Structure.{u, v, w, x} σ) : LevyEmbedding ℬ ℳ ℳ where
  toStr_emb := Str_emb.refl ℳ
  bounded_preimage _ a _ := ⟨a, rfl⟩

/-- 有界关系本身由关系保持合同双向保存。 -/
theorem holds_iff
    {σ : Signature.{u, v, w}} {ℬ : LevyBound σ}
    {source : Structure.{u, v, w, x} σ}
    {target : Structure.{u, v, w, y} σ}
    (embedding : LevyEmbedding ℬ source target)
    (element set : source.Carrier ℬ.sort) :
    ℬ.Holds source element set ↔
      ℬ.Holds target (embedding.map ℬ.sort element)
        (embedding.map ℬ.sort set) := by
  simpa only [LevyBound.Holds,
    LevyBound.map_pair_cast embedding.map ℬ.domains element set] using
    embedding.relation_iff ℬ.relation
      (ℬ.domains.symm ▸ Values.cons element (Values.cons set .nil))

end LevyEmbedding

namespace MembershipGuard

/-- 正位置成员 guard 从量词体真值中恢复显式集合界。 -/
theorem holds_of_satisfies
    {σ : Signature.{u, v, w}} {ℬ : LevyBound σ}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ}
    {set : Term σ bound free ℬ.sort}
    {body : Formula σ (ℬ.sort :: bound) free}
    (hGuard : MembershipGuard ℬ set body)
    (env : Env M (ℬ.sort :: bound) free)
    (hBody : Formula.satisfies env body) :
    ℬ.Holds M (Term.eval env (.bvar .here))
      (Term.eval env (set.weakenBound ℬ.sort)) := by
  induction hGuard generalizing env with
  | membership =>
      exact (LevyBound.satisfies_membership ℬ env _ _).mp hBody
  | conj_left hLeft ih =>
      exact ih env hBody.1
  | conj_right hRight ih =>
      exact ih env hBody.2

end MembershipGuard

/-- 相对 `Delta0` 公式在 Lévy 嵌入两侧绝对。 -/
theorem delta0_absolute
    {σ : Signature.{u, v, w}} {ℬ : LevyBound σ}
    {source : Structure.{u, v, w, x} σ}
    {target : Structure.{u, v, w, y} σ}
    (embedding : LevyEmbedding ℬ source target)
    {bound free : SortContext σ} {formula : Formula σ bound free}
    (hFormula : IsDelta0 ℬ formula) :
    ∀ env : Env source bound free,
      Formula.satisfies env formula ↔
        Formula.satisfies (env.map embedding.map) formula := by
  induction hFormula with
  | falsum => intro env; rfl
  | truth => intro env; rfl
  | rel relation arguments =>
      intro env
      simp only [Formula.satisfies]
      rw [← embedding.toFn_map.arguments_eval_eq env arguments]
      exact embedding.relation_iff relation (arguments.eval env)
  | equal left right =>
      intro env
      simp only [Formula.satisfies]
      constructor
      · intro hEqual
        rw [← embedding.toFn_map.term_eval_eq env left,
          ← embedding.toFn_map.term_eval_eq env right]
        exact congrArg (embedding.map _) hEqual
      · intro hEqual
        apply embedding.map_injective _
        simpa [embedding.toFn_map.term_eval_eq env left,
          embedding.toFn_map.term_eval_eq env right] using hEqual
  | neg hBody ih =>
      intro env
      exact not_congr (ih env)
  | conj hLeft hRight ihLeft ihRight =>
      intro env
      exact and_congr (ihLeft env) (ihRight env)
  | disj hLeft hRight ihLeft ihRight =>
      intro env
      exact or_congr (ihLeft env) (ihRight env)
  | imp hLeft hRight ihLeft ihRight =>
      intro env
      exact imp_congr (ihLeft env) (ihRight env)
  | iff hLeft hRight ihLeft ihRight =>
      intro env
      exact iff_congr (ihLeft env) (ihRight env)
  | bounded_forall set hBody ih =>
      intro env
      rw [LevyBound.satisfies_boundedForall,
        LevyBound.satisfies_boundedForall]
      constructor
      · intro hSource targetValue hTargetBound
        have hSet :
            Term.eval (env.map embedding.map) set =
              embedding.map ℬ.sort (Term.eval env set) :=
          (embedding.toFn_map.term_eval_eq env set).symm
        rw [hSet] at hTargetBound
        rcases embedding.bounded_preimage
            (Term.eval env set) targetValue hTargetBound with
          ⟨sourceValue, hValue⟩
        subst targetValue
        rw [← Env.map_pushBound]
        exact (ih (env.pushBound sourceValue)).mp
          (hSource sourceValue
            ((embedding.holds_iff sourceValue (Term.eval env set)).mpr
              hTargetBound))
      · intro hTarget sourceValue hSourceBound
        have hMappedBound :=
          (embedding.holds_iff sourceValue (Term.eval env set)).mp
            hSourceBound
        have hTargetBody := hTarget (embedding.map ℬ.sort sourceValue) (by
          simpa only [embedding.toFn_map.term_eval_eq env set] using hMappedBound)
        rw [← Env.map_pushBound] at hTargetBody
        exact (ih (env.pushBound sourceValue)).mpr hTargetBody
  | bounded_exists set hBody ih =>
      intro env
      rw [LevyBound.satisfies_boundedExists,
        LevyBound.satisfies_boundedExists]
      constructor
      · rintro ⟨sourceValue, hSourceBound, hSourceBody⟩
        have hMappedBound :=
          (embedding.holds_iff sourceValue (Term.eval env set)).mp
            hSourceBound
        refine ⟨embedding.map ℬ.sort sourceValue, ?_, ?_⟩
        · simpa only [embedding.toFn_map.term_eval_eq env set] using hMappedBound
        rw [← Env.map_pushBound]
        exact (ih (env.pushBound sourceValue)).mp hSourceBody
      · rintro ⟨targetValue, hTargetBound, hTargetBody⟩
        have hSet :
            Term.eval (env.map embedding.map) set =
              embedding.map ℬ.sort (Term.eval env set) :=
          (embedding.toFn_map.term_eval_eq env set).symm
        rw [hSet] at hTargetBound
        rcases embedding.bounded_preimage
            (Term.eval env set) targetValue hTargetBound with
          ⟨sourceValue, hValue⟩
        subst targetValue
        refine ⟨sourceValue,
          (embedding.holds_iff sourceValue (Term.eval env set)).mpr
            hTargetBound, ?_⟩
        rw [← Env.map_pushBound] at hTargetBody
        exact (ih (env.pushBound sourceValue)).mpr hTargetBody
  | guarded_exists set hBody hGuard ih =>
      intro env
      simp only [Formula.satisfies]
      constructor
      · rintro ⟨sourceValue, hSourceBody⟩
        refine ⟨embedding.map ℬ.sort sourceValue, ?_⟩
        rw [← Env.map_pushBound]
        exact (ih (env.pushBound sourceValue)).mp hSourceBody
      · rintro ⟨targetValue, hTargetBody⟩
        have hTargetBound := hGuard.holds_of_satisfies
          ((env.map embedding.map).pushBound targetValue) hTargetBody
        rw [Term.eval_weakenBound] at hTargetBound
        have hSet :
            Term.eval (env.map embedding.map) set =
              embedding.map ℬ.sort (Term.eval env set) :=
          (embedding.toFn_map.term_eval_eq env set).symm
        rw [hSet] at hTargetBound
        rcases embedding.bounded_preimage
            (Term.eval env set) targetValue hTargetBound with
          ⟨sourceValue, hValue⟩
        subst targetValue
        refine ⟨sourceValue, ?_⟩
        rw [← Env.map_pushBound] at hTargetBody
        exact (ih (env.pushBound sourceValue)).mpr hTargetBody

/-- 一级 Lévy 公式的绝对性方向由极性统一决定。 -/
theorem level1_absolute
    {σ : Signature.{u, v, w}} {ℬ : LevyBound σ}
    {source : Structure.{u, v, w, x} σ}
    {target : Structure.{u, v, w, y} σ}
    (embedding : LevyEmbedding ℬ source target)
    {polarity : LevyPolarity}
    {bound free : SortContext σ} {formula : Formula σ bound free}
    (hFormula : IsLevel1 ℬ polarity formula) :
    match polarity with
    | .sigma => ∀ env : Env source bound free,
        Formula.satisfies env formula →
          Formula.satisfies (env.map embedding.map) formula
    | .pi => ∀ env : Env source bound free,
        Formula.satisfies (env.map embedding.map) formula →
          Formula.satisfies env formula := by
  induction hFormula with
  | @delta0 polarity bound free formula hDelta =>
      cases polarity
      · intro env
        exact (delta0_absolute embedding hDelta env).mp
      · intro env
        exact (delta0_absolute embedding hDelta env).mpr
  | @neg polarity bound free body hBody ih =>
      cases polarity
      · intro env hTarget hSource
        exact hTarget (ih env hSource)
      · intro env hSource hTarget
        exact hSource (ih env hTarget)
  | @conj polarity bound free left right hLeft hRight ihLeft ihRight =>
      cases polarity
      · intro env hSource
        exact ⟨ihLeft env hSource.1, ihRight env hSource.2⟩
      · intro env hTarget
        exact ⟨ihLeft env hTarget.1, ihRight env hTarget.2⟩
  | @disj polarity bound free left right hLeft hRight ihLeft ihRight =>
      cases polarity
      · intro env hSource
        rcases hSource with hSourceLeft | hSourceRight
        · exact Or.inl (ihLeft env hSourceLeft)
        · exact Or.inr (ihRight env hSourceRight)
      · intro env hTarget
        rcases hTarget with hTargetLeft | hTargetRight
        · exact Or.inl (ihLeft env hTargetLeft)
        · exact Or.inr (ihRight env hTargetRight)
  | @imp polarity bound free left right hLeft hRight ihLeft ihRight =>
      cases polarity
      · intro env hSource hTargetLeft
        exact ihRight env (hSource (ihLeft env hTargetLeft))
      · intro env hTarget hSourceLeft
        exact ihRight env (hTarget (ihLeft env hSourceLeft))
  | @existsE bound free sort body hBody ih =>
      intro env hSource
      rcases hSource with ⟨sourceValue, hSourceBody⟩
      refine ⟨embedding.map sort sourceValue, ?_⟩
      rw [← Env.map_pushBound]
      exact ih (env.pushBound sourceValue) hSourceBody
  | @forallE bound free sort body hBody ih =>
      intro env hTarget sourceValue
      have hTargetBody := hTarget (embedding.map sort sourceValue)
      rw [← Env.map_pushBound] at hTargetBody
      exact ih (env.pushBound sourceValue) hTargetBody
  | @bounded_forall polarity bound free set body hBody ih =>
      cases polarity
      · intro env
        rw [LevyBound.satisfies_boundedForall,
          LevyBound.satisfies_boundedForall]
        intro hSource targetValue hTargetBound
        have hSet : Term.eval (env.map embedding.map) set =
            embedding.map ℬ.sort (Term.eval env set) :=
          (embedding.toFn_map.term_eval_eq env set).symm
        rw [hSet] at hTargetBound
        rcases embedding.bounded_preimage
            (Term.eval env set) targetValue hTargetBound with
          ⟨sourceValue, hValue⟩
        subst targetValue
        rw [← Env.map_pushBound]
        exact ih (env.pushBound sourceValue)
          (hSource sourceValue
            ((embedding.holds_iff sourceValue (Term.eval env set)).mpr
              hTargetBound))
      · intro env
        rw [LevyBound.satisfies_boundedForall,
          LevyBound.satisfies_boundedForall]
        intro hTarget sourceValue hSourceBound
        have hMappedBound :=
          (embedding.holds_iff sourceValue (Term.eval env set)).mp
            hSourceBound
        have hTargetBody := hTarget (embedding.map ℬ.sort sourceValue) (by
          simpa only [embedding.toFn_map.term_eval_eq env set] using hMappedBound)
        rw [← Env.map_pushBound] at hTargetBody
        exact ih (env.pushBound sourceValue) hTargetBody
  | @bounded_exists polarity bound free set body hBody ih =>
      cases polarity
      · intro env
        rw [LevyBound.satisfies_boundedExists,
          LevyBound.satisfies_boundedExists]
        rintro ⟨sourceValue, hSourceBound, hSourceBody⟩
        have hMappedBound :=
          (embedding.holds_iff sourceValue (Term.eval env set)).mp
            hSourceBound
        refine ⟨embedding.map ℬ.sort sourceValue, ?_, ?_⟩
        · simpa only [embedding.toFn_map.term_eval_eq env set] using hMappedBound
        rw [← Env.map_pushBound]
        exact ih (env.pushBound sourceValue) hSourceBody
      · intro env
        rw [LevyBound.satisfies_boundedExists,
          LevyBound.satisfies_boundedExists]
        rintro ⟨targetValue, hTargetBound, hTargetBody⟩
        have hSet : Term.eval (env.map embedding.map) set =
            embedding.map ℬ.sort (Term.eval env set) :=
          (embedding.toFn_map.term_eval_eq env set).symm
        rw [hSet] at hTargetBound
        rcases embedding.bounded_preimage
            (Term.eval env set) targetValue hTargetBound with
          ⟨sourceValue, hValue⟩
        subst targetValue
        refine ⟨sourceValue,
          (embedding.holds_iff sourceValue (Term.eval env set)).mpr
            hTargetBound, ?_⟩
        rw [← Env.map_pushBound] at hTargetBody
        exact ih (env.pushBound sourceValue) hTargetBody

/-- 相对 `Sigma1` 公式沿 Lévy 嵌入向上绝对。 -/
theorem sigma1_upward_absolute
    {σ : Signature.{u, v, w}} {ℬ : LevyBound σ}
    {source : Structure.{u, v, w, x} σ}
    {target : Structure.{u, v, w, y} σ}
    (embedding : LevyEmbedding ℬ source target)
    {bound free : SortContext σ} {formula : Formula σ bound free}
    (hFormula : IsSigma1 ℬ formula) (env : Env source bound free) :
    Formula.satisfies env formula →
      Formula.satisfies (env.map embedding.map) formula :=
  level1_absolute embedding hFormula env

/-- 相对 `Pi1` 公式沿 Lévy 嵌入向下绝对。 -/
theorem pi1_downward_absolute
    {σ : Signature.{u, v, w}} {ℬ : LevyBound σ}
    {source : Structure.{u, v, w, x} σ}
    {target : Structure.{u, v, w, y} σ}
    (embedding : LevyEmbedding ℬ source target)
    {bound free : SortContext σ} {formula : Formula σ bound free}
    (hFormula : IsPi1 ℬ formula) (env : Env source bound free) :
    Formula.satisfies (env.map embedding.map) formula →
      Formula.satisfies env formula :=
  level1_absolute embedding hFormula env

end Formula
end FirstOrder
end Logic
end YesMetaZFC
