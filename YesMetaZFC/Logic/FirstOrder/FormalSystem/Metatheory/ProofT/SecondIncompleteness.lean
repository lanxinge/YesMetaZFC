import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Loeb
import YesMetaZFC.Logic.FirstOrder.Derivation.Consistency

/-! # Löb 定理导出的第二不完备定理

一致性句子使用 ¬□⊥；只消费原可导性条件及矛盾反射的固定点。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.DerivabilityConditions_m
set_option autoImplicit false
universe u v w
variable {σ : Signature.{u, v, w}} {T : Theory σ} {F : Sentence σ → Sentence σ}

/-- 内部第二不完备公式：Con(T) → ¬□Con(T)。 -/
theorem second_incompleteness_internal_m (D : DerivabilityConditions_m T F)
    (ψ : Sentence σ) (hψ : Derives T [] (.iff ψ (.imp (F ψ) .falsum))) :
    Derives T [] (.imp (.neg (F .falsum)) (.neg (F (.neg (F .falsum))))) := by
  -- 否定消去经 D1、D2 提升，再接上矛盾句的内部 Löb 公式。
  have h : Derives T [] (.imp (F (.neg (F .falsum))) (F .falsum)) :=
    Derives.imp_trans
      (D.imp_m (Derives.logical_axiom (.explosion (F .falsum) .falsum)))
      (D.loeb_axiom_m .falsum ψ hψ)
  apply Derives.imp_intro
  apply Derives.neg_intro
  exact Derives.neg_elim
    (Derives.imp_elim h.context_weaken_cons.context_weaken_cons
      (Derives.assumption List.mem_cons_self))
    (Derives.assumption (List.mem_cons_of_mem _ List.mem_cons_self))

/-- 一致理论不能证明自己的普通一致性句子。 -/
theorem second_incompleteness_m (D : DerivabilityConditions_m T F)
    (ψ : Sentence σ) (hψ : Derives T [] (.iff ψ (.imp (F ψ) .falsum)))
    (hT : Derives.Consistent T ([] : Context σ [])) :
    ¬ Derives T [] (.neg (F .falsum)) := by
  intro h
  exact hT (D.loeb_m .falsum ψ hψ
    (Derives.imp_elim (Derives.logical_axiom (.explosion (F .falsum) .falsum)) h))

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.DerivabilityConditions_m
