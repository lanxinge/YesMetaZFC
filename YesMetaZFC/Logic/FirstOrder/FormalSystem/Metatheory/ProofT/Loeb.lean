import YesMetaZFC.Logic.FirstOrder.Derivation.Propositional

/-! # 普通 Hilbert 推导中的 Löb 定理

只消费 D1–D3 和一个实际固定点的推导等价。
签名及可证明性算子保持任意；具体 quotation 和对角化由实例层提供。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT
set_option autoImplicit false
universe u v w

/-- 同一理论和同一普通可证明性算子的三项可导性条件。 -/
structure DerivabilityConditions_m {σ : Signature.{u, v, w}} (T : Theory σ)
    (F : Sentence σ → Sentence σ) : Prop where
  necessitation_m : ∀ {φ}, Derives T [] φ → Derives T [] (F φ)
  distribution_m : ∀ φ ψ, Derives T [] (.imp (F (.imp φ ψ)) (.imp (F φ) (F ψ)))
  introspection_m : ∀ φ, Derives T [] (.imp (F φ) (F (F φ)))

namespace DerivabilityConditions_m
variable {σ : Signature.{u, v, w}} {T : Theory σ} {F : Sentence σ → Sentence σ}

theorem imp_m (D : DerivabilityConditions_m T F) {φ ψ : Sentence σ}
    (h : Derives T [] (.imp φ ψ)) : Derives T [] (.imp (F φ) (F ψ)) :=
  Derives.imp_elim (D.distribution_m φ ψ) (D.necessitation_m h)

theorem iff_m (D : DerivabilityConditions_m T F) {φ ψ : Sentence σ}
    (h : Derives T [] (.iff φ ψ)) : Derives T [] (.iff (F φ) (F ψ)) :=
  Derives.imp_elim
    (Derives.imp_elim (Derives.logical_axiom (.biconditional_intro (F φ) (F ψ)))
      (D.imp_m (Derives.imp_elim (Derives.logical_axiom (.biconditional_elim_left φ ψ)) h)))
    (D.imp_m (Derives.imp_elim (Derives.logical_axiom (.biconditional_elim_right φ ψ)) h))

/-- 固定点 ψ ↔ (□ψ → φ) 给出内部 Löb 公式。 -/
theorem loeb_axiom_m (D : DerivabilityConditions_m T F)
    (φ ψ : Sentence σ) (hψ : Derives T [] (.iff ψ (.imp (F ψ) φ))) :
    Derives T [] (.imp (F (.imp (F φ) φ)) (F φ)) := by
  have h₁ : Derives T [] (.imp ψ (.imp (F ψ) φ)) :=
    Derives.imp_elim (Derives.logical_axiom (.biconditional_elim_left _ _)) hψ
  -- 将固定点正方向提升，并用 D3 消去重复的证明前件。
  have h₂ := Derives.imp_trans (D.imp_m h₁) (D.distribution_m (F ψ) φ)
  have h₃ : Derives T [] (.imp (F ψ) (F φ)) :=
    Derives.imp_elim
      (Derives.imp_elim (Derives.Propositional.imp_distribution (F ψ) (F (F ψ)) (F φ)) h₂)
      (D.introspection_m ψ)
  -- 反射前提先推出固定点本身，再提升为固定点的可证明性。
  have hφ : Derives T [] (.imp (.imp (F φ) φ) ψ) := by
    apply Derives.imp_intro
    apply Derives.iff_elim_right hψ.context_weaken_cons
    apply Derives.imp_intro
    exact Derives.imp_elim
      (Derives.assumption (List.mem_cons_of_mem _ List.mem_cons_self))
      (Derives.imp_elim h₃.context_weaken_cons.context_weaken_cons
        (Derives.assumption List.mem_cons_self))
  exact Derives.imp_trans (D.imp_m hφ) h₃

/-- Löb 规则：理论若证明 □φ → φ，便已经证明 φ。 -/
theorem loeb_m (D : DerivabilityConditions_m T F)
    (φ ψ : Sentence σ) (hψ : Derives T [] (.iff ψ (.imp (F ψ) φ)))
    (hφ : Derives T [] (.imp (F φ) φ)) : Derives T [] φ :=
  Derives.imp_elim hφ
    (Derives.imp_elim (D.loeb_axiom_m φ ψ hψ) (D.necessitation_m hφ))

end DerivabilityConditions_m
end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT
