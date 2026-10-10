import YesMetaZFC.Model.Forcing.External.Formula
import YesMetaZFC.Logic.FirstOrder.NatPairing

/-! # 由公式自动生成量词稠密要求

原 AST 的结构递归给出可数稠密开族。二元联结词取交；量词把当前见证要求与
正文要求取交，用已有自然数配对遍历名称枚举和正文要求。无需新的公式编码。
-/

namespace YesMetaZFC.Model.Forcing
open Boolean Logic Logic.FirstOrder SetTheory
universe u v
variable {B : Type v} (𝔹 : CB_alg B) (N : Name_domain_l.{u, v} B)
  (e : Nat → {G : BV_graph.{u, v} B // N.mem G})

def fm_dense_l : {b f : SortContext ℒ} → Formula ℒ b f →
    (domain_str_l 𝔹 N).Env 𝔹.toBA_alg b f → Nat → Pos_l 𝔹.toBA_alg → Prop
  | _, _, .falsum, _, _, _ | _, _, .truth, _, _, _ |
    _, _, .equal _ _, _, _, _ | _, _, .rel _ _, _, _, _ => True
  | _, _, .neg φ, ρ, n, p => fm_dense_l φ ρ n p
  | _, _, .conj φ ψ, ρ, n, p | _, _, .disj φ ψ, ρ, n, p |
    _, _, .imp φ ψ, ρ, n, p | _, _, .iff φ ψ, ρ, n, p =>
      fm_dense_l φ ρ n p ∧ fm_dense_l ψ ρ n p
  | _, _, .forallE _ φ, ρ, n, p =>
      sup_dense_l 𝔹 (fun a => 𝔹.neg (BV_str.value 𝔹 (domain_str_l 𝔹 N) φ (ρ.pushBound a))) p ∧
      fm_dense_l φ (ρ.pushBound (e (NatPairing.first n))) (NatPairing.second n) p
  | _, _, .existsE _ φ, ρ, n, p =>
      sup_dense_l 𝔹 (fun a => BV_str.value 𝔹 (domain_str_l 𝔹 N) φ (ρ.pushBound a)) p ∧
      fm_dense_l φ (ρ.pushBound (e (NatPairing.first n))) (NatPairing.second n) p

theorem fm_dense_lower_l {b f} (φ : Formula ℒ b f)
    (ρ : (domain_str_l 𝔹 N).Env 𝔹.toBA_alg b f) (n : Nat) :
    (positive_order_l 𝔹.toBA_alg).toPO_pre.Lower_l (fm_dense_l 𝔹 N e φ ρ n) := by
  induction φ generalizing n with
  | falsum | truth | equal | rel => exact fun _ _ => trivial
  | neg φ ih => exact ih ρ n
  | conj φ ψ ih jh | disj φ ψ ih jh | imp φ ψ ih jh | iff φ ψ ih jh =>
    exact fun h k => ⟨ih ρ n h k.1, jh ρ n h k.2⟩
  | forallE s φ ih | existsE s φ ih =>
    exact fun h k => ⟨sup_dense_lower_l 𝔹 _ h k.1, ih _ _ h k.2⟩

theorem fm_dense_dense_l {b f} (φ : Formula ℒ b f)
    (ρ : (domain_str_l 𝔹 N).Env 𝔹.toBA_alg b f) (n : Nat) :
    (positive_order_l 𝔹.toBA_alg).toPO_pre.Dense_l (fm_dense_l 𝔹 N e φ ρ n) := by
  let R := (positive_order_l 𝔹.toBA_alg).toPO_pre
  induction φ generalizing n with
  | falsum | truth | equal | rel => exact fun p => ⟨p, R.le_refl p, trivial⟩
  | neg φ ih => exact ih ρ n
  | conj φ ψ ih jh | disj φ ψ ih jh | imp φ ψ ih jh | iff φ ψ ih jh =>
    exact R.dense_inter_l (ih ρ n) (jh ρ n) (fm_dense_lower_l 𝔹 N e φ ρ n)
  | forallE s φ ih | existsE s φ ih =>
    exact R.dense_inter_l (sup_dense_dense_l 𝔹 _) (ih _ _) (sup_dense_lower_l 𝔹 _)

/-- 逐项遇到计算得到的族，自动满足完整公式真值所需的全部量词要求。 -/
theorem fm_generic_of_meets_l (he : Function.Surjective e) (U : Filter_l 𝔹.toBA_alg)
    {b f} (φ : Formula ℒ b f) (ρ : (domain_str_l 𝔹 N).Env 𝔹.toBA_alg b f)
    (h : ∀ n, BF_meets_l U (fm_dense_l 𝔹 N e φ ρ n)) : Fm_generic_l 𝔹 N U φ ρ := by
  induction φ with
  | falsum | truth | equal | rel => trivial
  | neg φ ih => exact ih ρ h
  | conj φ ψ ih jh | disj φ ψ ih jh | imp φ ψ ih jh | iff φ ψ ih jh =>
    constructor
    · apply ih ρ
      intro n
      obtain ⟨p, hp, hφ, _⟩ := h n
      exact ⟨p, hp, hφ⟩
    · apply jh ρ
      intro n
      obtain ⟨p, hp, _, hψ⟩ := h n
      exact ⟨p, hp, hψ⟩
  | forallE s φ ih | existsE s φ ih =>
    constructor
    · obtain ⟨p, hp, hφ, _⟩ := h 0
      exact ⟨p, hp, hφ⟩
    · intro a
      obtain ⟨i, rfl⟩ := he a
      apply ih
      intro n
      obtain ⟨p, hp, _, hφ⟩ := h (NatPairing.pair i n)
      exact ⟨p, hp, by simpa only [NatPairing.first_pair, NatPairing.second_pair] using hφ⟩

/-- 公式与赋值都保留原类型化上下文，可用于参数实例或闭公理的统一调度。 -/
structure Fm_query_l where
  bound : SortContext ℒ
  free : SortContext ℒ
  formula : Formula ℒ bound free
  env : (domain_str_l 𝔹 N).Env 𝔹.toBA_alg bound free

/-- 可数种子及其节点枚举直接给出整个生成名称域的枚举。 -/
def span_enum_l (F : Nat → BV_graph.{u, v} B) (e : ∀ i, Nat → (F i).Domain) :
    Nat → {G // (name_span_l 𝔹.toBA_alg (fun H => ∃ i, F i = H)).mem G}
  | 0 => ⟨BV_graph.empty 𝔹.toPO_bot, Or.inl rfl⟩
  | n+1 => ⟨(F (NatPairing.first n)).at_node (e (NatPairing.first n) (NatPairing.second n)),
      Or.inr ⟨F (NatPairing.first n), ⟨NatPairing.first n, rfl⟩,
        e (NatPairing.first n) (NatPairing.second n), rfl⟩⟩

theorem span_enum_surjective_l (F : Nat → BV_graph.{u, v} B)
    (e : ∀ i, Nat → (F i).Domain) (he : ∀ i a, ∃ n, e i n = a) :
    Function.Surjective (span_enum_l 𝔹 F e) := by
  rintro ⟨G, hG⟩
  rcases hG with rfl | ⟨_, ⟨i, rfl⟩, a, rfl⟩
  · exact ⟨0, rfl⟩
  · obtain ⟨j, rfl⟩ := he i a
    refine ⟨NatPairing.pair i j + 1, Subtype.ext ?_⟩
    exact congrArg (fun k : Nat × Nat => (F k.1).at_node (e k.1 k.2))
      (show (NatPairing.first (NatPairing.pair i j), NatPairing.second (NatPairing.pair i j)) = (i, j)
        from Prod.ext (NatPairing.first_pair i j) (NatPairing.second_pair i j))

end YesMetaZFC.Model.Forcing
