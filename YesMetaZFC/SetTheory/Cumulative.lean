import YesMetaZFC.SetTheory.Ord.Arithmetic.Recursion

/-! # 原模型内的累积层级

统一递归方程为 V_α = ⋃_{β∈α} P(V_β)。算子先从先前值域的并之幂集分离，
所以在所有内部序数序列上实际全定义且唯一，不预设外部良基性或全局选择。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def V_step_d (F V : M.Domain) : Prop :=
  ∀ x, M.mem x V ↔ ∃ β W, M.PairMember I β W F ∧ M.MemberSubset x W

def v_step_m (𝒞 : OrderedPairConvention) {n} (F V : Term n) : Formula 1 n :=
  .forallE (.iff (.mem .newest V.weaken) (.existsE (.existsE
    (.conj (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken.weaken)
      (Formula.subset (.bound 2) .newest)))))
derive_free_closed v_step_m

def v_op_l (𝒞 : OrderedPairConvention) : BinarySchema 0 := { body := v_step_m 𝒞 (.bound 1) .newest }

def V_d (α V : M.Domain) : Prop := M.IsRecursionValue I (V_step_d I) α V

def v_m (𝒞 : OrderedPairConvention) {n} (α V : Term n) : Formula 1 n :=
  Formula.isRecursionValue 𝒞 (v_op_l 𝒞) Definitional.TermVector.empty α V
derive_free_closed v_m

theorem v_step_sat_l {n} (ρ : Env M n) (F V : Term n) :
    Formula.satisfies ρ (v_step_m 𝒞 F V) ↔ V_step_d I (F.eval ρ) (V.eval ρ) := by
  simp only [v_step_m, V_step_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_subset_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem v_op_denote_l (ρ : Env M 0) : (v_op_l 𝒞).denote ρ = V_step_d I := by
  funext F V
  exact propext (v_step_sat_l I ((ρ.push F).push V) _ _)

theorem v_sat_l (hE : Extensional M) {n} (ρ : Env M n) (α V : Term n) :
    Formula.satisfies ρ (v_m 𝒞 α V) ↔ V_d I (α.eval ρ) (V.eval ρ) := by
  rw [v_m, Formula.satisfies_isRecursionValue_iff I hE, v_op_denote_l I]
  rfl

theorem v_step_unique_l (hE : Extensional M) {F V W} (hV : V_step_d I F V) (hW : V_step_d I F W) : V = W :=
  hE.eq_of_same_members V W (fun x => (hV x).trans (hW x).symm)

theorem v_ordinal_l {α V} (h : V_d I α V) : M.IsOrdinal α := h.elim fun _ hF => hF.1.1.1

theorem v_empty_l {e V} (he : ∀ x, ¬ M.mem x e) (hV : V_d I e V) : ∀ x, ¬ M.mem x V := by
  obtain ⟨F, hF, hv⟩ := hV
  intro x hx
  obtain ⟨β, W, hβ, _⟩ := (hv x).mp hx
  exact he β ((hF.1.2.2 β).mpr ⟨W, hβ⟩)

namespace ZF

/-- 对任意实际集合函数图，先前值域幂集之并都是模型内集合。 -/
theorem v_step_exists_l (hZF : M.Models ZF) {F δ} (hF : M.IsSetFunction I F) (hδ : M.IsDomainOf I δ F) :
    ∃ V, V_step_d I F V := by
  obtain ⟨A, hA⟩ := exists_range_of_setFunction hZF I hF hδ
  obtain ⟨U, hU⟩ := KP.exists_union (modelsKP hZF) A
  obtain ⟨P, hP⟩ := exists_powerSet hZF U
  let ρ : Env M 1 := ⟨fun _ => F, fun _ => F⟩
  let φ : UnarySchema 1 := {
    body := .existsE (.existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 3))
      (Formula.subset (.bound 2) .newest))) }
  have hφ x : φ.denote ρ x ↔ ∃ β W, M.PairMember I β W F ∧ M.MemberSubset x W := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_subset_iff]
    rfl
  obtain ⟨V, hV⟩ := separation_exists_d hZF φ ρ P
  refine ⟨V, fun x => (hV x).trans ?_⟩
  change (M.mem x P ∧ φ.denote ρ x) ↔ _
  rw [hφ x]
  refine ⟨And.right, fun ⟨β, W, hβ, hx⟩ => ⟨?_, β, W, hβ, hx⟩⟩
  exact (hP x).mpr (fun y hy => (hU y).mpr ⟨W, (hA W).mpr ⟨β, hβ⟩, hx y hy⟩)

theorem v_step_class_l (hZF : M.Models ZF) : M.IsClassFunctionOnTransfiniteSequences I (V_step_d I) := by
  rintro F ⟨δ, hF⟩
  obtain ⟨V, hV⟩ := v_step_exists_l I hZF hF.2.1 hF.2.2
  exact ⟨V, hV, fun W hW => v_step_unique_l I hZF.1 hW hV⟩

/-- 任意内部序数处的层级实际存在，递归算子已由前一定理完整实现。 -/
theorem v_exists_l (hZF : M.Models ZF) {α} (hα : M.IsOrdinal α) : ∃ V, V_d I α V := by
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => α⟩
  have hOp := v_op_denote_l I ρ
  have hClass : M.IsClassFunctionOnTransfiniteSequences I ((v_op_l 𝒞).denote ρ) := by
    rw [hOp]
    exact v_step_class_l I hZF
  obtain ⟨V, hV⟩ := recursionValue_exists hZF I ρ (v_op_l 𝒞) hClass hα
  exact ⟨V, by simpa only [V_d, hOp] using hV⟩

theorem v_unique_l (hZF : M.Models ZF) {α V W} (hV : V_d I α V) (hW : V_d I α W) : V = W := by
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => α⟩
  have hOp := v_op_denote_l I ρ
  have hClass : M.IsClassFunctionOnTransfiniteSequences I ((v_op_l 𝒞).denote ρ) := by
    rw [hOp]
    exact v_step_class_l I hZF
  exact recursionValue_unique hZF I ρ (v_op_l 𝒞) hClass
    (by simpa only [V_d, hOp] using hV) (by simpa only [V_d, hOp] using hW)

/-- 层级成员由较早层的子集刻画；所有较早层都由实际递归值关系给出。 -/
theorem v_unfold_l (hZF : M.Models ZF) {α V} (hV : V_d I α V) (x) :
    M.mem x V ↔ ∃ β W, M.mem β α ∧ V_d I β W ∧ M.MemberSubset x W := by
  obtain ⟨F, hF, hv⟩ := hV
  refine (hv x).trans ⟨?_, ?_⟩
  · rintro ⟨β, W, hβ, hx⟩
    have hβα := (hF.1.2.2 β).mpr ⟨W, hβ⟩
    exact ⟨β, W, hβα, hF.recursionValue_of_pairMember hβα hβ, hx⟩
  · rintro ⟨β, W, hβα, hW, hx⟩
    obtain ⟨U, hU⟩ := (hF.1.2.2 β).mp hβα
    have he := v_unique_l I hZF (hF.recursionValue_of_pairMember hβα hU) hW
    subst U
    exact ⟨β, W, hU, hx⟩

theorem v_mono_l (hZF : M.Models ZF) {α β V W} (hV : V_d I α V) (hW : V_d I β W)
    (hαβ : M.MemberSubset α β) : M.MemberSubset V W := by
  intro x hx
  obtain ⟨γ, U, hγ, hU, hxU⟩ := (v_unfold_l I hZF hV x).mp hx
  exact (v_unfold_l I hZF hW x).mpr ⟨γ, U, hαβ γ hγ, hU, hxU⟩

theorem v_mem_l (hZF : M.Models ZF) {α β V W} (hV : V_d I α V) (hW : V_d I β W)
    (hαβ : M.mem α β) : M.mem V W :=
  (v_unfold_l I hZF hW V).mpr ⟨α, V, hαβ, hV, fun _ hx => hx⟩

theorem v_transitive_l (hZF : M.Models ZF) {α V} (hV : V_d I α V) : M.TransitiveSet V := by
  intro x hx y hy
  obtain ⟨β, W, hβ, hW, hxW⟩ := (v_unfold_l I hZF hV x).mp hx
  exact v_mono_l I hZF hW hV ((v_ordinal_l I hV).transitive.memberSubset hβ) y (hxW y hy)

/-- 后继层恰是前一层的内部幂集。 -/
theorem v_successor_l (hZF : M.Models ZF) {α β V W} (hV : V_d I α V) (hW : V_d I β W)
    (hβ : M.SuccessorOf β α) : M.IsPowerSetOf W V := by
  intro x
  constructor
  · intro hx
    obtain ⟨γ, U, hγ, hU, hxU⟩ := (v_unfold_l I hZF hW x).mp hx
    have hγα : M.MemberSubset γ α := by
      rcases (hβ γ).mp hγ with hγ | hγ
      · exact (v_ordinal_l I hV).transitive.memberSubset hγ
      · exact fun y hy => (hγ y).mp hy
    exact fun y hy => v_mono_l I hZF hU hV hγα y (hxU y hy)
  · intro hx
    exact (v_unfold_l I hZF hW x).mpr ⟨α, V, hβ.predecessor_mem, hV, hx⟩

/-- 没有最后索引时，当前层正是所有较早层的并；也包含零长度情形。 -/
theorem v_limit_mem_l (hZF : M.Models ZF) {α V} (hV : V_d I α V)
    (hlim : ∀ β, M.mem β α → ∃ γ, M.mem γ α ∧ M.mem β γ) (x) :
    M.mem x V ↔ ∃ β W, M.mem β α ∧ V_d I β W ∧ M.mem x W := by
  constructor
  · intro hx
    obtain ⟨β, W, hβ, hW, hxW⟩ := (v_unfold_l I hZF hV x).mp hx
    obtain ⟨γ, hγ, hβγ⟩ := hlim β hβ
    obtain ⟨U, hU⟩ := v_exists_l I hZF ((v_ordinal_l I hV).mem hγ)
    exact ⟨γ, U, hγ, hU, (v_unfold_l I hZF hU x).mpr ⟨β, W, hβγ, hW, hxW⟩⟩
  · rintro ⟨β, W, hβ, hW, hx⟩
    exact v_mono_l I hZF hW hV ((v_ordinal_l I hV).transitive.memberSubset hβ) x hx

end ZF
end YesMetaZFC.SetTheory
