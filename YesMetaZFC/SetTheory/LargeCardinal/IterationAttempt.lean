import YesMetaZFC.SetTheory.LargeCardinal.IterationDiagram
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingAttemptDecode
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingAttemptCertificate
import YesMetaZFC.Model.SetTheory.Internal.SourceClosureSyntax
import YesMetaZFC.SetTheory.Notation

/-! # 整条有限树枝的联合初等尝试

节点为 (k,P)：P 为 k 的全部树前驱各存一行，行长恰为 k。
各行检验全部内部公式，并在原树嵌入下交换；根行遵守指定嵌入。
末结点递增时只延长原来的行，所以内部无限链同时给出共尾枝和相容实现。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

structure Ja_enum_d (ω α Q E : M.Domain) : Prop where
  function : M.IsSetFunction I E
  domain : M.IsDomainOf I α E
  rows : ∀ i e c X R, Rd_entry_d i e E → Rd_entry_d i c Q → KPair_d M c X R →
    Fn0_d ω X e ∧ ∀ x, M.mem x X → ∃ n, M.mem n ω ∧ Rd_entry_d n x e

def Ja_rows_d (ω Q E Y W k P : M.Domain) : Prop := ∀ i p c X R e,
  Rd_entry_d i p P → Rd_entry_d i c Q → KPair_d M c X R → Rd_entry_d i e E →
    Fn0_d k Y p ∧ At_coherent_d k X Y e p ∧ At_elementary_d I ω X R Y W e k p

def Ja_commute_d (G E P : M.Domain) : Prop := ∀ i j p q e f g u v x y a b,
  Rd_entry_d i p P → Rd_entry_d j q P → Rd_entry_d i e E → Rd_entry_d j f E →
    It_map_d G i j g → Rd_entry_d u x e → Rd_entry_d v y f → Rd_entry_d x y g →
      Rd_entry_d u a p → Rd_entry_d v b q → a = b

structure Ja_node_d (ω T Q G E Y W z π k P : M.Domain) : Prop where
  length : M.mem k ω
  function : M.IsSetFunction I P
  domain : ∀ i, (∃ p, Rd_entry_d i p P) ↔ Rd_entry_d i k T
  rows : Ja_rows_d I ω Q E Y W k P
  root : ∀ p c X R e, Rd_entry_d z p P → Rd_entry_d z c Q → KPair_d M c X R → Rd_entry_d z e E →
    At_prescribed_d k X Y e π p
  commute : Ja_commute_d G E P

def Ja_extend_d (T s t : M.Domain) : Prop := ∃ k P l Q,
  KPair_d M s k P ∧ KPair_d M t l Q ∧ M.mem k l ∧ Rd_entry_d k l T ∧
    ∀ i p q, Rd_entry_d i p P → Rd_entry_d i q Q → M.MemberSubset p q

/-- 实际有限序列空间和双边真值证书检验全部内部公式。 -/
def ja_elementary_m {d} (ω X R Y W e k p : Term d) : Formula 1 d := set[d] ⟪
  ∃ Q J K, ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, ⌜ω⌝ₛ, Q) ∧
    ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, ⌜X⌝ₛ, J) ∧
    ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, ⌜Y⌝ₛ, K) ∧
    ⌜at_elementary_m⌝ₚ(⌜ω⌝ₛ, ⌜X⌝ₛ, ⌜R⌝ₛ, ⌜Y⌝ₛ, ⌜W⌝ₛ, ⌜e⌝ₛ, ⌜k⌝ₛ, ⌜p⌝ₛ, Q, J, K)⟫
derive_free_closed ja_elementary_m

theorem ja_elementary_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (ω X R Y W e k p : Term d)
    (hω : M.IsOmega (ω.eval ρ)) (hk : M.mem (k.eval ρ) (ω.eval ρ)) :
    Formula.satisfies ρ (ja_elementary_m ω X R Y W e k p) ↔
      At_elementary_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval ρ) (X.eval ρ) (R.eval ρ)
        (Y.eval ρ) (W.eval ρ) (e.eval ρ) (k.eval ρ) (p.eval ρ) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  simp only [ja_elementary_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fseq_space_sat_l I hZF.1, Definitional.Term.eval_weaken]
  let w (t : Term d) := t.weaken.weaken.weaken
  have read Q J K (hQ : Fseq_space_d I (ω.eval ρ) (ω.eval ρ) Q)
      (hJ : Fseq_space_d I (ω.eval ρ) (X.eval ρ) J) (hK : Fseq_space_d I (ω.eval ρ) (Y.eval ρ) K) :=
    at_elementary_sat_l hZF (((ρ.push Q).push J).push K)
      (w ω) (w X) (w R) (w Y) (w W) (w e) (w k) (w p) (.bound 2) (.bound 1) .newest
      (by simpa only [w, Definitional.Term.eval_weaken] using hω)
      (by simpa only [w, Definitional.Term.eval_weaken] using hk)
      (by simpa only [w, Definitional.Term.eval_weaken, Term.eval_bound_two_push,
        Term.eval_bound_one_push, Term.eval_bound_zero_push] using hQ)
      (by simpa only [w, Definitional.Term.eval_weaken, Term.eval_bound_one_push, Term.eval_bound_zero_push] using hJ)
      (by simpa only [w, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using hK)
  simp only [w, Definitional.Term.eval_weaken] at read
  constructor
  · rintro ⟨Q, J, K, hQ, hJ, hK, h⟩
    exact (read Q J K hQ hJ hK).mp h
  · intro h
    obtain ⟨Q, hQ⟩ := ZF.fseq_space_exists_l I hZF hω (ω.eval ρ)
    obtain ⟨J, hJ⟩ := ZF.fseq_space_exists_l I hZF hω (X.eval ρ)
    obtain ⟨K, hK⟩ := ZF.fseq_space_exists_l I hZF hω (Y.eval ρ)
    exact ⟨Q, J, K, hQ, hJ, hK, (read Q J K hQ hJ hK).mpr h⟩

def ja_rows_m {d} (ω Q E Y W k P : Term d) : Formula 1 d := set[d] ⟪
  ∀ i p c X R e, ⌜rd_entry0_m⌝ₚ(i, p, ⌜P⌝ₛ) → ⌜rd_entry0_m⌝ₚ(i, c, ⌜Q⌝ₛ) →
    ⌜kpair0_m⌝ₚ(c, X, R) → ⌜rd_entry0_m⌝ₚ(i, e, ⌜E⌝ₛ) →
    ⌜fn0_m⌝ₚ(⌜k⌝ₛ, ⌜Y⌝ₛ, p) ∧ ⌜at_coherent_m⌝ₚ(⌜k⌝ₛ, X, ⌜Y⌝ₛ, e, p) ∧
      ⌜ja_elementary_m⌝ₚ(⌜ω⌝ₛ, X, R, ⌜Y⌝ₛ, ⌜W⌝ₛ, e, ⌜k⌝ₛ, p)⟫
derive_free_closed ja_rows_m

theorem ja_rows_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (ω Q E Y W k P : Term d)
    (hω : M.IsOmega (ω.eval ρ)) (hk : M.mem (k.eval ρ) (ω.eval ρ)) :
    Formula.satisfies ρ (ja_rows_m ω Q E Y W k P) ↔
      Ja_rows_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval ρ) (Q.eval ρ) (E.eval ρ)
        (Y.eval ρ) (W.eval ρ) (k.eval ρ) (P.eval ρ) := by
  simp only [ja_rows_m, Ja_rows_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    rd_entry0_sat_l hZF.1, kpair0_sat_l hZF.1, Formula.satisfies_conj_iff, fn0_sat_l hZF.1,
    at_coherent_sat_l hZF.1, Definitional.Term.eval_weaken]
  simp only [ja_elementary_sat_l hZF, Definitional.Term.eval_weaken, hω, hk]
  rfl

def ja_commute_m {d} (G E P : Term d) : Formula 1 d := set[d] ⟪
  ∀ i j p q e f g u v x y a b,
    ⌜rd_entry0_m⌝ₚ(i, p, ⌜P⌝ₛ) → ⌜rd_entry0_m⌝ₚ(j, q, ⌜P⌝ₛ) →
    ⌜rd_entry0_m⌝ₚ(i, e, ⌜E⌝ₛ) → ⌜rd_entry0_m⌝ₚ(j, f, ⌜E⌝ₛ) → ⌜it_map_m⌝ₚ(⌜G⌝ₛ, i, j, g) →
    ⌜rd_entry0_m⌝ₚ(u, x, e) → ⌜rd_entry0_m⌝ₚ(v, y, f) → ⌜rd_entry0_m⌝ₚ(x, y, g) →
    ⌜rd_entry0_m⌝ₚ(u, a, p) → ⌜rd_entry0_m⌝ₚ(v, b, q) → a = b⟫
derive_free_closed ja_commute_m

theorem ja_commute_sat_l (hE : Extensional M) {d} (ρ : Env M d) (G E P : Term d) :
    Formula.satisfies ρ (ja_commute_m G E P) ↔ Ja_commute_d (G.eval ρ) (E.eval ρ) (P.eval ρ) := by
  simp only [ja_commute_m, Ja_commute_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    rd_entry0_sat_l hE, it_map_sat_l hE, Formula.satisfies_extensionalEq_iff_eq hE,
    Definitional.Term.eval_weaken]; rfl

def ja_node_m {d} (ω T Q G E Y W z π k P : Term d) : Formula 1 d := set[d] ⟪
  ⌜k⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜Formula.isFunction kpair_convention_l⌝ₚ(⌜P⌝ₛ) ∧
    (∀ i, (∃ p, ⌜rd_entry0_m⌝ₚ(i, p, ⌜P⌝ₛ)) ↔ ⌜rd_entry0_m⌝ₚ(i, ⌜k⌝ₛ, ⌜T⌝ₛ)) ∧
    ⌜ja_rows_m⌝ₚ(⌜ω⌝ₛ, ⌜Q⌝ₛ, ⌜E⌝ₛ, ⌜Y⌝ₛ, ⌜W⌝ₛ, ⌜k⌝ₛ, ⌜P⌝ₛ) ∧
    (∀ p c X R e, ⌜rd_entry0_m⌝ₚ(⌜z⌝ₛ, p, ⌜P⌝ₛ) → ⌜rd_entry0_m⌝ₚ(⌜z⌝ₛ, c, ⌜Q⌝ₛ) →
      ⌜kpair0_m⌝ₚ(c, X, R) → ⌜rd_entry0_m⌝ₚ(⌜z⌝ₛ, e, ⌜E⌝ₛ) →
        ⌜at_prescribed_m⌝ₚ(⌜k⌝ₛ, X, ⌜Y⌝ₛ, e, ⌜π⌝ₛ, p)) ∧ ⌜ja_commute_m⌝ₚ(⌜G⌝ₛ, ⌜E⌝ₛ, ⌜P⌝ₛ)⟫
derive_free_closed ja_node_m

theorem ja_node_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (ω T Q G E Y W z π k P : Term d)
    (hω : M.IsOmega (ω.eval ρ)) :
    Formula.satisfies ρ (ja_node_m ω T Q G E Y W z π k P) ↔
      Ja_node_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval ρ) (T.eval ρ) (Q.eval ρ) (G.eval ρ) (E.eval ρ) (Y.eval ρ) (W.eval ρ)
        (z.eval ρ) (π.eval ρ) (k.eval ρ) (P.eval ρ) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  simp only [ja_node_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isFunction_iff I hZF.1, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_exists_iff, rd_entry0_sat_l hZF.1, Formula.satisfies_imp_iff,
    kpair0_sat_l hZF.1, at_prescribed_sat_l hZF.1, ja_commute_sat_l hZF.1, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, (ja_rows_sat_l hZF _ _ _ _ _ _ _ _ hω a).mp d, e, f⟩,
    fun h => ⟨h.length, h.function, h.domain,
      (ja_rows_sat_l hZF _ _ _ _ _ _ _ _ hω h.length).mpr h.rows, h.root, h.commute⟩⟩

def ja_extend_m {d} (T s t : Term d) : Formula 1 d := set[d] ⟪
  ∃ k P l Q, ⌜kpair0_m⌝ₚ(⌜s⌝ₛ, k, P) ∧ ⌜kpair0_m⌝ₚ(⌜t⌝ₛ, l, Q) ∧ k ∈ l ∧
    ⌜rd_entry0_m⌝ₚ(k, l, ⌜T⌝ₛ) ∧ (∀ i p q, ⌜rd_entry0_m⌝ₚ(i, p, P) → ⌜rd_entry0_m⌝ₚ(i, q, Q) → p ⊆ q)⟫
derive_free_closed ja_extend_m

theorem ja_extend_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T s t : Term d) :
    Formula.satisfies ρ (ja_extend_m T s t) ↔ Ja_extend_d (T.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [ja_extend_m, Ja_extend_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair0_sat_l hE, Formula.satisfies_mem_iff, rd_entry0_sat_l hE, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.LargeCardinal
